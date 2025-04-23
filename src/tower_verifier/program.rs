use super::binding::{
    IOPProverMessage, IOPProverMessageVariable, Point, PointAndEvalVariable, PointVariable,
    TowerVerifierInput, TowerVerifierInputVariable,
};
use crate::arithmetics::{
    dot_product, dot_product_pt_n_eval, eq_eval, evaluate_at_point, gen_alpha_pows, join, product,
    reverse, is_smaller_than,
};
use crate::tower_verifier;
use crate::transcript::transcript_observe_label;
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use ark_poly::domain::EvaluationDomain;
use ark_std::collections::BTreeSet;
use ceno_zkvm::structs::PointAndEval;
use mpcs::BasefoldCommitment;
use openvm::io::println;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler::{asm::AsmConfig, ir::MemVariable};
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::{
    challenger::ChallengerVariable,
    hints::{Hintable, InnerChallenge, InnerVal, VecAutoHintable},
};
use openvm_stark_sdk::{p3_baby_bear::BabyBear, p3_blake3::Blake3};
use p3_field::PrimeField32;
use p3_field::{
    ExtensionField, Field as Plonky3Field, FieldAlgebra, FieldExtensionAlgebra, PackedValue,
    TwoAdicField,
};
use whir::{
    crypto::{
        fields::Field64,
        merkle_tree::blake3::{self as merkle_tree, Blake3Digest},
    },
    poly_utils::{eq_poly_outside, MultilinearPoint},
    sumcheck::proof::SumcheckPolynomial,
    whir::{
        fs_utils::DigestReader,
        parameters::WhirConfig,
        vm_binding::{
            BlakeDigestVariable, StatementVariable, WhirProofRoundVariable, WhirProofVariable,
        },
        WhirProof,
    },
};
type InnerConfig = AsmConfig<InnerVal, InnerChallenge>;
const NUM_FANIN: usize = 2;
const MAX_DEGREE: usize = 3;

// Interpolate a uni-variate degree-`p_i.len()-1` polynomial and evaluate this
// polynomial at `eval_at`:
//
//   \sum_{i=0}^len p_i * (\prod_{j!=i} (eval_at - j)/(i-j) )
//
pub(crate) fn interpolate_uni_poly<C: Config>(
    builder: &mut Builder<C>,
    p_i: &Array<C, Ext<C::F, C::EF>>,
    eval_at: Ext<C::F, C::EF>,
) -> Ext<C::F, C::EF> {
    let len = p_i.len();
    let evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(len.clone());
    let prod: Ext<C::F, C::EF> = builder.eval(eval_at);

    builder.set(&evals, 0, eval_at);

    // `prod = \prod_{j} (eval_at - j)`
    let e: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    builder.range(1, len.clone()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let tmp: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
        builder.assign(&tmp, eval_at - e);
        builder.set(&evals, i, tmp);
        builder.assign(&prod, prod * tmp);
        builder.assign(&e, e + one);
    });

    let denom_up: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let i: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    builder.assign(&i, i + one);
    builder.range(2, len.clone()).for_each(|_i_vec, builder| {
        builder.assign(&denom_up, denom_up * i);
        builder.assign(&i, i + one);
    });
    let denom_down: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);

    let idx_vec_len: RVar<C::N> = builder.eval_expr(len.clone() - RVar::from(1));
    let idx_vec: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(idx_vec_len);
    let idx_val: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    builder.range(0, idx_vec.len()).for_each(|i_vec, builder| {
        builder.set(&idx_vec, i_vec[0], idx_val);
        builder.assign(&idx_val, idx_val + one);
    });
    let idx_rev = reverse(builder, &idx_vec);
    let res = builder.constant(C::EF::ZERO);

    let len_f = idx_val.clone();
    let neg_one: Ext<C::F, C::EF> = builder.constant(C::EF::NEG_ONE);
    let evals_rev = reverse(builder, &evals);
    let p_i_rev = reverse(builder, &p_i);

    let mut idx_pos: RVar<C::N> = builder.eval_expr(len.clone() - RVar::from(1));
    iter_zip!(builder, idx_rev, evals_rev, p_i_rev).for_each(|ptr_vec, builder| {
        let idx = builder.iter_ptr_get(&idx_rev, ptr_vec[0]);
        let eval = builder.iter_ptr_get(&evals_rev, ptr_vec[1]);
        let up_eval_inv: Ext<C::F, C::EF> = builder.eval(denom_up * eval);
        builder.assign(&up_eval_inv, up_eval_inv.inverse());
        let p = builder.iter_ptr_get(&p_i_rev, ptr_vec[2]);

        builder.assign(&res, res + p * prod * denom_down * up_eval_inv);
        builder.assign(&denom_up, denom_up * (len_f - idx) * neg_one);
        builder.assign(&denom_down, denom_down * idx);

        idx_pos = builder.eval_expr(idx_pos - RVar::from(1));
    });

    let p_i_0 = builder.get(&p_i, 0);
    let eval_0 = builder.get(&evals, 0);
    let up_eval_inv: Ext<C::F, C::EF> = builder.eval(denom_up * eval_0);
    builder.assign(&up_eval_inv, up_eval_inv.inverse());
    builder.assign(&res, res + p_i_0 * prod * denom_down * up_eval_inv);

    res
}

pub fn iop_verifier_state_verify<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    out_claim: &Ext<C::F, C::EF>,
    prover_messages: &Array<C, IOPProverMessageVariable<C>>,
    max_num_variables: Felt<C::F>,
    max_degree: Felt<C::F>,
) -> (
    Array<C, Ext<<C as Config>::F, <C as Config>::EF>>,
    Ext<<C as Config>::F, <C as Config>::EF>,
) {
    let max_num_variables_usize: Usize<C::N> = Usize::from(builder.cast_felt_to_var(max_num_variables.clone()));
    challenger.observe(builder, max_num_variables);
    challenger.observe(builder, max_degree);

    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let round: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let polynomials_received: Array<C, Array<C, Ext<C::F, C::EF>>> =
        builder.dyn_array(max_num_variables_usize.clone());
    let challenges: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(max_num_variables_usize.clone());

    builder
        .range(0, max_num_variables_usize.clone())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let prover_msg = builder.get(&prover_messages, i);

            iter_zip!(builder, prover_msg.evaluations).for_each(|ptr_vec, builder| {
                let e = builder.iter_ptr_get(&prover_msg.evaluations, ptr_vec[0]);
                let e_felts = builder.ext2felt(e);
                challenger.observe_slice(builder, e_felts);
            });

            transcript_observe_label(builder, challenger, b"Internal round");
            let challenge = challenger.sample_ext(builder);

            builder.set(&challenges, i, challenge);
            builder.set(&polynomials_received, i, prover_msg.evaluations);
            builder.assign(&round, round + one);
        });

    // set `expected` to P(r)`
    let expected_len: RVar<_> = builder.eval_expr(polynomials_received.len() + RVar::from(1));
    let expected_vec: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(expected_len.clone());
    builder.set(&expected_vec, 0, out_claim.clone());

    let truncated_expected_vec = expected_vec.slice(builder, 1, expected_len);
    iter_zip!(
        builder,
        polynomials_received,
        challenges,
        truncated_expected_vec
    )
    .for_each(|idx_vec, builder| {
        let poly_ptr = idx_vec[0];
        let c_ptr = idx_vec[1];

        let evaluations = builder.iter_ptr_get(&polynomials_received, poly_ptr);
        let c = builder.iter_ptr_get(&challenges, c_ptr);

        let expected_ptr = idx_vec[2];
        let expected = interpolate_uni_poly(builder, &evaluations, c);

        builder.iter_ptr_set(&truncated_expected_vec, expected_ptr, expected);
    });

    // l-append asserted_sum to the first position of the expected vector
    iter_zip!(builder, polynomials_received, expected_vec).for_each(|idx_vec, builder| {
        let evaluations = builder.iter_ptr_get(&polynomials_received, idx_vec[0]);
        let expected = builder.iter_ptr_get(&expected_vec, idx_vec[1]);

        let e1 = builder.get(&evaluations, 0);
        let e2 = builder.get(&evaluations, 1);
        let target: Ext<<C as Config>::F, <C as Config>::EF> = builder.eval(e1 + e2);

        builder.assert_ext_eq(expected, target);
    });

    let expected = builder.get(&expected_vec, max_num_variables_usize);

    (challenges, expected)
}

pub fn verify_tower_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    tower_verifier_input: TowerVerifierInputVariable<C>,
) -> (
    PointVariable<C>,
    Array<C, PointAndEvalVariable<C>>,
    Array<C, PointAndEvalVariable<C>>,
    Array<C, PointAndEvalVariable<C>>,
) {
    let num_fanin: usize = 2;
    builder.assert_usize_eq(tower_verifier_input.num_fanin, RVar::from(num_fanin));
    let num_prod_spec = tower_verifier_input.prod_out_evals.len();
    let num_logup_spec = tower_verifier_input.logup_out_evals.len();

    builder.assert_usize_eq(
        tower_verifier_input.prod_specs_eval.len(),
        num_prod_spec.clone(),
    );
    builder.assert_usize_eq(
        tower_verifier_input.logup_specs_eval.len(),
        num_logup_spec.clone(),
    );
    builder.assert_usize_eq(
        tower_verifier_input.num_variables.len(),
        num_prod_spec.clone() + num_logup_spec.clone(),
    );

    iter_zip!(builder, tower_verifier_input.prod_out_evals).for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let evals = builder.iter_ptr_get(&tower_verifier_input.prod_out_evals, ptr);
        builder.assert_usize_eq(evals.len(), RVar::from(num_fanin));
    });
    iter_zip!(builder, tower_verifier_input.logup_out_evals).for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let evals = builder.iter_ptr_get(&tower_verifier_input.logup_out_evals, ptr);
        builder.assert_usize_eq(evals.len(), RVar::from(4));
    });

    let alpha_len: Usize<C::N> =
        builder.eval(num_prod_spec.clone() + num_logup_spec.clone() + num_logup_spec.clone());

    transcript_observe_label(builder, challenger, b"combine subset evals");
    let alpha_pows = gen_alpha_pows(builder, challenger, alpha_len.clone());

    // initial_claim = \sum_j alpha^j * out_j[rt]
    // out_j[rt] := (record_{j}[rt])
    // out_j[rt] := (logup_p{j}[rt])
    // out_j[rt] := (logup_q{j}[rt])
    let log2_num_fanin = 1usize;
    let initial_rt: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(RVar::from(log2_num_fanin));
    transcript_observe_label(builder, challenger, b"product_sum");
    builder
        .range(0, initial_rt.len())
        .for_each(|idx_vec, builder| {
            let idx = idx_vec[0];
            let c = challenger.sample_ext(builder);
            builder.set(&initial_rt, idx, c);
        });

    let prod_spec_point_n_eval: Array<C, PointAndEvalVariable<C>> =
        builder.dyn_array(num_prod_spec.clone());
    iter_zip!(
        builder,
        tower_verifier_input.prod_out_evals,
        prod_spec_point_n_eval
    )
    .for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let evals = builder.iter_ptr_get(&tower_verifier_input.prod_out_evals, ptr);
        let e = evaluate_at_point(builder, &evals, &initial_rt);
        let p_ptr = ptr_vec[1];
        builder.iter_ptr_set(
            &prod_spec_point_n_eval,
            p_ptr,
            PointAndEvalVariable {
                point: PointVariable {
                    fs: initial_rt.clone(),
                },
                eval: e,
            },
        );
    });

    let logup_spec_p_point_n_eval: Array<C, PointAndEvalVariable<C>> =
        builder.dyn_array(num_logup_spec.clone());
    let logup_spec_q_point_n_eval: Array<C, PointAndEvalVariable<C>> =
        builder.dyn_array(num_logup_spec.clone());

    iter_zip!(
        builder,
        tower_verifier_input.logup_out_evals,
        logup_spec_p_point_n_eval,
        logup_spec_q_point_n_eval
    )
    .for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let evals = builder.iter_ptr_get(&tower_verifier_input.prod_out_evals, ptr);

        let p_slice = evals.slice(builder, 0, 2);
        let q_slice = evals.slice(builder, 2, 4);

        let e1 = evaluate_at_point(builder, &p_slice, &initial_rt);
        let e2 = evaluate_at_point(builder, &q_slice, &initial_rt);

        let p_ptr = ptr_vec[1];
        let q_ptr = ptr_vec[2];

        builder.iter_ptr_set(
            &logup_spec_p_point_n_eval,
            p_ptr,
            PointAndEvalVariable {
                point: PointVariable {
                    fs: initial_rt.clone(),
                },
                eval: e1,
            },
        );
        builder.iter_ptr_set(
            &logup_spec_q_point_n_eval,
            q_ptr,
            PointAndEvalVariable {
                point: PointVariable {
                    fs: initial_rt.clone(),
                },
                eval: e2,
            },
        );
    });

    let interleaved_len = builder.eval_expr(num_logup_spec.clone() * RVar::from(2));
    let interleaved_point_n_eval: Array<C, PointAndEvalVariable<C>> =
        builder.dyn_array(interleaved_len);
    builder
        .range(0, num_logup_spec.clone())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let p_i = builder.eval_expr(i * RVar::from(2));
            let q_i = builder.eval_expr(i * RVar::from(2) + RVar::from(1));

            let p = builder.get(&logup_spec_p_point_n_eval, i);
            builder.set(&interleaved_point_n_eval, p_i, p);
            let q = builder.get(&logup_spec_q_point_n_eval, i);
            builder.set(&interleaved_point_n_eval, q_i, q);
        });

    let alpha_prod_slice = alpha_pows.slice(builder, 0, num_prod_spec.clone());
    let prod_sub_sum = dot_product_pt_n_eval(builder, &prod_spec_point_n_eval, &alpha_prod_slice);
    let alpha_logup_slice = alpha_pows.slice(builder, num_prod_spec.clone(), alpha_len.clone());
    let logup_sub_sum =
        dot_product_pt_n_eval(builder, &interleaved_point_n_eval, &alpha_logup_slice);
    let initial_claim: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    builder.assign(&initial_claim, prod_sub_sum + logup_sub_sum);

    let curr_pt = initial_rt.clone();
    let curr_eval = initial_claim.clone();
    let op_range: RVar<C::N> = builder.eval_expr(tower_verifier_input.max_num_variables - Usize::from(1));
    let round: Felt<C::F> = builder.constant(C::F::ZERO);
    let one: Ext<<C as Config>::F, <C as Config>::EF> = builder.constant(C::EF::ONE);

    let mut next_rt = PointAndEvalVariable {
        point: PointVariable {
            fs: builder.dyn_array(1),
        },
        eval: builder.constant(C::EF::ZERO),
    };

    builder.range(0, op_range.clone()).for_each(|i_vec, builder| {
        let round_var = i_vec[0];

        let out_rt = &curr_pt;
        let out_claim = &curr_eval;

        let prover_messages = builder.get(&tower_verifier_input.proofs, round_var);

        let max_num_variables: Felt<C::F> = builder.constant(C::F::ONE);
        builder.assign(&max_num_variables, max_num_variables + round);

        let max_degree = builder.constant(C::F::from_canonical_usize(3));

        let (sub_rt, sub_e) = iop_verifier_state_verify(
            builder,
            challenger,
            out_claim,
            &prover_messages,
            max_num_variables,
            max_degree,
        );

        let expected_evaluation: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
        builder
            .range(0, num_prod_spec.clone())
            .for_each(|i_vec, builder| {
                let spec_index = i_vec[0];
                let eq_e = eq_eval(builder, &out_rt, &sub_rt);
                let alpha = builder.get(&alpha_pows, spec_index.clone());
                let max_round = builder.get(&tower_verifier_input.num_variables, spec_index);
                let round_limit: RVar<C::N> = builder.eval_expr(max_round - RVar::from(1));

                let prod: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

                let is_smaller = is_smaller_than(builder, round_var, round_limit);
                builder.if_eq(is_smaller, RVar::from(1)).then(|builder| {
                    let prod_slice = builder.get(&tower_verifier_input.prod_specs_eval, spec_index);
                    let prod_round_slice = builder.get(&prod_slice, round_var);
                    let pdt = product(builder, &prod_round_slice);
                    builder.assign(&prod, pdt);
                });

                builder.assign(
                    &expected_evaluation,
                    expected_evaluation + eq_e * alpha * prod,
                );
            });

        let num_variables_len = tower_verifier_input.num_variables.len();
        let logup_alpha_pows_slice =
            alpha_pows.slice(builder, num_prod_spec.clone(), alpha_len.clone());
        let logup_num_variables_slice = tower_verifier_input.num_variables.slice(
            builder,
            num_prod_spec.clone(),
            num_variables_len.clone(),
        );

        builder
            .range(0, num_logup_spec.clone())
            .for_each(|i_vec, builder| {
                let spec_index = i_vec[0];

                let alpha_numerator_idx = builder.eval_expr(spec_index * RVar::from(2));
                let alpha_denominator_idx =
                    builder.eval_expr(spec_index * RVar::from(2) + RVar::from(1));
                let alpha_numerator: Ext<<C as Config>::F, <C as Config>::EF> =
                    builder.get(&logup_alpha_pows_slice, alpha_numerator_idx);
                let alpha_denominator = builder.get(&logup_alpha_pows_slice, alpha_denominator_idx);

                let max_round = builder.get(&logup_num_variables_slice, spec_index);
                let round_limit: RVar<C::N> = builder.eval_expr(max_round - RVar::from(1));

                let eq_e = eq_eval(builder, &out_rt, &sub_rt);
                let prod: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

                let is_smaller = is_smaller_than(builder, round_var, round_limit);
                builder.if_eq(is_smaller, RVar::from(1)).then(|builder| {
                    let prod_slice =
                        builder.get(&tower_verifier_input.logup_specs_eval, spec_index);
                    let prod_round_slice = builder.get(&prod_slice, round_var);

                    let p1 = builder.get(&prod_round_slice, 0);
                    let p2 = builder.get(&prod_round_slice, 1);
                    let q1 = builder.get(&prod_round_slice, 2);
                    let q2 = builder.get(&prod_round_slice, 3);

                    builder.assign(
                        &prod,
                        alpha_numerator * (p1 * q2 + p2 * q1) + alpha_denominator * (q1 * q2),
                    );
                });

                builder.assign(&expected_evaluation, expected_evaluation + eq_e * prod);
            });

        builder.assert_ext_eq(expected_evaluation, sub_e);

        // derive single eval
        // rt' = r_merge || rt
        // r_merge.len() == ceil_log2(num_product_fanin)
        transcript_observe_label(builder, challenger, b"merge");
        let r_merge = challenger.sample_ext(builder);

        let coeffs: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(num_fanin);
        let one: Ext<<C as Config>::F, <C as Config>::EF> = builder.constant(C::EF::ONE);
        let c1: Ext<<C as Config>::F, <C as Config>::EF> = builder.eval(one - r_merge.clone());
        let c2: Ext<<C as Config>::F, <C as Config>::EF> = builder.eval(r_merge.clone());
        builder.set(&coeffs, 0, c1);
        builder.set(&coeffs, 1, c2);

        let r_merge_arr = builder.dyn_array(RVar::from(1));
        builder.set(&r_merge_arr, 0, r_merge);
        let rt_prime = join(builder, &sub_rt, &r_merge_arr);

        // generate next round challenge
        let next_alpha_len: Usize<C::N> =
            builder.eval(num_prod_spec.clone() + num_logup_spec.clone() + num_logup_spec.clone());
        transcript_observe_label(builder, challenger, b"combine subset evals");
        let next_alpha_pows = gen_alpha_pows(builder, challenger, next_alpha_len.clone());
        let next_round = builder.eval_expr(round_var + RVar::from(1));

        let next_prod_spec_evals: Ext<<C as Config>::F, <C as Config>::EF> =
            builder.constant(C::EF::ZERO);
        builder
            .range(0, num_prod_spec.clone())
            .for_each(|i_vec, builder| {
                let spec_index = i_vec[0];
                let alpha = builder.get(&next_alpha_pows, spec_index.clone());

                let max_round =
                    builder.get(&tower_verifier_input.num_variables, spec_index.clone());
                let round_limit: RVar<C::N> = builder.eval_expr(max_round - RVar::from(1));

                let is_smaller = is_smaller_than(builder, round_var, round_limit.clone());
                builder.if_eq(is_smaller, RVar::from(1)).then(|builder| {
                    let prod_slice = builder.get(&tower_verifier_input.prod_specs_eval, spec_index);
                    let prod_round_slice = builder.get(&prod_slice, round_var);
                    let evals = dot_product(builder, &prod_round_slice, &coeffs);

                    builder.set(&prod_spec_point_n_eval, spec_index, PointAndEvalVariable {
                        point: PointVariable { fs: rt_prime.clone() },
                        eval: evals,
                    });

                    let is_next_smaller = is_smaller_than(builder, next_round, round_limit);
                    builder.if_eq(is_next_smaller, RVar::from(1)).then(|builder| {
                        let new_subsum: Ext<C::F, C::EF> = builder.eval(evals * alpha);
                        builder.assign(&next_prod_spec_evals, next_prod_spec_evals + new_subsum);
                    });
                });
            });
            
        let next_logup_spec_evals: Ext<<C as Config>::F, <C as Config>::EF> =
            builder.constant(C::EF::ZERO);
        let logup_next_alpha_pows_slice =
            next_alpha_pows.slice(builder, num_prod_spec.clone(), next_alpha_len.clone());
        let logup_num_variables_slice = tower_verifier_input.num_variables.slice(
            builder,
            num_prod_spec.clone(),
            num_variables_len.clone(),
        );

        builder
            .range(0, num_logup_spec.clone())
            .for_each(|i_vec, builder| {
                let spec_index = i_vec[0];
                let max_round = builder.get(&logup_num_variables_slice, spec_index);
                let round_limit: RVar<C::N> = builder.eval_expr(max_round - RVar::from(1));

                let is_smaller = is_smaller_than(builder, round_var, round_limit);
                builder.if_eq(is_smaller, RVar::from(1)).then(|builder| {
                    let alpha_numerator_idx = builder.eval_expr(spec_index * RVar::from(2));
                    let alpha_denominator_idx =
                        builder.eval_expr(spec_index * RVar::from(2) + RVar::from(1));
                    let alpha_numerator =
                        builder.get(&logup_next_alpha_pows_slice, alpha_numerator_idx);
                    let alpha_denominator =
                        builder.get(&logup_next_alpha_pows_slice, alpha_denominator_idx);

                    let prod_slice =
                        builder.get(&tower_verifier_input.logup_specs_eval, spec_index);
                    let prod_round_slice = builder.get(&prod_slice, round_var);
                    let p1 = builder.get(&prod_round_slice, 0);
                    let p2 = builder.get(&prod_round_slice, 1);
                    let q1 = builder.get(&prod_round_slice, 2);
                    let q2 = builder.get(&prod_round_slice, 3);
                    let c1 = builder.get(&coeffs, 0);
                    let c2 = builder.get(&coeffs, 1);

                    let p_eval: Ext<<C as Config>::F, <C as Config>::EF> =
                        builder.constant(C::EF::ZERO);
                    let q_eval: Ext<<C as Config>::F, <C as Config>::EF> =
                        builder.constant(C::EF::ZERO);
                    builder.assign(&p_eval, p1 * c1 + p2 * c2);
                    builder.assign(&q_eval, q1 * c1 + q2 * c2);

                    builder.set(&logup_spec_p_point_n_eval, spec_index, PointAndEvalVariable {
                        point: PointVariable { fs: rt_prime.clone() },
                        eval: p_eval,
                    });
                    builder.set(&logup_spec_q_point_n_eval, spec_index, PointAndEvalVariable {
                        point: PointVariable { fs: rt_prime.clone() },
                        eval: q_eval,
                    });

                    let is_next_smaller = is_smaller_than(builder, next_round, round_limit);
                    builder.if_eq(is_next_smaller, RVar::from(1)).then(|builder| {
                        builder.assign(
                            &next_logup_spec_evals,
                            next_logup_spec_evals
                                + alpha_numerator * p_eval
                                + alpha_denominator * q_eval,
                        );
                    });
                })
            });

        iter_zip!(builder, alpha_pows, next_alpha_pows).for_each(|ptr_vec, builder| {
            let new_alpha = builder.iter_ptr_get(&next_alpha_pows, ptr_vec[1]);
            builder.iter_ptr_set(&alpha_pows, ptr_vec[0], new_alpha);
        });

        // _debug
        // builder.print_debug(101);
        // builder.print_e(next_prod_spec_evals);
        // builder.print_e(next_logup_spec_evals);

        builder.assign(&curr_pt, rt_prime.clone());
        builder.assign(&curr_eval, next_prod_spec_evals + next_logup_spec_evals);
        builder.assign(&round, round + C::F::ONE);

        next_rt = PointAndEvalVariable {
            point: PointVariable {
                fs: rt_prime.clone(),
            },
            eval: curr_eval.clone(),
        };
    });

    (
        next_rt.point,
        prod_spec_point_n_eval,
        logup_spec_p_point_n_eval,
        logup_spec_q_point_n_eval,
    )
}

pub mod tests {
    use crate::tower_verifier::binding::{IOPProverMessage, Point, TowerVerifierInput, F};
    use crate::transcript::transcript_observe_label;
    use ceno_zkvm::scheme::{verifier, ZKVMProof};
    use mpcs::{Basefold, BasefoldCommitment, BasefoldRSParams};
    use openvm::io::println;
    use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::{AsmBuilder, AsmConfig};
    use openvm_native_compiler::prelude::*;
    use openvm_native_recursion::challenger::ChallengerVariable;
    use openvm_native_recursion::challenger::FeltChallenger;
    use openvm_native_recursion::{
        challenger::{duplex::DuplexChallengerVariable, CanObserveVariable, CanSampleVariable},
        fri::witness,
        hints::Hintable,
        types::InnerConfig,
    };
    use openvm_stark_backend::config::StarkGenericConfig;
    use openvm_stark_sdk::{
        config::baby_bear_poseidon2::{default_engine, BabyBearPoseidon2Config},
        p3_baby_bear::BabyBear,
    };
    use p3_field::{
        extension::BinomialExtensionField, FieldAlgebra, FieldExtensionAlgebra, PrimeField32,
        PrimeField64,
    };
    use p3_util::array_serialization::deserialize;
    use serde::{Deserialize, Serialize};
    use serde_json::Value;
    use std::io::Read;
    use std::{default, fs::File};

    use super::verify_tower_proof;
    type SC = BabyBearPoseidon2Config;
    type EF = <SC as StarkGenericConfig>::Challenge;
    type Challenger = <SC as StarkGenericConfig>::Challenger;

    use crate::tower_verifier::binding::E;
    use ff_ext::BabyBearExt4;

    type B = BabyBear;
    type Pcs = Basefold<E, BasefoldRSParams>;

    fn read_json() -> Value {
        let mut file = File::open("zkvm_proof.json").unwrap();
        let mut contents = String::new();
        let _ = file.read_to_string(&mut contents);
        serde_json::from_str(&contents).unwrap()
    }

    fn print_structure(value: &Value, indent: usize) {
        let recursive = false;
        // Generate indentation for pretty printing
        let indent_str = "  ".repeat(indent);

        match value {
            // If it's an object, recursively print each key-value pair's type
            Value::Object(obj) => {
                println!("{}Object ({} fields):", indent_str, obj.len());
                for (key, val) in obj {
                    println!("{}  {}: ", indent_str, key);
                    print_structure(val, indent + 1);
                }
            }

            // If it's an array, recursively print the type of each item
            Value::Array(arr) => {
                println!("{}Array ({} elements):", indent_str, arr.len());
                for (i, item) in arr.iter().enumerate() {
                    println!("{}  [{}]:", indent_str, i);
                    if recursive {
                        print_structure(item, indent + 1);
                    }
                }
            }

            // If it's a string, print its type
            Value::String(_) => {
                println!("{}String", indent_str);
            }

            // If it's a number (integer or float), print its type
            Value::Number(_) => {
                println!("{}Number", indent_str);
            }

            // If it's a boolean, print its type
            Value::Bool(_) => {
                println!("{}Boolean", indent_str);
            }

            // If it's null, print its type
            Value::Null => {
                println!("{}Null", indent_str);
            }
        }
    }

    #[derive(Default, Debug)]
    pub struct ZKVMProofJSONParsed {
        raw_pi: Vec<Vec<F>>,

        circuit_vks_fixed_commits: Vec<BasefoldCommitment<BabyBearExt4>>,
        opcode_proof_commits: Vec<BasefoldCommitment<BabyBearExt4>>,
        table_proof_commits: Vec<BasefoldCommitment<BabyBearExt4>>,

        pub prod_out_evals: Vec<Vec<E>>,
        pub logup_out_evals: Vec<Vec<E>>,
        pub num_variables: Vec<usize>,
        pub num_fanin: usize,

        // TowerProof
        pub num_proofs: usize,
        pub num_prod_specs: usize,
        pub num_logup_specs: usize,
        pub max_num_variables: usize,

        proofs: Vec<Vec<IOPProverMessage>>,
        prod_specs_eval: Vec<Vec<Vec<E>>>,
        logup_specs_eval: Vec<Vec<Vec<E>>>,
    }

    fn parse_json() -> ZKVMProofJSONParsed {
        let mut res = ZKVMProofJSONParsed::default();

        let filename = "zkvm_proof.json";
        let section = "opcode_proofs";
        let opcode_idx: usize = 0;
        let opcode_str = "ADD";

        let mut file = File::open(filename).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents);
        let data: Value = serde_json::from_str(&contents).unwrap();

        // Check if the root is an object (it is in this case)
        if let Some(obj) = data.as_object() {
            let mut raw_pi_vec: Vec<Vec<F>> = vec![];

            if let Some(raw_pi) = obj.get("raw_pi").and_then(Value::as_array) {
                for pi in raw_pi {
                    let mut sub_pi_vec: Vec<F> = vec![];
                    let fs = Value::as_array(pi).expect("Correct structure");
                    for f in fs {
                        let f_v: F =
                            serde_json::from_value(f.clone()).expect("correct deserlization");
                        sub_pi_vec.push(f_v);
                    }
                    raw_pi_vec.push(sub_pi_vec);
                }
                res.raw_pi = raw_pi_vec;
            }

            // deal with opcode + table proof
            let opcode_proofs =
                Value::as_object(obj.get(section).expect("section")).expect("section");
            let table_proofs =
                Value::as_object(obj.get("table_proofs").expect("section")).expect("section");

            // Gather opcode proof and table proof commitments
            let opcode_keys = vec![
                "ADD", "ADDI", "ANDI", "BEQ", "BLTU", "BNE", "JALR", "LW", "ORI", "SB", "SRAI",
                "SRLI", "SUB", "SW",
            ];
            let table_keys = vec![
                "OPS_And",
                "OPS_Ltu",
                "OPS_Or",
                "OPS_Pow",
                "OPS_Xor",
                "PROGRAM",
                "RAM_Memory_PubIOTable",
                "RAM_Memory_StaticMemTable",
                "RAM_Register_RegTable",
                "RANGE_U14",
                "RANGE_U16",
                "RANGE_U5",
                "RANGE_U8",
            ];

            let mut opcode_commits: Vec<BasefoldCommitment<BabyBearExt4>> = vec![];
            for key in opcode_keys {
                let op_proof = Value::as_array(opcode_proofs.get(key).expect("opcode"))
                    .expect("opcode_section");
                let commit = op_proof[1].get("wits_commit").expect("commitment");
                let basefold_cmt: BasefoldCommitment<BabyBearExt4> =
                    serde_json::from_value(commit.clone()).expect("deserialization");
                opcode_commits.push(basefold_cmt);
            }
            res.opcode_proof_commits = opcode_commits;

            let mut table_commits: Vec<BasefoldCommitment<BabyBearExt4>> = vec![];
            for key in table_keys {
                let tb_proof =
                    Value::as_array(table_proofs.get(key).expect("table")).expect("table_section");
                let commit = tb_proof[1].get("wits_commit").expect("commitment");
                let basefold_cmt: BasefoldCommitment<BabyBearExt4> =
                    serde_json::from_value(commit.clone()).expect("deserialization");
                table_commits.push(basefold_cmt);
            }
            res.table_proof_commits = table_commits;

            // Parse out ADD proof for testing
            let opcode_proof =
                Value::as_array(opcode_proofs.get(opcode_str).expect("opcode_section"))
                    .expect("opcode_section");

            // prod_out_evals
            let mut prod_out_evals: Vec<Vec<E>> = vec![];

            let mut record_r_out_evals: Vec<E> = vec![];
            let record_r_out_evals_v =
                Value::as_array(opcode_proof[1].get("record_r_out_evals").expect("section"))
                    .expect("section");
            for e in record_r_out_evals_v {
                let e_v: E = serde_json::from_value(e.clone()).expect("conversion");
                record_r_out_evals.push(e_v);
            }
            prod_out_evals.push(record_r_out_evals);

            let mut record_w_out_evals: Vec<E> = vec![];
            let record_w_out_evals_v =
                Value::as_array(opcode_proof[1].get("record_w_out_evals").expect("section"))
                    .expect("section");
            for e in record_w_out_evals_v {
                let e_v: E = serde_json::from_value(e.clone()).expect("conversion");
                record_w_out_evals.push(e_v);
            }
            prod_out_evals.push(record_w_out_evals);
            res.prod_out_evals = prod_out_evals;

            // logup_out_evals
            let mut logup_out_evals: Vec<Vec<E>> = vec![];
            let mut inner: Vec<E> = vec![];

            for label in [
                "lk_p1_out_eval",
                "lk_p2_out_eval",
                "lk_q1_out_eval",
                "lk_q2_out_eval",
            ] {
                let e_v: E =
                    serde_json::from_value(opcode_proof[1].get(label).expect("section").clone())
                        .expect("conversion");
                inner.push(e_v);
            }
            logup_out_evals.push(inner);
            res.logup_out_evals = logup_out_evals;

            // parse out tower proof fields
            let tower_proof =
                Value::as_object(opcode_proof[1].get("tower_proof").expect("tower_proof"))
                    .expect("tower_proof");

            let mut proofs: Vec<Vec<IOPProverMessage>> = vec![];
            let proofs_section =
                Value::as_array(tower_proof.get("proofs").expect("proofs")).expect("proof");
            for proof in proofs_section {
                let mut proof_messages: Vec<IOPProverMessage> = vec![];
                let messages = Value::as_array(proof).expect("messages");
                for m in messages {
                    let mut evaluations_vec: Vec<E> = vec![];
                    let evaluations = Value::as_array(
                        Value::as_object(m)
                            .expect("IOPProverMessage")
                            .get("evaluations")
                            .expect("evaluations"),
                    )
                    .expect("evaluations");
                    for v in evaluations {
                        let e_v: E = serde_json::from_value(v.clone()).expect("e");
                        evaluations_vec.push(e_v);
                    }
                    proof_messages.push(IOPProverMessage {
                        evaluations: evaluations_vec,
                    });
                    // println!("=> m: {:?}", m);
                    // println!("=> m parsed evaluations: {:?}", evaluations_vec);
                }
                proofs.push(proof_messages);
            }
            res.num_proofs = proofs.len();
            res.proofs = proofs;

            let mut prod_specs_eval: Vec<Vec<Vec<E>>> = vec![];
            let prod_specs_eval_section =
                Value::as_array(tower_proof.get("prod_specs_eval").expect("eval")).expect("evals");
            for inner in prod_specs_eval_section {
                let mut inner_v: Vec<Vec<E>> = vec![];
                let v = Value::as_array(inner).expect("inner vec");
                for inner_inner in v {
                    let mut inner_evals_v: Vec<E> = vec![];
                    let inner_evals = Value::as_array(inner_inner).expect("inner evals vec");
                    for e in inner_evals {
                        let e_v: E = serde_json::from_value(e.clone()).expect("e");
                        inner_evals_v.push(e_v);
                    }
                    inner_v.push(inner_evals_v);
                }
                prod_specs_eval.push(inner_v);
            }
            res.num_prod_specs = prod_specs_eval.len();
            res.prod_specs_eval = prod_specs_eval;

            let mut logup_specs_eval: Vec<Vec<Vec<E>>> = vec![];
            let logup_specs_eval_section =
                Value::as_array(tower_proof.get("logup_specs_eval").expect("eval")).expect("evals");
            for inner in logup_specs_eval_section {
                let mut inner_v: Vec<Vec<E>> = vec![];
                let v = Value::as_array(inner).expect("inner vec");
                for inner_inner in v {
                    let mut inner_evals_v: Vec<E> = vec![];
                    let inner_evals = Value::as_array(inner_inner).expect("inner evals vec");
                    for e in inner_evals {
                        let e_v: E = serde_json::from_value(e.clone()).expect("e");
                        inner_evals_v.push(e_v);
                    }
                    inner_v.push(inner_evals_v);
                }
                logup_specs_eval.push(inner_v);
            }
            res.num_logup_specs = logup_specs_eval.len();
            res.logup_specs_eval = logup_specs_eval;

            res.num_variables = vec![17, 17, 19];
            res.num_fanin = 2;
            res.max_num_variables = 19;
        }

        // parse out fixed commits
        let mut vk_file = File::open("circuit_vks_fixed_commits.json").unwrap();
        let mut vk_contents = String::new();
        vk_file.read_to_string(&mut vk_contents);
        let data: Value = serde_json::from_str(&vk_contents).unwrap();

        let mut circuit_vks_fixed_commits: Vec<BasefoldCommitment<BabyBearExt4>> = vec![];
        for c in Value::as_array(&data).expect("conversion") {
            let cmt: BasefoldCommitment<BabyBearExt4> =
                serde_json::from_value(c.clone()).expect("conversion");
            circuit_vks_fixed_commits.push(cmt);
        }
        res.circuit_vks_fixed_commits = circuit_vks_fixed_commits;

        res
    }

    #[allow(dead_code)]
    pub fn build_tower_verifier_input() -> TowerVerifierInput {
        TowerVerifierInput {
            prod_out_evals: vec![vec![
                E::from_canonical_u64(0x01),
                E::from_canonical_u64(0x22),
            ]],
            logup_out_evals: vec![],
            num_variables: vec![2usize],
            num_fanin: 2,

            // TowerProof
            num_proofs: 1usize,
            num_prod_specs: 1usize,
            num_logup_specs: 0usize,
            _max_num_variables: 2usize,

            proofs: vec![vec![IOPProverMessage {
                evaluations: vec![
                    E::from_canonical_u64(0x03),
                    E::from_canonical_u64(0x04),
                    E::from_canonical_u64(0x05),
                    E::from_canonical_u64(0x06),
                ],
            }]],
            prod_specs_eval: vec![vec![vec![
                E::from_canonical_u64(0x07),
                E::from_canonical_u64(0x08),
            ]]],
            logup_specs_eval: vec![],
        }
    }

    #[allow(dead_code)]
    pub fn build_test_tower_verifier() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        // OpenVM DSL
        let engine = default_engine();
        let perm = engine.perm;
        let mut challenger = Challenger::new(perm.clone());

        let mut builder = AsmBuilder::<F, EF>::default();
        let mut challenger = DuplexChallengerVariable::new(&mut builder);

        // Obtain witness inputs
        let tower_verifier_input = TowerVerifierInput::read(&mut builder);

        // Initialize transcript
        transcript_observe_label(&mut builder, &mut challenger, b"riscv");

        // Setup pre-program transcript operations
        let parsed_zkvm_proof_fields = parse_json();

        for v in parsed_zkvm_proof_fields.raw_pi.clone() {
            for f in v {
                let f_v = builder.constant(f);
                challenger.observe(&mut builder, f_v);
            }
        }

        for cmt in parsed_zkvm_proof_fields.circuit_vks_fixed_commits.clone() {
            cmt.root().0.iter().for_each(|x| {
                let f: F = serde_json::from_str(&serde_json::to_string(x).expect("serialization"))
                    .expect("serialization bridge");
                let f_v: Felt<F> = builder.constant(f);
                challenger.observe(&mut builder, f_v);
            });
        }

        for cmt in parsed_zkvm_proof_fields.opcode_proof_commits.clone() {
            cmt.root().0.iter().for_each(|x| {
                let f: F = serde_json::from_str(&serde_json::to_string(x).expect("serialization"))
                    .expect("serialization bridge");
                let f_v: Felt<F> = builder.constant(f);
                challenger.observe(&mut builder, f_v);
            });
        }

        for cmt in parsed_zkvm_proof_fields.table_proof_commits.clone() {
            cmt.root().0.iter().for_each(|x| {
                let f: F = serde_json::from_str(&serde_json::to_string(x).expect("serialization"))
                    .expect("serialization bridge");
                let f_v: Felt<F> = builder.constant(f);
                challenger.observe(&mut builder, f_v);
            });
        }

        // Sampling before verification
        let _alpha = challenger.sample_ext(&mut builder);
        let _beta = challenger.sample_ext(&mut builder);

        // Fork the transcript depending on sub-circuit
        // ```
        //     => forking transcript length: 62
        //     => using transcript fork: 0
        // ```
        let transcript_forking_segment: usize = 0;
        let f_v: Felt<F> = builder.constant(F::from_canonical_usize(transcript_forking_segment));
        challenger.observe(&mut builder, f_v);

        let (_, _, _, _) = verify_tower_proof(&mut builder, &mut challenger, tower_verifier_input);
        builder.halt();

        // Pass in witness stream
        let mut witness_stream: Vec<
            Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
        > = Vec::new();

        let verifier_input = TowerVerifierInput {
            prod_out_evals: parsed_zkvm_proof_fields.prod_out_evals,
            logup_out_evals: parsed_zkvm_proof_fields.logup_out_evals,
            num_variables: parsed_zkvm_proof_fields.num_variables,
            num_fanin: parsed_zkvm_proof_fields.num_fanin,

            // TowerProof
            num_proofs: parsed_zkvm_proof_fields.num_proofs,
            num_prod_specs: parsed_zkvm_proof_fields.num_prod_specs,
            num_logup_specs: parsed_zkvm_proof_fields.num_logup_specs,
            _max_num_variables: parsed_zkvm_proof_fields.max_num_variables,

            proofs: parsed_zkvm_proof_fields.proofs,
            prod_specs_eval: parsed_zkvm_proof_fields.prod_specs_eval,
            logup_specs_eval: parsed_zkvm_proof_fields.logup_specs_eval,
        };

        witness_stream.extend(verifier_input.write());

        let program: Program<
            p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
        > = builder.compile_isa();

        (program, witness_stream)
    }

    #[test]
    fn test_tower_proof_verifier() {
        let (program, witness) = build_test_tower_verifier();

        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100);
        let config = NativeConfig::new(system_config, Native);

        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
        executor.execute(program, witness).unwrap();

        // _debug
        // let results = executor.execute_segments(program, witness).unwrap();
        // for seg in results {
        //     println!("=> cycle count: {:?}", seg.metrics.cycle_count);
        // }
    }
}
