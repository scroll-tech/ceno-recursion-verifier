use crate::tower_verifier::transcript::transcript_observe_label;
use crate::{sumcheck::construct_binary_evaluation_idxs, tower_verifier};
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use ark_poly::domain::EvaluationDomain;
use ark_std::collections::BTreeSet;
use nimue::{
    plugins::ark::{FieldChallenges, FieldReader},
    ByteChallenges, ByteReader,
};
use nimue_pow::{blake3::Blake3PoW, PoWChallenge};
use openvm::io::println;
use openvm_native_compiler::asm::AsmConfig;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::{
    challenger::ChallengerVariable,
    hints::{Hintable, InnerChallenge, InnerVal, VecAutoHintable},
};
use openvm_stark_sdk::{p3_baby_bear::BabyBear, p3_blake3::Blake3};
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

use super::{
    binding::{
        IOPProverMessage, IOPProverMessageVariable, Point, PointVariable, TowerVerifierInput,
        TowerVerifierInputVariable,
    },
    transcript,
};
type PowStrategy = Blake3PoW;
type InnerConfig = AsmConfig<InnerVal, InnerChallenge>;
const NUM_FANIN: usize = 2;
const MAX_DEGREE: usize = 3;

/// A point and the evaluation of this point.
#[derive(Clone)]
pub struct PointAndEvalVariable<C: Config> {
    pub point: Option<PointVariable<C>>, // None: initial_rt
    pub eval: Ext<C::F, C::EF>,
}

pub fn evaluate_at_point<C: Config>(
    builder: &mut Builder<C>,
    evals: &Array<C, Ext<C::F, C::EF>>,
    point: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<C::F, C::EF> {
    // TODO: Dynamic length
    // TODO: Sanity checks
    let left = builder.get(&evals, 0);
    let right = builder.get(&evals, 1);
    let r = builder.get(point, 0);

    builder.eval(r * (right - left) + left)
}

fn dot_product<C: Config>(
    builder: &mut Builder<C>,
    a: &Array<C, Ext<C::F, C::EF>>,
    b: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<<C as Config>::F, <C as Config>::EF> {
    let mut acc: Ext<C::F, C::EF> = builder.eval(C::F::ZERO);

    iter_zip!(builder, a, b).for_each(|idx_vec, builder| {
        let ptr_a = idx_vec[0];
        let ptr_b = idx_vec[1];
        let v_a = builder.iter_ptr_get(&a, ptr_a);
        let v_b = builder.iter_ptr_get(&b, ptr_b);
        let new_acc = builder.eval(acc + v_a * v_b);
        acc = new_acc;
    });

    acc
}

fn reverse<C: Config>(
    builder: &mut Builder<C>,
    arr: &Array<C, Ext<C::F, C::EF>>,
) -> Array<C, Ext<C::F, C::EF>> {
    let len = arr.len();
    let res: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(len.clone());
    builder.range(0, len.clone()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let rev_i: RVar<_> = builder.eval_expr(len.clone() - i - RVar::from(1));

        let el = builder.get(arr, i);
        builder.set(&res, rev_i, el);
    });

    res
}

// Interpolate a uni-variate degree-`p_i.len()-1` polynomial and evaluate this
// polynomial at `eval_at`:
//
//   \sum_{i=0}^len p_i * (\prod_{j!=i} (eval_at - j)/(i-j) )
//
pub(crate) fn interpolate_uni_poly<C: Config>(
    builder: &mut Builder<C>,
    p_i: Array<C, Ext<C::F, C::EF>>,
    eval_at: Ext<C::F, C::EF>,
) -> Ext<C::F, C::EF> {
    let len = p_i.len();
    let evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(len.clone());
    let prod = eval_at.clone();

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

    let res = builder.constant(C::EF::ZERO);

    let denom_up: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let i: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    builder.assign(&i, i + one);
    builder.range(2, len.clone()).for_each(|_i_vec, builder| {
        builder.assign(&denom_up, denom_up * i);
        builder.assign(&i, i + one);
    });
    let denom_down: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);

    let idx_vec: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(len.clone());
    let idx: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    builder.range(1, len.clone()).for_each(|i_vec, builder| {
        builder.set(&idx_vec, i_vec[0], idx);
        builder.assign(&idx, idx + one);
    });

    let len_limit = idx.clone();
    let idx_rev = reverse(builder, &idx_vec);
    let len_pos: Var<<C as Config>::N> = builder.eval(len.clone() - RVar::from(1));
    let neg_one: Ext<C::F, C::EF> = builder.constant(C::EF::NEG_ONE);
    iter_zip!(builder, idx_rev).for_each(|ptr_vec, builder| {
        let i = len_pos;
        let p = builder.get(&p_i, i);
        let eval = builder.get(&evals, i);
        let up_eval_inv: Ext<C::F, C::EF> = builder.eval(denom_up * eval);
        builder.assign(&up_eval_inv, up_eval_inv.inverse());
        builder.assign(&res, res + p * prod * denom_down * up_eval_inv);

        let len_ind = builder.iter_ptr_get(&idx_rev, ptr_vec[0]);
        builder.assign(&denom_up, denom_up * (len_limit - len_ind) * neg_one);
        builder.assign(&denom_down, len_ind);
        builder.assign(&len_ind, len_ind - one);
    });

    let p_i_0 = builder.get(&p_i, 0);
    let eval_0 = builder.get(&evals, 0);
    let up_eval_inv: Ext<C::F, C::EF> = builder.eval(denom_up * eval_0);
    builder.assign(&up_eval_inv, up_eval_inv.inverse());
    builder.assign(&res, res + p_i_0 * prod * denom_down * up_eval_inv);

    res
}

fn iop_verifier_state_verify<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    out_claim: &Ext<C::F, C::EF>,
    prover_messages: &Array<C, IOPProverMessageVariable<C>>,
    max_num_variables: RVar<C::N>,
) -> (
    Array<C, Ext<<C as Config>::F, <C as Config>::EF>>,
    Ext<<C as Config>::F, <C as Config>::EF>,
) {
    // TODO: append message on aux_info
    // transcript.append_message(&aux_info.max_num_variables.to_le_bytes());
    // transcript.append_message(&aux_info.max_degree.to_le_bytes());

    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let round: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let polynomials_received: Array<C, Array<C, Ext<C::F, C::EF>>> =
        builder.dyn_array(max_num_variables);
    let challenges: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(max_num_variables);

    builder
        .range(0, max_num_variables)
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let prover_msg = builder.get(&prover_messages, i);
            iter_zip!(builder, prover_msg.evaluations).for_each(|ptr_vec, builder| {
                let e = builder.iter_ptr_get(&prover_msg.evaluations, ptr_vec[0]);
                let e_felts = builder.ext2felt(e);
                challenger.observe_slice(builder, e_felts);
            });

            let challenge = challenger.sample_ext(builder);
            let challenger_felts = builder.ext2felt(challenge);
            challenger.observe_slice(builder, challenger_felts);

            builder.set(&challenges, i, challenge);
            builder.set(&polynomials_received, i, prover_msg.evaluations);
            builder.assign(&round, round + one);
        });

    // set `expected` to P(r)`
    let expected_len: RVar<_> = builder.eval_expr(polynomials_received.len() + RVar::from(1));
    let expected_vec: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(expected_len.clone());
    builder.set(&expected_vec, 0, out_claim.clone());

    let truncated_expected_vec = expected_vec.slice(builder, 0, max_num_variables);
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
        let expected = interpolate_uni_poly(builder, evaluations, c);
        builder.iter_ptr_set(&expected_vec, expected_ptr, expected);
    });

    // l-append asserted_sum to the first position of the expected vector
    iter_zip!(builder, polynomials_received, truncated_expected_vec).for_each(
        |idx_vec, builder| {
            let evaluations = builder.iter_ptr_get(&polynomials_received, idx_vec[0]);
            let expected = builder.iter_ptr_get(&expected_vec, idx_vec[1]);

            let e1 = builder.get(&evaluations, 0);
            let e2 = builder.get(&evaluations, 1);
            let target: Ext<<C as Config>::F, <C as Config>::EF> = builder.eval(e1 + e2);

            // TODO: Enable scalar check
            // builder.assert_ext_eq(expected, target);
        },
    );

    let expected = builder.get(&expected_vec, max_num_variables);

    (challenges, expected)
}

// Evaluate eq polynomial.
fn eq_eval<C: Config>(
    builder: &mut Builder<C>,
    x: &Array<C, Ext<C::F, C::EF>>,
    y: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<C::F, C::EF> {
    let mut acc: Ext<C::F, C::EF> = builder.eval(C::F::ZERO);

    iter_zip!(builder, x, y).for_each(|idx_vec, builder| {
        let ptr_x = idx_vec[0];
        let ptr_y = idx_vec[1];
        let v_x = builder.iter_ptr_get(&x, ptr_x);
        let v_y = builder.iter_ptr_get(&y, ptr_y);
        let xi_yi: Ext<C::F, C::EF> = builder.eval(v_x * v_y);
        let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
        let new_acc = builder.eval(acc * (xi_yi + xi_yi - v_x - v_y + one));
        acc = new_acc;
    });

    acc
}

// Multiply all elements in the Array
fn product<C: Config>(
    builder: &mut Builder<C>,
    arr: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<C::F, C::EF> {
    let acc = builder.constant(C::EF::ONE);
    iter_zip!(builder, arr).for_each(|idx_vec, builder| {
        let el = builder.iter_ptr_get(arr, idx_vec[0]);
        builder.assign(&acc, acc * el);
    });

    acc
}

// Join two arrays
fn join<C: Config>(
    builder: &mut Builder<C>,
    a: &Array<C, Ext<C::F, C::EF>>,
    b: &Array<C, Ext<C::F, C::EF>>,
) -> Array<C, Ext<C::F, C::EF>> {
    let a_len = a.len();
    let b_len = b.len();
    let out_len = builder.eval_expr(a_len.clone() + b_len.clone());
    let out = builder.dyn_array(out_len);

    builder.range(0, a_len.clone()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let a_val = builder.get(a, i);
        builder.set(&out, i, a_val);
    });

    builder.range(0, b_len).for_each(|i_vec, builder| {
        let b_i = i_vec[0];
        let i = builder.eval_expr(b_i + a_len.clone());
        let b_val = builder.get(b, b_i);
        builder.set(&out, i, b_val);
    });

    out
}

// Generate alpha power challenges
fn gen_alpha_pows<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    alpha_len: RVar<<C as Config>::N>,
) -> Array<C, Ext<C::F, C::EF>> {
    let alpha = challenger.sample_ext(builder);
    let alpha_felts = builder.ext2felt(alpha);
    challenger.observe_slice(builder, alpha_felts);
    let alpha_pows: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(alpha_len);
    let mut prev = C::EF::ONE.cons();
    iter_zip!(builder, alpha_pows).for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        builder.iter_ptr_set(&alpha_pows, ptr, prev.clone());
        prev *= alpha;
    });

    alpha_pows
}

fn verify_tower_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    tower_verifier_input: TowerVerifierInputVariable<C>,
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

    let log2_num_fanin = 1usize;

    let alpha_len =
        builder.eval_expr(num_prod_spec.clone() + num_logup_spec.clone() + num_logup_spec.clone());
    let alpha_pows = gen_alpha_pows(builder, challenger, alpha_len);

    // initial_claim = \sum_j alpha^j * out_j[rt]
    // out_j[rt] := (record_{j}[rt])
    // out_j[rt] := (logup_p{j}[rt])
    // out_j[rt] := (logup_q{j}[rt])
    let initial_rt: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(RVar::from(log2_num_fanin));
    iter_zip!(builder, initial_rt).for_each(|ptr_vec, builder| {
        let pt = builder.iter_ptr_get(&initial_rt, ptr_vec[0]);
        let pt_felts = builder.ext2felt(pt);
        challenger.observe_slice(builder, pt_felts);
    });
    iter_zip!(builder, initial_rt).for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let new_challenge = challenger.sample_ext(builder);
        builder.iter_ptr_set(&initial_rt, ptr, new_challenge);
    });

    let prod_spec_point_n_eval: Array<C, Ext<C::F, C::EF>> =
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
        builder.iter_ptr_set(&prod_spec_point_n_eval, p_ptr, e);
    });

    let logup_spec_p_point_n_eval: Array<C, Ext<C::F, C::EF>> =
        builder.dyn_array(num_logup_spec.clone());
    let logup_spec_q_point_n_eval: Array<C, Ext<C::F, C::EF>> =
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

        builder.iter_ptr_set(&logup_spec_p_point_n_eval, p_ptr, e1);
        builder.iter_ptr_set(&logup_spec_q_point_n_eval, q_ptr, e2);
    });

    let interleaved_len = builder.eval_expr(num_logup_spec.clone() * RVar::from(2));
    let interleaved_point_n_eval: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(interleaved_len);
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
    let prod_sub_sum = dot_product(builder, &prod_spec_point_n_eval, &alpha_prod_slice);
    let alpha_logup_slice = alpha_pows.slice(builder, num_prod_spec.clone(), alpha_len.clone());
    let logup_sub_sum = dot_product(builder, &interleaved_point_n_eval, &alpha_logup_slice);
    let initial_claim: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    builder.assign(&initial_claim, prod_sub_sum + logup_sub_sum);

    let mut curr_pt = initial_rt.clone();
    let mut curr_eval = initial_claim.clone();
    let op_range = builder.eval_expr(tower_verifier_input.max_num_variables - RVar::from(1));
    builder.range(0, op_range).for_each(|i_vec, builder| {
        let round = i_vec[0];
        let out_rt = &curr_pt;
        let out_claim = &curr_eval;

        let prover_messages = builder.get(&tower_verifier_input.proofs, round);
        let max_num_variables = builder.eval_expr(round + RVar::from(1));
        let (sub_rt, sub_e) = iop_verifier_state_verify(
            builder,
            challenger,
            out_claim,
            &prover_messages,
            max_num_variables,
        );

        let mut expected_evaluation: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

        builder
            .range(0, num_prod_spec.clone())
            .for_each(|i_vec, builder| {
                let spec_index = i_vec[0];

                let alpha = builder.get(&alpha_pows, spec_index.clone());
                let max_round = builder.get(&tower_verifier_input.num_variables, spec_index);
                let round_limit: Var<<C as Config>::N> = builder.eval(max_round - RVar::from(1));

                builder.if_ne(round, round_limit).then(|builder| {
                    let eq_e = eq_eval(builder, &out_rt, &sub_rt);
                    let prod_slice = builder.get(&tower_verifier_input.prod_specs_eval, spec_index);
                    let prod_round_slice = builder.get(&prod_slice, round);
                    let prod = product(builder, &prod_round_slice);

                    builder.assign(
                        &expected_evaluation,
                        expected_evaluation + eq_e * alpha * prod,
                    );
                });
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
                let alpha_numerator = builder.get(&logup_alpha_pows_slice, alpha_numerator_idx);
                let alpha_denominator = builder.get(&logup_alpha_pows_slice, alpha_denominator_idx);

                let max_round = builder.get(&logup_num_variables_slice, spec_index);
                let round_limit: Var<<C as Config>::N> = builder.eval(max_round - RVar::from(1));

                builder.if_ne(round, round_limit).then(|builder| {
                    let eq_e = eq_eval(builder, &out_rt, &sub_rt);
                    let prod_slice =
                        builder.get(&tower_verifier_input.logup_specs_eval, spec_index);
                    let prod_round_slice = builder.get(&prod_slice, round);

                    let p1 = builder.get(&prod_round_slice, 0);
                    let p2 = builder.get(&prod_round_slice, 1);
                    let q1 = builder.get(&prod_round_slice, 2);
                    let q2 = builder.get(&prod_round_slice, 3);

                    builder.assign(
                        &expected_evaluation,
                        expected_evaluation
                            + eq_e
                                * (alpha_numerator * (p1 * q2 + p2 * q1)
                                    + alpha_denominator * (q1 * q2)),
                    );
                });
            });

        // TODO: Scalar check
        // builder.assert_ext_eq(expected_evaluation, sub_e);

        // derive single eval
        // rt' = r_merge || rt
        // r_merge.len() == ceil_log2(num_product_fanin)
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
        let next_alpha_len = builder
            .eval_expr(num_prod_spec.clone() + num_logup_spec.clone() + num_logup_spec.clone());
        let next_alpha_pows = gen_alpha_pows(builder, challenger, next_alpha_len);
        let next_round = builder.eval_expr(round + RVar::from(1));

        let next_prod_spec_evals: Ext<<C as Config>::F, <C as Config>::EF> =
            builder.constant(C::EF::ZERO);
        builder
            .range(0, num_prod_spec.clone())
            .for_each(|i_vec, builder| {
                let spec_index = i_vec[0];
                let alpha = builder.get(&next_alpha_pows, spec_index.clone());
                let max_round =
                    builder.get(&tower_verifier_input.num_variables, spec_index.clone());
                let round_limit: Var<<C as Config>::N> = builder.eval(max_round - RVar::from(1));

                builder.if_ne(round, round_limit).then(|builder| {
                    let prod_slice = builder.get(&tower_verifier_input.prod_specs_eval, spec_index);
                    let prod_round_slice = builder.get(&prod_slice, round);

                    builder.if_ne(next_round, round_limit).then(|builder| {
                        let evals = dot_product(builder, &prod_round_slice, &coeffs);
                        builder.assign(&next_prod_spec_evals, next_prod_spec_evals + evals * alpha);
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
            .range(0, num_prod_spec.clone())
            .for_each(|i_vec, builder| {
                let spec_index = i_vec[0];
                let max_round = builder.get(&logup_num_variables_slice, spec_index);
                let round_limit: Var<<C as Config>::N> = builder.eval(max_round - RVar::from(1));

                builder.if_ne(round, round_limit).then(|builder| {
                    let alpha_numerator_idx = builder.eval_expr(spec_index * RVar::from(2));
                    let alpha_denominator_idx =
                        builder.eval_expr(spec_index * RVar::from(2) + RVar::from(1));
                    let alpha_numerator =
                        builder.get(&logup_next_alpha_pows_slice, alpha_numerator_idx);
                    let alpha_denominator =
                        builder.get(&logup_next_alpha_pows_slice, alpha_denominator_idx);
                    let prod_slice =
                        builder.get(&tower_verifier_input.logup_specs_eval, spec_index);
                    let prod_round_slice = builder.get(&prod_slice, round);
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

                    builder.if_ne(next_round, round_limit).then(|builder| {
                        builder.assign(
                            &next_logup_spec_evals,
                            next_logup_spec_evals
                                + alpha_numerator * p_eval
                                + alpha_denominator * q_eval,
                        );
                    });
                });
            });

        let next_eval = builder.eval(next_prod_spec_evals + next_logup_spec_evals);
        curr_pt = rt_prime;
        curr_eval = next_eval;
    });
}

pub mod tests {
    use crate::tower_verifier::binding::{IOPProverMessage, Point, TowerVerifierInput, F};
    use crate::tower_verifier::transcript::transcript_observe_label;
    use ceno_zkvm::scheme::{verifier, ZKVMProof};
    use mpcs::{Basefold, BasefoldRSParams};
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
    use openvm_stark_backend::config::{StarkGenericConfig, Val};
    use openvm_stark_sdk::{
        config::baby_bear_poseidon2::{default_engine, BabyBearPoseidon2Config},
        p3_baby_bear::BabyBear,
    };
    use p3_field::{extension::BinomialExtensionField, FieldAlgebra, FieldExtensionAlgebra};
    use p3_util::array_serialization::deserialize;
    use serde::{Deserialize, Serialize};
    use serde_json::Value;
    use std::io::Read;
    use std::{default, fs::File};

    use super::verify_tower_proof;
    type SC = BabyBearPoseidon2Config;
    type EF = <SC as StarkGenericConfig>::Challenge;
    type Challenger = <SC as StarkGenericConfig>::Challenger;

    use ff_ext::BabyBearExt4;

    // _debug
    // type E = BabyBearExt4;
    use crate::tower_verifier::binding::E;

    type B = BabyBear;
    type Pcs = Basefold<E, BasefoldRSParams>;

    fn read_json() -> Value {
        let mut file = File::open("zkvm_proof.json").unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents);
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

    // _debug

    // #[derive(Clone, Serialize)]
    // pub struct ZKVMProof<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>> {
    //     pub raw_pi: Vec<Vec<E::BaseField>>,
    //     pub pi_evals: Vec<E>,
    //     opcode_proofs: BTreeMap<String, (usize, ZKVMOpcodeProof<E, PCS>)>,
    //     table_proofs: BTreeMap<String, (usize, ZKVMTableProof<E, PCS>)>,
    // }

    // BaseFold stuff

    // fn write_commitment(
    //     comm: &Self::Commitment,
    //     transcript: &mut impl Transcript<E>,
    // ) -> Result<(), Error> {
    //     write_digest_to_transcript(&comm.root(), transcript);
    //     Ok(())
    // }

    // pub fn write_digest_to_transcript<E: ExtensionField>(
    //     digest: &Digest<E::BaseField>,
    //     transcript: &mut impl Transcript<E>,
    // ) {
    //     digest
    //         .0
    //         .iter()
    //         .for_each(|x| transcript.append_field_element(x));
    // }

    // pub struct Digest<F: PrimeField>(pub [F; DIGEST_WIDTH]);

    // #[cfg(feature = "babybear")]
    // pub(crate) const DIGEST_WIDTH: usize = 8;

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

            // deal with opcode proof
            let opcode_proofs =
                Value::as_object(obj.get(section).expect("section")).expect("section");
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

            // _debug
            res.num_variables = vec![17, 17, 19];
            res.num_fanin = 2;
            res.max_num_variables = 19;
        }

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
            max_num_variables: 2usize,

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
        // Consult pre-opcode verification transcript operations here: _debug
        let parsed_zkvm_proof_fields = parse_json();

        for v in parsed_zkvm_proof_fields.raw_pi.clone() {
            for f in v {
                let f_v = builder.constant(f);
                challenger.observe(&mut builder, f_v);
            }
        }

        // _debug
        // println!("=> Parsed zkvm proof: {:?}", parsed_zkvm_proof_fields);
        // let proof = &parsed_zkvm_proof_fields.proofs[17];
        // for m in proof {
        //     println!("=> message: {:?}", m);
        // }

        // _debug
        // transcript_observe_label(&mut builder, &mut challenger, b"test");
        // let t = challenger.sample_ext(&mut builder);
        // println!("=> test challenge:");
        // builder.print_e(t);

        //         // write fixed commitment to transcript
        //         for (_, vk) in self.vk.circuit_vks.iter() {
        //             if let Some(fixed_commit) = vk.fixed_commit.as_ref() {
        //                 PCS::write_commitment(fixed_commit, &mut transcript)
        //                     .map_err(ZKVMError::PCSError)?;
        //             }
        //         }

        //         for (name, (_, proof)) in vm_proof.opcode_proofs.iter() {
        //             tracing::debug!("read {}'s commit", name);
        //             PCS::write_commitment(&proof.wits_commit, &mut transcript)
        //                 .map_err(ZKVMError::PCSError)?;
        //         }
        //         for (name, (_, proof)) in vm_proof.table_proofs.iter() {
        //             tracing::debug!("read {}'s commit", name);
        //             PCS::write_commitment(&proof.wits_commit, &mut transcript)
        //                 .map_err(ZKVMError::PCSError)?;
        //         }

        //         // alpha, beta
        //         let challenges = [
        //             transcript.read_challenge().elements,
        //             transcript.read_challenge().elements,
        //         ];
        //         tracing::debug!("challenges in verifier: {:?}", challenges);

        //         let dummy_table_item = challenges[0];
        //         let mut dummy_table_item_multiplicity = 0;
        //         let point_eval = PointAndEval::default();
        //         let mut transcripts = transcript.fork(self.vk.circuit_vks.len());

        //         for (name, (i, opcode_proof)) in vm_proof.opcode_proofs {
        //             let transcript = &mut transcripts[i];

        //             let circuit_vk = self
        //                 .vk
        //                 .circuit_vks
        //                 .get(&name)
        //                 .ok_or(ZKVMError::VKNotFound(name.clone()))?;
        //             let _rand_point = self.verify_opcode_proof(
        //                 &name,
        //                 &self.vk.vp,
        //                 circuit_vk,
        //                 &opcode_proof,
        //                 pi_evals,
        //                 transcript,
        //                 NUM_FANIN,
        //                 &point_eval,
        //                 &challenges,
        //             )?;

        verify_tower_proof(&mut builder, &mut challenger, tower_verifier_input);
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
            max_num_variables: parsed_zkvm_proof_fields.max_num_variables,
    
            proofs: parsed_zkvm_proof_fields.proofs,
            prod_specs_eval: parsed_zkvm_proof_fields.prod_specs_eval,
            logup_specs_eval: parsed_zkvm_proof_fields.logup_specs_eval,
        };

        witness_stream.extend(verifier_input.write());

        // _debug
        let program: Program<
            p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
        > = builder.compile_isa();

        (program, witness_stream)
    }

    #[test]
    fn test_tower_proof_verifier() {
        let (program, witness) = build_test_tower_verifier();

        // _debug
        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100);
        let config = NativeConfig::new(system_config, Native);

        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
        executor.execute(program, witness).unwrap();
    }
}
