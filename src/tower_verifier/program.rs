use super::binding::{
    IOPProverMessageVariable, PointAndEvalVariable, PointVariable, TowerVerifierInputVariable,
};
use crate::arithmetics::{
    challenger_multi_observe, dot_product, dot_product_pt_n_eval, eq_eval, evaluate_at_point,
    exts_to_felts, gen_alpha_pows, is_smaller_than, join, product, reverse,
};
use crate::transcript::transcript_observe_label;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::ChallengerVariable;
use openvm_native_recursion::challenger::{
    duplex::DuplexChallengerVariable, CanObserveVariable, FeltChallenger,
};
use p3_field::FieldAlgebra;

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

pub(crate) fn interpolate_uni_poly_with_weights<C: Config>(
    builder: &mut Builder<C>,
    p_i: &Array<C, Ext<C::F, C::EF>>,
    eval_at: Ext<C::F, C::EF>,
    interpolation_weights: &Array<C, Array<C, Ext<C::F, C::EF>>>,
) -> Ext<C::F, C::EF> {
    // \prod_i (eval_at - i)
    let weights_idx: Usize<C::N> = builder.eval(p_i.len() - Usize::from(2));
    let weights = builder.get(interpolation_weights, weights_idx);
    let num_points = p_i.len().get_var();

    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let mut iter_i: Ext<C::F, C::EF> = builder.eval(zero + zero); // 0 + 0 to take advantage of AddE
    let prod: Ext<C::F, C::EF> = builder.eval(one + zero); // 1 + 0 to take advantage of AddE
    builder.range(0, num_points).for_each(|_, builder| {
        builder.assign(&prod, prod * (eval_at - iter_i));
        builder.assign(&iter_i, iter_i + one);
    });

    iter_i = builder.eval(zero + zero); // reset to 0
    let result = zero; // take ownership
    iter_zip!(builder, p_i, weights).for_each(|ptr_vec, builder| {
        let pi_ptr = ptr_vec[0];
        let w_ptr = ptr_vec[1];

        let p_i_val = builder.iter_ptr_get(p_i, pi_ptr);
        let weight = builder.iter_ptr_get(&weights, w_ptr);

        // weight_i = \prod_{j!=i} 1/(i-j)
        // \sum_{i=0}^len p_i * weight_i * prod / (eval_at-i)
        let e: Ext<C::F, C::EF> = builder.eval(eval_at - iter_i);
        let term = p_i_val * weight * prod / e; // TODO: how to handle e = 0
        builder.assign(&iter_i, iter_i + one);
        builder.assign(&result, result + term);
    });

    result
}

pub fn iop_verifier_state_verify<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    out_claim: &Ext<C::F, C::EF>,
    prover_messages: &Array<C, IOPProverMessageVariable<C>>,
    max_num_variables: Felt<C::F>,
    max_degree: Felt<C::F>,
    interpolation_weights: &Array<C, Array<C, Ext<C::F, C::EF>>>,
) -> (
    Array<C, Ext<<C as Config>::F, <C as Config>::EF>>,
    Ext<<C as Config>::F, <C as Config>::EF>,
) {
    let max_num_variables_usize: Usize<C::N> =
        Usize::from(builder.cast_felt_to_var(max_num_variables.clone()));
    challenger.observe(builder, max_num_variables);
    challenger.observe(builder, max_degree);

    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let round: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let challenges: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(max_num_variables_usize.clone());

    builder
        .range(0, max_num_variables_usize.clone())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let prover_msg = builder.get(&prover_messages, i);

            builder.cycle_tracker_start("IOPVerifierState::verify_round_and_update_state");

            unsafe {
                let prover_msg_felts = exts_to_felts(builder, &prover_msg.evaluations);
                challenger_multi_observe(builder, challenger, &prover_msg_felts);
            }

            transcript_observe_label(builder, challenger, b"Internal round");
            let challenge = challenger.sample_ext(builder);

            builder.set(&challenges, i, challenge);
            builder.assign(&round, round + one);
            builder.cycle_tracker_end("IOPVerifierState::verify_round_and_update_state");
        });

    builder.cycle_tracker_start("IOPVerifierState::check_and_generate_subclaim");
    // set `expected` to P(r)`
    let expected_len: RVar<_> = builder.eval_expr(max_num_variables_usize.clone() + RVar::from(1));
    let expected_vec: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(expected_len.clone());
    builder.set(&expected_vec, 0, out_claim.clone());

    let truncated_expected_vec = expected_vec.slice(builder, 1, expected_len);
    iter_zip!(builder, prover_messages, challenges, truncated_expected_vec).for_each(
        |idx_vec, builder| {
            let poly_ptr = idx_vec[0];
            let c_ptr = idx_vec[1];

            let msg = builder.iter_ptr_get(&prover_messages, poly_ptr);
            let c = builder.iter_ptr_get(&challenges, c_ptr);

            let expected_ptr = idx_vec[2];
            // _debug
            // let expected = interpolate_uni_poly(builder, &msg, c);
            let expected = interpolate_uni_poly_with_weights(
                builder,
                &msg.evaluations,
                c,
                interpolation_weights,
            );

            builder.iter_ptr_set(&truncated_expected_vec, expected_ptr, expected);
        },
    );

    // l-append asserted_sum to the first position of the expected vector
    iter_zip!(builder, prover_messages, expected_vec).for_each(|idx_vec, builder| {
        let msg = builder.iter_ptr_get(&prover_messages, idx_vec[0]);
        let expected = builder.iter_ptr_get(&expected_vec, idx_vec[1]);

        let e1 = builder.get(&msg.evaluations, 0);
        let e2 = builder.get(&msg.evaluations, 1);
        let target: Ext<<C as Config>::F, <C as Config>::EF> = builder.eval(e1 + e2);

        builder.assert_ext_eq(expected, target);
    });

    let expected = builder.get(&expected_vec, max_num_variables_usize);
    builder.cycle_tracker_end("IOPVerifierState::check_and_generate_subclaim");

    (challenges, expected)
}

pub fn verify_tower_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    tower_verifier_input: TowerVerifierInputVariable<C>,
    interpolation_weights: &Array<C, Array<C, Ext<C::F, C::EF>>>,
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
    let op_range: RVar<C::N> =
        builder.eval_expr(tower_verifier_input.max_num_variables - Usize::from(1));
    let round: Felt<C::F> = builder.constant(C::F::ZERO);

    let mut next_rt = PointAndEvalVariable {
        point: PointVariable {
            fs: builder.dyn_array(1),
        },
        eval: builder.constant(C::EF::ZERO),
    };

    builder
        .range(0, op_range.clone())
        .for_each(|i_vec, builder| {
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
                interpolation_weights,
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
                        let prod_slice =
                            builder.get(&tower_verifier_input.prod_specs_eval, spec_index);
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
                    let alpha_denominator =
                        builder.get(&logup_alpha_pows_slice, alpha_denominator_idx);

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
            let next_alpha_len: Usize<C::N> = builder
                .eval(num_prod_spec.clone() + num_logup_spec.clone() + num_logup_spec.clone());
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
                        let prod_slice =
                            builder.get(&tower_verifier_input.prod_specs_eval, spec_index);
                        let prod_round_slice = builder.get(&prod_slice, round_var);
                        let evals = dot_product(builder, &prod_round_slice, &coeffs);

                        builder.set(
                            &prod_spec_point_n_eval,
                            spec_index,
                            PointAndEvalVariable {
                                point: PointVariable {
                                    fs: rt_prime.clone(),
                                },
                                eval: evals,
                            },
                        );

                        let is_next_smaller = is_smaller_than(builder, next_round, round_limit);
                        builder
                            .if_eq(is_next_smaller, RVar::from(1))
                            .then(|builder| {
                                let new_subsum: Ext<C::F, C::EF> = builder.eval(evals * alpha);
                                builder.assign(
                                    &next_prod_spec_evals,
                                    next_prod_spec_evals + new_subsum,
                                );
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

                        builder.set(
                            &logup_spec_p_point_n_eval,
                            spec_index,
                            PointAndEvalVariable {
                                point: PointVariable {
                                    fs: rt_prime.clone(),
                                },
                                eval: p_eval,
                            },
                        );
                        builder.set(
                            &logup_spec_q_point_n_eval,
                            spec_index,
                            PointAndEvalVariable {
                                point: PointVariable {
                                    fs: rt_prime.clone(),
                                },
                                eval: q_eval,
                            },
                        );

                        let is_next_smaller = is_smaller_than(builder, next_round, round_limit);
                        builder
                            .if_eq(is_next_smaller, RVar::from(1))
                            .then(|builder| {
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

#[cfg(test)]
mod tests {
    use crate::tower_verifier::binding::IOPProverMessage;
    use crate::tower_verifier::program::iop_verifier_state_verify;
    use ceno_mle::mle::DenseMultilinearExtension;
    use ceno_mle::virtual_poly::ArcMultilinearExtension;
    use ceno_mle::virtual_polys::VirtualPolynomials;
    use ceno_sumcheck::structs::IOPProverState;
    use ceno_transcript::BasicTranscript;
    use ff_ext::BabyBearExt4;
    use ff_ext::FieldFrom;
    use itertools::Itertools;
    use openvm_circuit::arch::SystemConfig;
    use openvm_circuit::arch::VmExecutor;
    use openvm_native_circuit::Native;
    use openvm_native_circuit::NativeConfig;
    use openvm_native_compiler::asm::AsmCompiler;
    use openvm_native_compiler::asm::{AsmBuilder, AsmConfig};
    use openvm_native_compiler::conversion::convert_program;
    use openvm_native_compiler::conversion::CompilerOptions;
    use openvm_native_compiler::ir::Array;
    use openvm_native_compiler::ir::Ext;
    use openvm_native_compiler::prelude::Felt;
    use openvm_native_recursion::challenger::duplex::DuplexChallengerVariable;
    use p3_baby_bear::BabyBear;
    use p3_field::Field;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::FieldAlgebra;
    use openvm_native_recursion::hints::Hintable;
    use rand::thread_rng;

    #[test]
    fn test_simple_sumcheck() {
        type F = BabyBear;
        type E = BabyBearExt4;
        type EF = BinomialExtensionField<BabyBear, 4>;
        type C = AsmConfig<F, EF>;

        let nv = 5;
        let degree = 3;

        let mut builder = AsmBuilder::<F, EF>::default();

        let out_claim = EF::read(&mut builder);
        let prover_msgs = Vec::<IOPProverMessage>::read(&mut builder);

        let max_num_variables: Felt<F> = builder.constant(F::from_canonical_u32(nv as u32));
        let max_degree: Felt<F> = builder.constant(F::from_canonical_u32(degree as u32));

        let mut challenger: DuplexChallengerVariable<C> =
            DuplexChallengerVariable::new(&mut builder);

        let interpolation_weights: Array<C, Array<C, Ext<F, EF>>> = builder.dyn_array(4);
        for deg in 1..=4usize {
            let points: Vec<EF> = (0..=deg)
                .into_iter()
                .map(|i| EF::from_canonical_u32(i as u32))
                .collect();
            let weights = points
                .iter()
                .enumerate()
                .map(|(j, point_j)| {
                    points
                        .iter()
                        .enumerate()
                        .filter(|&(i, _)| (i != j))
                        .map(|(_, point_i)| *point_j - *point_i)
                        .reduce(|acc, value| acc * value)
                        .unwrap_or(EF::ONE)
                        .inverse()
                })
                .collect::<Vec<_>>();

            let weight_array: Array<C, Ext<F, EF>> = builder.dyn_array(4);
            weights.into_iter().enumerate().for_each(|(i, w)| {
                let w: Ext<F, EF> = builder.constant(w);
                builder.set(&weight_array, i, w);
            });

            builder.set(&interpolation_weights, deg - 1, weight_array);
        }

        iop_verifier_state_verify(
            &mut builder,
            &mut challenger,
            &out_claim,
            &prover_msgs,
            max_num_variables,
            max_degree,
            &interpolation_weights,
        );

        builder.halt();

        // get the assembly code
        let options = CompilerOptions::default();
        let mut compiler = AsmCompiler::new(options.word_size);
        compiler.build(builder.operations);
        let asm_code = compiler.code();
        println!("asm code");
        println!("{asm_code}");

        // run sumcheck prover to get sumcheck proof
        let mut rng = thread_rng();
        let (mles, expected_sum) =
            DenseMultilinearExtension::<E>::random_mle_list(nv, degree, &mut rng);
        let mles: Vec<ArcMultilinearExtension<E>> =
            mles.into_iter().map(|mle| mle as _).collect_vec();
        let mut virtual_poly: VirtualPolynomials<'_, E> = VirtualPolynomials::new(1, nv);
        virtual_poly.add_mle_list(mles.iter().collect_vec(), E::from_v(1));

        let mut transcript = BasicTranscript::new(&[]);
        let (sumcheck_proof, _) = IOPProverState::prove(virtual_poly, &mut transcript);
        let mut input_stream = Vec::new();

        // hacky way: convert E to EF but actually they are the same
        let expected_sum: EF = cast_vec(vec![expected_sum])[0];
        input_stream.extend(expected_sum.write());
        input_stream.extend(
            sumcheck_proof
                .proofs
                .into_iter()
                .map(|msg| {
                    let evaluations: Vec<EF> = cast_vec(msg.evaluations);
                    IOPProverMessage { evaluations }
                })
                .collect_vec()
                .write(),
        );

        // get execution result
        let program = convert_program(asm_code, options);
        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100)
            .with_profiling();
        let config = NativeConfig::new(system_config, Native);
        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);

        let res = executor
            .execute_and_then(program, input_stream, |_, seg| Ok(seg), |err| err)
            .unwrap();

        for (i, seg) in res.iter().enumerate() {
            #[cfg(feature = "bench-metrics")]
            {
                println!(
                    "=> segment {} metrics.cycle_count: {:?}",
                    i, seg.metrics.cycle_count
                );
                for (insn, count) in seg.metrics.counts.iter() {
                    println!("insn: {:?}, count: {:?}", insn, count);
                }
                println!(
                    "=> segment {} #(insns): {}",
                    i,
                    seg.metrics
                        .counts
                        .values()
                        .copied()
                        .into_iter()
                        .sum::<usize>()
                );
            }
        }
    }

    fn cast_vec<A, B>(mut vec: Vec<A>) -> Vec<B> {
        let length = vec.len();
        let capacity = vec.capacity();
        let ptr = vec.as_mut_ptr();
        // Prevent `vec` from dropping its contents
        std::mem::forget(vec);

        // Convert the pointer to the new type
        let new_ptr = ptr as *mut B;

        // Create a new vector with the same length and capacity, but different type
        unsafe { Vec::from_raw_parts(new_ptr, length, capacity) }
    }
}
