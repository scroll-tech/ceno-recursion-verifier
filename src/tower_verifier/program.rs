use super::binding::{
    IOPProverMessageVariable, PointAndEvalVariable, PointVariable,
};
use crate::arithmetics::{
    challenger_multi_observe, dot_product, eq_eval, evaluate_at_point, extend, exts_to_felts,
    fixed_dot_product, gen_alpha_pows, is_smaller_than, reverse, UniPolyExtrapolator, print_ext_arr,
};
use crate::transcript::transcript_observe_label;
use crate::zkvm_verifier::binding::TowerProofInputVariable;
use ceno_zkvm::scheme::constants::NUM_FANIN;
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
    unipoly_extrapolator: &mut UniPolyExtrapolator<C>,
) -> (
    Array<C, Ext<<C as Config>::F, <C as Config>::EF>>,
    Ext<<C as Config>::F, <C as Config>::EF>,
) {
    // TODO: either store it in a global cache or pass them as parameters
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let zero_f: Felt<C::F> = builder.constant(C::F::ZERO);

    let max_num_variables_usize: Usize<C::N> =
        Usize::from(builder.cast_felt_to_var(max_num_variables.clone()));
    challenger.observe(builder, max_num_variables);
    challenger.observe(builder, zero_f);
    challenger.observe(builder, max_degree);
    challenger.observe(builder, zero_f);

    builder.assert_var_eq(max_num_variables_usize.get_var(), prover_messages.len());

    let challenges: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(max_num_variables_usize.clone());
    let expected: Ext<C::F, C::EF> = builder.eval(out_claim.clone() + zero);

    builder.cycle_tracker_start("IOPVerifierState::verify_round_and_update_state");
    builder
        .range(0, max_num_variables_usize.clone())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            // TODO: this takes 7 cycles, can we optimize it?
            let prover_msg = builder.get(&prover_messages, i);

            unsafe {
                let prover_msg_felts = exts_to_felts(builder, &prover_msg.evaluations);
                challenger_multi_observe(builder, challenger, &prover_msg_felts);
            }

            transcript_observe_label(builder, challenger, b"Internal round");
            let challenge = challenger.sample_ext(builder);

            let e1 = builder.get(&prover_msg.evaluations, 0);
            let e2 = builder.get(&prover_msg.evaluations, 1);
            let target: Ext<<C as Config>::F, <C as Config>::EF> = builder.eval(e1 + e2);
            builder.assert_ext_eq(expected, target);

            let p_r = unipoly_extrapolator.extrapolate_uni_poly(
                builder,
                &prover_msg.evaluations,
                challenge,
            );

            builder.assign(&expected, p_r + zero);
            builder.set_value(&challenges, i, challenge);
        });
    builder.cycle_tracker_end("IOPVerifierState::verify_round_and_update_state");

    (challenges, expected)
}

pub fn verify_tower_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    prod_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>>,
    logup_out_evals: &Array<C, Array<C, Ext<C::F, C::EF>>>,
    num_variables: Array<C, Usize<C::N>>,
    num_fanin: Usize<C::N>,

    // TowerProofVariable
    max_num_variables: Usize<C::N>,

    proof: &TowerProofInputVariable<C>,
    unipoly_extrapolator: &mut UniPolyExtrapolator<C>,
) -> (
    PointVariable<C>,
    Array<C, PointAndEvalVariable<C>>,
    Array<C, PointAndEvalVariable<C>>,
    Array<C, PointAndEvalVariable<C>>,
) {
    // _debug
    // let num_fanin: usize = 2;
    // builder.assert_usize_eq(num_fanin, RVar::from(num_fanin));
    let num_prod_spec = prod_out_evals.len();
    let num_logup_spec = logup_out_evals.len();

    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    builder.assert_usize_eq(
        proof.prod_specs_eval.len(),
        num_prod_spec.clone(),
    );
    iter_zip!(builder, prod_out_evals).for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let evals = builder.iter_ptr_get(&prod_out_evals, ptr);
        builder.assert_usize_eq(evals.len(), num_fanin.clone());
    });
    builder.assert_usize_eq(
        proof.logup_specs_eval.len(),
        num_logup_spec.clone(),
    );
    iter_zip!(builder, logup_out_evals).for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let evals = builder.iter_ptr_get(&logup_out_evals, ptr);
        builder.assert_usize_eq(evals.len(), RVar::from(4));
    });
    builder.assert_usize_eq(
        num_variables.len(),
        num_prod_spec.clone() + num_logup_spec.clone(),
    );

    let var_zero: Var<C::N> = builder.constant(C::N::ZERO);
    let var_one: Var<C::N> = builder.constant(C::N::ONE);
    let num_specs: Var<C::N> = builder.eval(num_prod_spec.get_var() + num_logup_spec.get_var());
    let should_skip: Array<C, Var<C::N>> = builder.dyn_array(num_specs);
    builder.range(0, num_specs).for_each(|i_vec, builder| {
        let i = i_vec[0];

        // all specs should not be skipped initially
        builder.set_value(&should_skip, i, var_zero.clone());
    });

    transcript_observe_label(builder, challenger, b"combine subset evals");
    let alpha = challenger.sample_ext(builder);
    let alpha_acc: Ext<C::F, C::EF> = builder.eval(zero + one);

    // initial_claim = \sum_j alpha^j * out_j[rt]
    // out_j[rt] := (record_{j}[rt])
    // out_j[rt] := (logup_p{j}[rt])
    // out_j[rt] := (logup_q{j}[rt])
    let log2_num_fanin = 1usize;
    builder.cycle_tracker_start("initial sum");
    let initial_rt: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(log2_num_fanin);
    transcript_observe_label(builder, challenger, b"product_sum");
    builder
        .range(0, initial_rt.len())
        .for_each(|idx_vec, builder| {
            let idx = idx_vec[0];
            let c = challenger.sample_ext(builder);
            builder.set_value(&initial_rt, idx, c);
        });

    let prod_spec_point_n_eval: Array<C, PointAndEvalVariable<C>> =
        builder.dyn_array(num_prod_spec.clone());

    iter_zip!(
        builder,
        prod_out_evals,
        prod_spec_point_n_eval
    )
    .for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let evals = builder.iter_ptr_get(&prod_out_evals, ptr);
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
        logup_out_evals,
        logup_spec_p_point_n_eval,
        logup_spec_q_point_n_eval
    )
    .for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let evals = builder.iter_ptr_get(&prod_out_evals, ptr);

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

    let mut initial_claim: Ext<C::F, C::EF> = builder.eval(zero + zero);

    iter_zip!(builder, prod_spec_point_n_eval).for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let prod_eval = builder.iter_ptr_get(&prod_spec_point_n_eval, ptr);
        builder.assign(&initial_claim, initial_claim + prod_eval.eval * alpha_acc);
        builder.assign(&alpha_acc, alpha_acc * alpha);
    });

    iter_zip!(builder, interleaved_point_n_eval).for_each(|ptr_vec, builder| {
        let ptr = ptr_vec[0];
        let logup_eval = builder.iter_ptr_get(&interleaved_point_n_eval, ptr);
        builder.assign(&initial_claim, initial_claim + logup_eval.eval * alpha_acc);
        builder.assign(&alpha_acc, alpha_acc * alpha);
    });
    builder.cycle_tracker_end("initial sum");

    let curr_pt = initial_rt.clone();
    let curr_eval = initial_claim.clone();
    let op_range: RVar<C::N> =
        builder.eval_expr(max_num_variables - Usize::from(1));
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
            let prover_messages = builder.get(&proof.proofs, round_var);

            let max_num_variables: Felt<C::F> = builder.constant(C::F::ONE);
            builder.assign(&max_num_variables, max_num_variables + round);

            let max_degree = builder.constant(C::F::from_canonical_usize(3));

            builder.cycle_tracker_start("sumcheck verify");
            let (sub_rt, sub_e) = iop_verifier_state_verify(
                builder,
                challenger,
                out_claim,
                &prover_messages,
                max_num_variables,
                max_degree,
                unipoly_extrapolator,
            );
            builder.cycle_tracker_end("sumcheck verify");

            builder.cycle_tracker_start("check expected evaluation");
            let eq_e = eq_eval(builder, &out_rt, &sub_rt, one, zero);

            let expected_evaluation: Ext<C::F, C::EF> = builder.eval(zero + zero);
            let alpha_acc: Ext<C::F, C::EF> = builder.eval(zero + one);

            builder
                .range(0, num_prod_spec.clone())
                .for_each(|i_vec, builder| {
                    builder.cycle_tracker_start("accumulate expected eval for prod specs");
                    let spec_index = i_vec[0];
                    let skip = builder.get(&should_skip, spec_index.clone());
                    let max_round = builder.get(&num_variables, spec_index);
                    let round_limit: RVar<C::N> = builder.eval_expr(max_round - RVar::from(1));

                    let prod: Ext<C::F, C::EF> = builder.eval(zero + zero);

                    // invariant: skip == 0 implies previous round_var is smaller than round_limit.
                    //
                    // if skip == 0 and current round_var is also not equal to round_limit,
                    // then we know round_var is also smaller than round_limit.
                    builder.if_eq(skip, var_zero.clone()).then(|builder| {
                        builder.if_ne(round_var, round_limit).then_or_else(
                            |builder| {
                                let prod_slice =
                                    builder.get(&proof.prod_specs_eval, spec_index);
                                let prod_round_slice = builder.get(&prod_slice, round_var);
                                builder.assign(&prod, one * one);
                                for j in 0..NUM_FANIN {
                                    let prod_j = builder.get(&prod_round_slice, j);
                                    builder.assign(&prod, prod * prod_j);
                                }
                            },
                            |builder| {
                                builder.set_value(&should_skip, spec_index, var_one.clone());
                            },
                        );
                    });

                    builder.assign(&expected_evaluation, expected_evaluation + alpha_acc * prod);
                    builder.assign(&alpha_acc, alpha_acc * alpha.clone());
                    builder.cycle_tracker_end("accumulate expected eval for prod specs");
                });

            let num_variables_len = num_variables.len();
            let logup_num_variables_slice = num_variables.slice(
                builder,
                num_prod_spec.clone(),
                num_variables_len.clone(),
            );

            builder
                .range(0, num_logup_spec.clone())
                .for_each(|i_vec, builder| {
                    builder.cycle_tracker_start("accumulate expected eval for logup specs");
                    let spec_index = i_vec[0];

                    let alpha_numerator: Ext<<C as Config>::F, <C as Config>::EF> =
                        builder.eval(alpha_acc * one);
                    builder.assign(&alpha_acc, alpha_acc * alpha);
                    let alpha_denominator: Ext<C::F, C::EF> = builder.eval(alpha_acc * one);
                    builder.assign(&alpha_acc, alpha_acc * alpha);

                    let idx: Var<C::N> =
                        builder.eval(spec_index.variable() + num_prod_spec.get_var());
                    let skip = builder.get(&should_skip, idx);
                    let max_round = builder.get(&logup_num_variables_slice, spec_index);
                    let round_limit: RVar<C::N> = builder.eval_expr(max_round - RVar::from(1));

                    let prod: Ext<C::F, C::EF> = builder.eval(zero + zero);

                    builder.if_eq(skip, var_zero).then(|builder| {
                        builder.if_ne(round_var, round_limit).then_or_else(
                            |builder| {
                                let prod_slice =
                                    builder.get(&proof.logup_specs_eval, spec_index);
                                let prod_round_slice = builder.get(&prod_slice, round_var);

                                let p1 = builder.get(&prod_round_slice, 0);
                                let p2 = builder.get(&prod_round_slice, 1);
                                let q1 = builder.get(&prod_round_slice, 2);
                                let q2 = builder.get(&prod_round_slice, 3);
                                builder.assign(
                                    &prod,
                                    alpha_numerator * (p1 * q2 + p2 * q1)
                                        + alpha_denominator * (q1 * q2),
                                );
                            },
                            |builder| {
                                builder.set_value(&should_skip, idx, var_one.clone());
                            },
                        );
                    });

                    builder.assign(&expected_evaluation, expected_evaluation + prod);
                    builder.cycle_tracker_end("accumulate expected eval for logup specs");
                });

            builder.assign(&expected_evaluation, expected_evaluation * eq_e);
            builder.assert_ext_eq(expected_evaluation, sub_e);
            builder.cycle_tracker_end("check expected evaluation");

            builder.cycle_tracker_start("derive next layer's expected sum");
            // derive single eval
            // rt' = r_merge || rt
            // r_merge.len() == ceil_log2(num_product_fanin)
            transcript_observe_label(builder, challenger, b"merge");

            builder.cycle_tracker_start("derive rt_prime");
            let r_merge = challenger.sample_ext(builder);

            let c1: Ext<<C as Config>::F, <C as Config>::EF> = builder.eval(one - r_merge.clone());
            let c2: Ext<<C as Config>::F, <C as Config>::EF> = builder.eval(r_merge.clone());
            let coeffs = vec![c1, c2];

            let rt_prime = extend(builder, &sub_rt, &r_merge);
            builder.cycle_tracker_end("derive rt_prime");

            // generate next round challenge
            transcript_observe_label(builder, challenger, b"combine subset evals");
            let new_alpha = challenger.sample_ext(builder);
            builder.assign(&alpha, new_alpha);
            builder.assign(&alpha_acc, zero + one);

            let next_round = builder.eval_expr(round_var + RVar::from(1));

            let next_prod_spec_evals: Ext<<C as Config>::F, <C as Config>::EF> =
                builder.eval(zero + zero); // simple trick to avoid AddEI
            builder
                .range(0, num_prod_spec.clone())
                .for_each(|i_vec, builder| {
                    builder.cycle_tracker_start("derive next layer for prod specs");
                    let spec_index = i_vec[0];
                    let skip = builder.get(&should_skip, spec_index.clone());
                    let max_round =
                        builder.get(&num_variables, spec_index.clone());
                    let round_limit: RVar<C::N> = builder.eval_expr(max_round - RVar::from(1));

                    // now skip is 0 if and only if current round_var is smaller than round_limit.
                    builder.if_eq(skip, var_zero.clone()).then(|builder| {
                        let prod_slice =
                            builder.get(&proof.prod_specs_eval, spec_index);
                        let prod_round_slice = builder.get(&prod_slice, round_var);
                        let evals = fixed_dot_product(builder, &coeffs, &prod_round_slice, zero);

                        builder.if_ne(next_round, round_limit).then_or_else(
                            |builder| {
                                let new_subsum: Ext<C::F, C::EF> = builder.eval(evals * alpha_acc);
                                builder.assign(
                                    &next_prod_spec_evals,
                                    next_prod_spec_evals + new_subsum,
                                );
                            },
                            // update point and eval only for last layer
                            |builder| {
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
                            },
                        );
                    });

                    builder.assign(&alpha_acc, alpha_acc * alpha.clone());
                    builder.cycle_tracker_end("derive next layer for prod specs");
                });

            let next_logup_spec_evals: Ext<<C as Config>::F, <C as Config>::EF> =
                builder.eval(zero + zero);
            let logup_num_variables_slice = num_variables.slice(
                builder,
                num_prod_spec.clone(),
                num_variables_len.clone(),
            );

            builder
                .range(0, num_logup_spec.clone())
                .for_each(|i_vec, builder| {
                    builder.cycle_tracker_start("derive next layer for logup specs");
                    let spec_index = i_vec[0];
                    let max_round = builder.get(&logup_num_variables_slice, spec_index);
                    let round_limit: RVar<C::N> = builder.eval_expr(max_round - RVar::from(1));
                    let idx: Var<C::N> =
                        builder.eval(spec_index.variable() + num_prod_spec.get_var());
                    let skip = builder.get(&should_skip, idx);

                    let alpha_numerator: Ext<C::F, C::EF> = builder.eval(alpha_acc * one);
                    builder.assign(&alpha_acc, alpha_acc * alpha.clone());
                    let alpha_denominator: Ext<C::F, C::EF> = builder.eval(alpha_acc * one);
                    builder.assign(&alpha_acc, alpha_acc * alpha.clone());

                    // now skip is 0 if and only if current round_var is smaller than round_limit.
                    builder.if_eq(skip, var_zero).then(|builder| {
                        let prod_slice =
                            builder.get(&proof.logup_specs_eval, spec_index);
                        let prod_round_slice = builder.get(&prod_slice, round_var);
                        let p1 = builder.get(&prod_round_slice, 0);
                        let p2 = builder.get(&prod_round_slice, 1);
                        let q1 = builder.get(&prod_round_slice, 2);
                        let q2 = builder.get(&prod_round_slice, 3);

                        let p_eval: Ext<<C as Config>::F, <C as Config>::EF> =
                            builder.eval(zero + zero);
                        let q_eval: Ext<<C as Config>::F, <C as Config>::EF> =
                            builder.eval(zero + zero);
                        builder.assign(&p_eval, p1 * coeffs[0] + p2 * coeffs[1]);
                        builder.assign(&q_eval, q1 * coeffs[0] + q2 * coeffs[1]);

                        builder.if_ne(next_round, round_limit).then_or_else(
                            |builder| {
                                builder.assign(
                                    &next_logup_spec_evals,
                                    next_logup_spec_evals
                                        + alpha_numerator * p_eval
                                        + alpha_denominator * q_eval,
                                );
                            },
                            // update point and eval only for last layer
                            |builder| {
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
                            },
                        );
                    });
                    builder.cycle_tracker_end("derive next layer for logup specs");
                });

            builder.assign(&curr_pt, rt_prime.clone());
            builder.assign(&curr_eval, next_prod_spec_evals + next_logup_spec_evals);
            builder.assign(&round, round + C::F::ONE);

            builder.cycle_tracker_end("derive next layer's expected sum");

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

/*
#[cfg(test)]
mod tests {
    use crate::arithmetics::UniPolyExtrapolator;
    use crate::tower_verifier::binding::IOPProverMessage;
    use crate::tower_verifier::binding::TowerVerifierInput;
    use crate::tower_verifier::program::iop_verifier_state_verify;
    use crate::tower_verifier::program::verify_tower_proof;
    use ceno_mle::mle::{DenseMultilinearExtension, IntoMLE, MultilinearExtension};
    use ceno_mle::virtual_poly::ArcMultilinearExtension;
    use ceno_mle::virtual_polys::VirtualPolynomials;
    use ceno_sumcheck::structs::IOPProverState;
    use ceno_transcript::BasicTranscript;
    use ceno_zkvm::scheme::constants::NUM_FANIN;
    use ceno_zkvm::scheme::utils::infer_tower_logup_witness;
    use ceno_zkvm::scheme::utils::infer_tower_product_witness;
    use ceno_zkvm::structs::TowerProver;
    use ff_ext::BabyBearExt4;
    use ff_ext::FieldFrom;
    use ff_ext::FromUniformBytes;
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
    use openvm_native_recursion::hints::Hintable;
    use openvm_stark_sdk::config::setup_tracing_with_log_level;
    use p3_baby_bear::BabyBear;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::Field;
    use p3_field::FieldAlgebra;
    use rand::thread_rng;

    type F = BabyBear;
    type E = BabyBearExt4;
    type EF = BinomialExtensionField<BabyBear, 4>;
    type C = AsmConfig<F, EF>;

    #[test]
    fn test_simple_sumcheck() {
        setup_tracing_with_log_level(tracing::Level::WARN);

        let nv = 5;
        let degree = 3;

        let mut builder = AsmBuilder::<F, EF>::default();

        let out_claim = EF::read(&mut builder);
        let prover_msgs = Vec::<IOPProverMessage>::read(&mut builder);

        let max_num_variables: Felt<F> = builder.constant(F::from_canonical_u32(nv as u32));
        let max_degree: Felt<F> = builder.constant(F::from_canonical_u32(degree as u32));

        let mut challenger: DuplexChallengerVariable<C> =
            DuplexChallengerVariable::new(&mut builder);

        let mut uni_p = UniPolyExtrapolator::new(&mut builder);

        builder.cycle_tracker_start("sumcheck verify");
        iop_verifier_state_verify(
            &mut builder,
            &mut challenger,
            &out_claim,
            &prover_msgs,
            max_num_variables,
            max_degree,
            &mut uni_p,
        );
        builder.cycle_tracker_end("sumcheck verify");

        builder.halt();

        // get the assembly code
        let options = CompilerOptions::default().with_cycle_tracker();
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

    #[test]
    fn test_prod_tower() {
        let nv = 5;
        let num_prod_specs = 2;
        let num_logup_specs = 1;
        let mut rng = thread_rng();

        setup_tracing_with_log_level(tracing::Level::WARN);

        let records: Vec<DenseMultilinearExtension<E>> = (0..num_prod_specs)
            .map(|_| {
                DenseMultilinearExtension::from_evaluations_ext_vec(
                    nv - 1,
                    E::random_vec(1 << (nv - 1), &mut rng),
                )
            })
            .collect_vec();
        let denom_records = (0..num_logup_specs)
            .map(|_| {
                DenseMultilinearExtension::from_evaluations_ext_vec(
                    nv,
                    E::random_vec(1 << nv, &mut rng),
                )
            })
            .collect_vec();

        let prod_specs = records
            .into_iter()
            .map(|record| {
                let (first, second) = record
                    .get_ext_field_vec()
                    .split_at(record.evaluations().len() / 2);
                let last_layer: Vec<ArcMultilinearExtension<E>> = vec![
                    first.to_vec().into_mle().into(),
                    second.to_vec().into_mle().into(),
                ];
                assert_eq!(last_layer.len(), NUM_FANIN);
                ceno_zkvm::structs::TowerProverSpec {
                    witness: infer_tower_product_witness(nv - 1, last_layer, NUM_FANIN),
                }
            })
            .collect_vec();

        let prod_out_evals = prod_specs
            .iter()
            .map(|spec| {
                spec.witness[0]
                    .iter()
                    .map(|mle| cast_vec(mle.get_ext_field_vec().to_vec())[0])
                    .collect_vec()
            })
            .collect_vec();

        let logup_specs = denom_records
            .into_iter()
            .map(|record| {
                let (first, second) = record
                    .get_ext_field_vec()
                    .split_at(record.evaluations().len() / 2);
                let last_layer: Vec<ArcMultilinearExtension<E>> = vec![
                    first.to_vec().into_mle().into(),
                    second.to_vec().into_mle().into(),
                ];
                ceno_zkvm::structs::TowerProverSpec {
                    witness: infer_tower_logup_witness(None, last_layer),
                }
            })
            .collect_vec();

        let logup_out_evals = logup_specs
            .iter()
            .map(|spec| {
                spec.witness[0]
                    .iter()
                    .map(|mle| cast_vec(mle.get_ext_field_vec().to_vec())[0])
                    .collect_vec()
            })
            .collect_vec();

        let num_variables = prod_specs
            .iter()
            .chain(logup_specs.iter())
            .map(|spec| spec.witness.len())
            .collect_vec();

        let mut transcript = BasicTranscript::new(&[]);
        let (_, tower_proof) =
            TowerProver::create_proof(prod_specs, logup_specs, NUM_FANIN, &mut transcript);

        // build program
        let mut builder = AsmBuilder::<F, EF>::default();

        let mut challenger: DuplexChallengerVariable<C> =
            DuplexChallengerVariable::new(&mut builder);

        // construct extrapolation weights
        let mut uni_p = UniPolyExtrapolator::new(&mut builder);

        assert_eq!(tower_proof.proofs.len(), nv - 1);
        let tower_verifier_input_var = TowerVerifierInput::read(&mut builder);
        let tower_verifier_input = TowerVerifierInput {
            prod_out_evals,
            logup_out_evals,
            num_variables,
            num_fanin: NUM_FANIN,
            num_proofs: nv - 1,
            num_prod_specs,
            num_logup_specs,
            _max_num_variables: nv,
            proofs: tower_proof
                .proofs
                .iter()
                .map(|layer| {
                    layer
                        .iter()
                        .map(|round| IOPProverMessage {
                            evaluations: cast_vec(round.evaluations.clone()),
                        })
                        .collect_vec()
                })
                .collect_vec(),
            prod_specs_eval: tower_proof
                .prod_specs_eval
                .iter()
                .map(|spec| {
                    spec.iter()
                        .map(|layer| cast_vec(layer.clone()))
                        .collect_vec()
                })
                .collect_vec(),
            logup_specs_eval: tower_proof
                .logup_specs_eval
                .iter()
                .map(|spec| {
                    spec.iter()
                        .map(|layer| cast_vec(layer.clone()))
                        .collect_vec()
                })
                .collect_vec(),
        };
        verify_tower_proof(
            &mut builder,
            &mut challenger,
            tower_verifier_input_var,
            &mut uni_p,
        );

        builder.halt();

        // prepare input
        let mut input_stream = Vec::new();
        input_stream.extend(tower_verifier_input.write());

        // get the assembly code
        let options = CompilerOptions::default().with_cycle_tracker();
        let program = builder.compile_isa_with_options(options);
        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100)
            .with_profiling();
        let config = NativeConfig::new(system_config, Native);
        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
        executor
            .execute_and_then(program, input_stream, |_, seg| Ok(seg), |err| err)
            .unwrap();
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
*/