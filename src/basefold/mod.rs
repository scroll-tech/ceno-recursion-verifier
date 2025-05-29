pub mod binding;
use crate::{arithmetics::{evaluate_at_point, gen_alpha_pows, join, max_usize_arr}, tower_verifier::binding::PointVariable, transcript::transcript_observe_label};
use binding::{BasefoldProofVariable, CircuitIndexMetaVariable, PointAndEvalsVariable};
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::{
    duplex::DuplexChallengerVariable, CanObserveVariable, CanSampleBitsVariable, FeltChallenger
};
use ceno_zkvm::scheme::verifier::ZKVMVerifier;
use ff_ext::BabyBearExt4;
use mpcs::{Basefold, BasefoldRSParams};

type E = BabyBearExt4;
type Pcs = Basefold<E, BasefoldRSParams>;

const BASECODE_MSG_SIZE: usize = 7;
const NUM_QUERIES: usize = 200;
const RATE_LOG: usize = 1;

pub fn basefold_batch_verify<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    num_instances: Array<C, Array<C, Felt<C::F>>>,
    rt_points: Vec<PointVariable<C>>,
    fixed_commit: Array<C, Felt<C::F>>,
    fixed_commit_log2_max_codeword_size: Felt<C::F>,
    fixed_commit_trivial_commits: Array<C, Array<C, Felt<C::F>>>,
    witin_commit: Array<C, Felt<C::F>>,
    witin_commit_log2_max_codeword_size: Felt<C::F>,
    witin_commit_trivial_commits: Array<C, Array<C, Felt<C::F>>>,
    evaluations: Vec<Array<C, Ext<C::F, C::EF>>>,
    circuit_num_polys: &Vec<(usize, usize)>,
    fixed_witin_opening_proof: BasefoldProofVariable<C>,
    cs: &ZKVMVerifier<E, Pcs>,
) {
    builder.assert_usize_eq(num_instances.len(), Usize::from(rt_points.len()));

    let points: Array<C, PointVariable<C>> = builder.dyn_array(rt_points.len());
    for (idx, pt) in rt_points.into_iter().enumerate() {
        builder.set(&points, idx, pt);
    }
    let evals: Array<C, Array<C, Ext<C::F, C::EF>>> = builder.dyn_array(evaluations.len());
    for (idx, es) in evaluations.into_iter().enumerate() {
        builder.set(&evals, idx, es);
    }
    
    let circuit_num_vars: Array<C, Usize<C::N>> = builder.dyn_array(num_instances.len());
    iter_zip!(builder, num_instances, points, circuit_num_vars).for_each(|ptr_vec, builder| {
        let circuit_params = builder.iter_ptr_get(&num_instances, ptr_vec[0]);
        let point = builder.iter_ptr_get(&points, ptr_vec[1]);
        let circuit_num_var_f = builder.get(&circuit_params, 2);
        let circuit_num_var = Usize::from(builder.cast_felt_to_var(circuit_num_var_f.clone()));
        builder.iter_ptr_set(&circuit_num_vars, ptr_vec[2], circuit_num_var.clone());
        builder.assert_usize_eq(circuit_num_var, point.fs.len());
    });

    let trivial_point_evals: Array<C, PointAndEvalsVariable<C>> = builder.dyn_array(fixed_witin_opening_proof.trivial_metas_count.clone());
    let point_evals: Array<C, PointAndEvalsVariable<C>> = builder.dyn_array(fixed_witin_opening_proof.metas_count.clone());

    let trivial_idx: Usize<C::N> = Usize::from(0);
    let sumcheck_idx: Usize<C::N> = Usize::from(0);
    let evals_idx: Usize<C::N> = Usize::from(0);

    builder.range(0, fixed_witin_opening_proof.circuit_metas.len()).for_each(|idx_vec, builder| {
        let metas = builder.get(&fixed_witin_opening_proof.circuit_metas, idx_vec[0]);

        let point = builder.get(&points, idx_vec[0]);
        let es = builder.get(&evals, evals_idx.clone());
        builder.assign(&evals_idx, evals_idx.clone() + Usize::from(1));
        let es_slice = es.slice(builder, 0, metas.witin_num_polys.clone());

        let fixed_es_slice: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(metas.fixed_num_polys.clone());
        builder.if_ne(metas.fixed_num_polys.clone(), Usize::from(0)).then(|builder| {
            let next_es = builder.get(&evals, evals_idx.clone());
            builder.assign(&evals_idx, evals_idx.clone() + Usize::from(1));
            builder.range(0, metas.fixed_num_polys.clone()).for_each(|fixed_idx_vec, builder| {
                let e = builder.get(&next_es, fixed_idx_vec[0]);
                builder.set(&fixed_es_slice, fixed_idx_vec[0], e);
            });
        });

        let es = join(builder, &es_slice, &fixed_es_slice);

        builder.if_eq(metas.is_trivial.clone(), Usize::from(1)).then(|builder| {
            builder.set(&trivial_point_evals, trivial_idx.clone(), PointAndEvalsVariable {
                point: point.clone(),
                evals: es.clone(),
            });
            builder.assign(&trivial_idx, trivial_idx.clone() + Usize::from(1));
        });
        builder.if_ne(metas.is_trivial, Usize::from(1)).then(|builder| {
            builder.set(&point_evals, sumcheck_idx.clone(), PointAndEvalsVariable {
                point: point.clone(),
                evals: es.clone(),
            });
            builder.assign(&sumcheck_idx, sumcheck_idx.clone() + Usize::from(1));
        });
    });

    builder.if_ne(fixed_witin_opening_proof.metas_count.clone(), Usize::from(0)).then(|builder| {
        builder.range(0, fixed_witin_opening_proof.final_message.len()).for_each(|idx_vec, builder| {
            let msg = builder.get(&fixed_witin_opening_proof.final_message, idx_vec[0]);
            builder.assert_usize_eq(msg.len(), Usize::from(BASECODE_MSG_SIZE));
        });
        builder.assert_usize_eq(fixed_witin_opening_proof.query_opening_proofs.len(), Usize::from(NUM_QUERIES));
    });

    // check trivial proofs
    builder.if_ne(fixed_witin_opening_proof.trivial_metas_count.clone(), Usize::from(0)).then(|builder| {
        builder.assert_usize_eq(fixed_witin_opening_proof.trivial_metas_count.clone(), fixed_witin_opening_proof.trivial_proof.matrices.len());
        builder.assert_usize_eq(fixed_witin_opening_proof.trivial_proof.matrices.len(), fixed_commit_trivial_commits.len());

        // 1. check mmcs verify opening
        // 2. check mle.evaluate(point) == evals
        let trivial_idx: Usize<C::N> = Usize::from(0);
        let circuit_trivial_metas: Array<C, CircuitIndexMetaVariable<C>> = builder.dyn_array(fixed_witin_opening_proof.trivial_metas_count.clone());
        iter_zip!(builder, fixed_witin_opening_proof.circuit_metas).for_each(|ptr_vec, builder| {
            let metas = builder.iter_ptr_get(&fixed_witin_opening_proof.circuit_metas, ptr_vec[0]);
            builder.if_eq(metas.is_trivial.clone(), Usize::from(1)).then(|builder| {
                builder.set(&circuit_trivial_metas, trivial_idx.clone(), metas.clone());
                builder.assign(&trivial_idx, trivial_idx.clone() + Usize::from(1));
            });
        });

        iter_zip!(
            builder, 
            circuit_trivial_metas, 
            fixed_witin_opening_proof.trivial_proof.matrices, 
            trivial_point_evals, 
            witin_commit_trivial_commits
        ).for_each(|ptr_vec, builder| {
            let metas = builder.iter_ptr_get(&circuit_trivial_metas, ptr_vec[0]);
            let proof = builder.iter_ptr_get(&fixed_witin_opening_proof.trivial_proof.matrices, ptr_vec[1]);
            let point_and_evals = builder.iter_ptr_get(&trivial_point_evals, ptr_vec[2]);
            let point = point_and_evals.point;
            let witin_fixed_evals = point_and_evals.evals;
            let witin_commit = builder.iter_ptr_get(&witin_commit_trivial_commits, ptr_vec[3]);

            let witin_rmm = builder.get(&proof, 0);

            let rows = witin_rmm.values.len();
            let cols = builder.get(&witin_rmm.values, 0).len();

            let mles: Array<C, Array<C, Ext<C::F, C::EF>>> = builder.dyn_array(cols.clone());
            builder.range(0, cols.clone()).for_each(|col_idx_vec, builder| {
                let values: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(rows.clone());
                builder.range(0, rows.clone()).for_each(|row_idx_vec, builder| {
                    let row = builder.get(&witin_rmm.values, row_idx_vec[0]);
                    let f = builder.get(&row, col_idx_vec[0]);
                    let e = builder.felts2ext(&[f]);
                    builder.set(&values, row_idx_vec[0], e);
                });
                builder.set(&mles, col_idx_vec[0], values);
            });

            let witin_evals_slice = witin_fixed_evals.slice(builder, 0, mles.len());
            iter_zip!(builder, mles, witin_evals_slice).for_each(|ptr_vec, builder| {
                let mle = builder.iter_ptr_get(&mles, ptr_vec[0]);
                let eval = builder.iter_ptr_get(&witin_evals_slice, ptr_vec[1]);

                let expected = evaluate_at_point(builder, &mle, &point.fs);
                builder.assert_ext_eq(expected, eval);
            });

            builder.if_ne(metas.fixed_num_polys.clone(), Usize::from(0)).then(|builder| {
                let fixed_rmm = builder.get(&proof, 1);

                let rows = fixed_rmm.values.len();
                let cols = builder.get(&fixed_rmm.values, 0).len();

                let fixed_mles: Array<C, Array<C, Ext<C::F, C::EF>>> = builder.dyn_array(cols.clone());
                builder.range(0, cols.clone()).for_each(|col_idx_vec, builder| {
                    let values: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(rows.clone());
                    builder.range(0, rows.clone()).for_each(|row_idx_vec, builder| {
                        let row = builder.get(&fixed_rmm.values, row_idx_vec[0]);
                        let f = builder.get(&row, col_idx_vec[0]);
                        let e = builder.felts2ext(&[f]);
                        builder.set(&values, row_idx_vec[0], e);
                    });
                    builder.set(&fixed_mles, col_idx_vec[0], values);
                });

                let witin_evals_slice = witin_fixed_evals.slice(builder, mles.len(), witin_fixed_evals.len());
                iter_zip!(builder, fixed_mles, witin_evals_slice).for_each(|ptr_vec, builder| {
                    let mle = builder.iter_ptr_get(&mles, ptr_vec[0]);
                    let eval = builder.iter_ptr_get(&witin_evals_slice, ptr_vec[1]);

                    let expected = evaluate_at_point(builder, &mle, &point.fs);
                    builder.assert_ext_eq(expected, eval);
                });
            });
        });
    });

    // verify non trivial proof
    let total_num_polys: Usize<C::N> = Usize::from(0);
    builder.range(0, fixed_witin_opening_proof.circuit_metas.len()).for_each(|idx_vec, builder| {
        let metas = builder.get(&fixed_witin_opening_proof.circuit_metas, idx_vec[0]);
        builder.assign(&total_num_polys, total_num_polys.clone() + metas.witin_num_polys + metas.fixed_num_polys);
    });
    transcript_observe_label(builder, challenger, b"batch coeffs");
    let batch_coeffs = gen_alpha_pows(builder, challenger, total_num_polys);

    let max_num_var = max_usize_arr(builder, &circuit_num_vars);
    let num_rounds_minus_one: Usize<C::N> = builder.eval(max_num_var.clone() - Usize::from(BASECODE_MSG_SIZE + 1));

    let fold_challenges: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(max_num_var.clone());
    builder.range(0, num_rounds_minus_one.clone()).for_each(|idx_vec, builder| {
        let sumcheck_msg = builder.get(&fixed_witin_opening_proof.sumcheck_proof, idx_vec[0]).evaluations;
        builder.range(0, sumcheck_msg.len()).for_each(|msg_idx_vec, builder| {
            let e = builder.get(&sumcheck_msg, msg_idx_vec[0]);
            let e_felts = builder.ext2felt(e);
            challenger.observe_slice(builder, e_felts);
        });

        let c = challenger.sample_ext(builder);
        builder.set(&fold_challenges, idx_vec[0], c);

        let commit = builder.get(&fixed_witin_opening_proof.commits, idx_vec[0]).value;
        builder.range(0, commit.len()).for_each(|cmt_idx_vec, builder| {
            let f = builder.get(&commit, cmt_idx_vec[0]);
            challenger.observe(builder, f);
        });
    });

    let sumcheck_msg = builder.get(&fixed_witin_opening_proof.sumcheck_proof, num_rounds_minus_one.clone()).evaluations;
    builder.range(0, sumcheck_msg.len()).for_each(|msg_idx_vec, builder| {
        let e = builder.get(&sumcheck_msg, msg_idx_vec[0]);
        let e_felts = builder.ext2felt(e);
        challenger.observe_slice(builder, e_felts);
    });

    let c = challenger.sample_ext(builder);
    builder.set(&fold_challenges, num_rounds_minus_one, c);

    builder.range(0, fixed_witin_opening_proof.final_message.len()).for_each(|idx_vec, builder| {
        let msg = builder.get(&fixed_witin_opening_proof.final_message, idx_vec[0]);

        iter_zip!(builder, msg).for_each(|ptr_vec, builder| {
            let e = builder.iter_ptr_get(&msg, ptr_vec[0]);
            let e_felts = builder.ext2felt(e);
            challenger.observe_slice(builder, e_felts);
        });
    });

    transcript_observe_label(builder, challenger, b"query indices");
    let queries: Array<C, Array<C, Var<C::N>>> = builder.dyn_array(NUM_QUERIES);
    let n_bits: RVar<C::N> = builder.eval_expr(max_num_var.clone() + Usize::from(RATE_LOG));
    builder.range(0, queries.len()).for_each(|idx_vec, builder| {
        let c = challenger.sample_bits(builder, n_bits);
        builder.set(&queries, idx_vec[0], c);
    });

    /*
    // verify basefold sumcheck + FRI codeword query
    batch_verifier_query_phase::<E, Spec>(
        max_num_var,
        &queries,
        &vp.encoding_params,
        final_message,
        batch_coeffs,
        &proof.query_opening_proof,
        fixed_comms,
        witin_comms,
        &circuit_metas,
        &proof.commits,
        &fold_challenges,
        sumcheck_messages,
        &point_evals,
    );

    Ok(())
    */
}