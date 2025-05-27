pub mod binding;
use crate::{arithmetics::{gen_alpha_pows, join, max_usize_arr}, tower_verifier::binding::PointVariable, transcript::transcript_observe_label};
use binding::{BasefoldProofVariable, PointAndEvalsVariable};
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
    witin_commit: Array<C, Felt<C::F>>,
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

//     let mmcs = poseidon2_merkle_tree::<E>();
//     
//     if !circuit_trivial_metas.is_empty() {
//         let mut trivial_fixed_commit = fixed_comms
//             .as_ref()
//             .map(|fc| fc.trivial_commits.iter().cloned())
//             .unwrap_or_default();
//         assert!(proof.trivial_proof.is_some());
//         assert!(
//             [
//                 circuit_trivial_metas.len(),
//                 proof.trivial_proof.as_ref().unwrap().len(),
//                 witin_comms.trivial_commits.len()
//             ]
//             .iter()
//             .all_equal()
//         );

//         // 1. check mmcs verify opening
//         // 2. check mle.evaluate(point) == evals
//         circuit_trivial_metas
//             .iter()
//             .zip_eq(proof.trivial_proof.as_ref().unwrap())
//             .zip_eq(&trivial_point_evals)
//             .zip_eq(&witin_comms.trivial_commits)
//             .try_for_each(
//                 |(
//                     (
//                         (
//                             CircuitIndexMeta {
//                                 fixed_num_polys, ..
//                             },
//                             proof,
//                         ),
//                         (point, witin_fixed_evals),
//                     ),
//                     witin_commit,
//                 )| {
//                     let witin_rmm = proof[0].clone();
//                     let (commit, _) = mmcs.commit_matrix(witin_rmm.clone());
//                     if commit != *witin_commit {
//                         Err(Error::MerkleRootMismatch)?;
//                     }
//                     let mut mles = RowMajorMatrix::new_by_inner_matrix(
//                         witin_rmm,
//                         InstancePaddingStrategy::Default,
//                     )
//                     .to_mles();

//                     if *fixed_num_polys > 0 {
//                         let fixed_rmm = proof[1].clone();
//                         let fixed_commit =
//                             trivial_fixed_commit.next().expect("proof must exist");
//                         // NOTE rmm clone here is ok since trivial proof is relatively small
//                         let (commit, _) = mmcs.commit_matrix(fixed_rmm.clone());
//                         if commit != fixed_commit {
//                             Err(Error::MerkleRootMismatch)?;
//                         }
//                         mles.extend(
//                             RowMajorMatrix::new_by_inner_matrix(
//                                 fixed_rmm,
//                                 InstancePaddingStrategy::Default,
//                             )
//                             .to_mles(),
//                         );
//                     }

//                     mles.iter()
//                         .zip_eq(witin_fixed_evals)
//                         .all(|(mle, eval)| mle.evaluate(point) == *eval)
//                         .then_some(())
//                         .ok_or_else(|| {
//                             Error::PointEvalMismatch("trivial point eval mismatch".to_string())
//                         })
//                 },
//             )?;
//     }

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