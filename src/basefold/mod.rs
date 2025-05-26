pub mod binding;
use crate::tower_verifier::binding::PointVariable;
use binding::BasefoldProofVariable;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::duplex::DuplexChallengerVariable;
use ceno_zkvm::scheme::verifier::ZKVMVerifier;
use ff_ext::BabyBearExt4;
use mpcs::{Basefold, BasefoldRSParams};

type E = BabyBearExt4;
type Pcs = Basefold<E, BasefoldRSParams>;

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
    
    iter_zip!(builder, num_instances, points).for_each(|ptr_vec, builder| {
        let circuit_params = builder.iter_ptr_get(&num_instances, ptr_vec[0]);
        let point = builder.iter_ptr_get(&points, ptr_vec[1]);
        let circuit_num_var_f = builder.get(&circuit_params, 2);
        let circuit_num_var = Usize::from(builder.cast_felt_to_var(circuit_num_var_f.clone()));
        builder.assert_usize_eq(circuit_num_var, point.fs.len());
    });

    // let trivial_point_evals = builder.dyn_array(fixed_witin_opening_proof.circuit_trivial_metas.len());
    // let point_evals = builder.dyn_array(fixed_witin_opening_proof.circuit_metas.len());
}

// fn batch_verify(
//     vp: &Self::VerifierParam,
//     num_instances: &[(usize, usize)],
//     points: &[Point<E>],
//     fixed_comms: Option<&Self::Commitment>,
//     witin_comms: &Self::Commitment,
//     evals: &[Vec<E>],
//     proof: &Self::Proof,
//     circuit_num_polys: &[(usize, usize)],
//     transcript: &mut impl Transcript<E>,
// ) -> Result<(), Error> {
//     let mmcs = poseidon2_merkle_tree::<E>();

//     // preprocess data into respective group, in particularly, trivials vs non-trivials
//     let mut circuit_metas = vec![];
//     let mut circuit_trivial_metas = vec![];
//     let mut evals_iter = evals.iter().cloned();
//     let (trivial_point_evals, point_evals) = izip!(&circuit_num_vars, points).fold(
//         (vec![], vec![]),
//         |(mut trivial_point_evals, mut point_evals), ((circuit_index, num_var), point)| {
//             let (expected_witins_num_poly, expected_fixed_num_poly) =
//                 &circuit_num_polys[*circuit_index];
//             let mut circuit_meta = CircuitIndexMeta {
//                 witin_num_vars: *num_var,
//                 witin_num_polys: *expected_witins_num_poly,
//                 ..Default::default()
//             };
//             // NOTE: for evals, we concat witin with fixed to make process easier
//             if *num_var <= Spec::get_basecode_msg_size_log() {
//                 trivial_point_evals.push((
//                     point.clone(),
//                     evals_iter.next().unwrap()[0..*expected_witins_num_poly].to_vec(),
//                 ));
//                 if *expected_fixed_num_poly > 0 {
//                     circuit_meta.fixed_num_vars = *num_var;
//                     circuit_meta.fixed_num_polys = *expected_fixed_num_poly;
//                     trivial_point_evals.last_mut().unwrap().1.extend(
//                         evals_iter.next().unwrap()[0..*expected_fixed_num_poly].to_vec(),
//                     )
//                 }
//                 circuit_trivial_metas.push(circuit_meta);
//             } else {
//                 point_evals.push((
//                     point.clone(),
//                     evals_iter.next().unwrap()[0..*expected_witins_num_poly].to_vec(),
//                 ));
//                 if *expected_fixed_num_poly > 0 {
//                     circuit_meta.fixed_num_vars = *num_var;
//                     circuit_meta.fixed_num_polys = *expected_fixed_num_poly;
//                     point_evals.last_mut().unwrap().1.extend(
//                         evals_iter.next().unwrap()[0..*expected_fixed_num_poly].to_vec(),
//                     );
//                 }
//                 circuit_metas.push(circuit_meta);
//             }

//             (trivial_point_evals, point_evals)
//         },
//     );
//     assert!(evals_iter.next().is_none());

//     // check trivial proofs
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

//     if circuit_metas.is_empty() {
//         return Ok(());
//     } else {
//         assert!(
//             !proof.final_message.is_empty()
//                 && proof
//                     .final_message
//                     .iter()
//                     .map(|final_message| { final_message.len() })
//                     .chain(std::iter::once(1 << Spec::get_basecode_msg_size_log()))
//                     .all_equal(),
//             "final message size should be equal to 1 << Spec::get_basecode_msg_size_log()"
//         );
//         assert!(proof.sumcheck_proof.is_some(), "sumcheck proof must exist");
//         assert_eq!(proof.query_opening_proof.len(), Spec::get_number_queries())
//     }

//     // verify non trivial proof
//     let total_num_polys = circuit_metas
//         .iter()
//         .map(|circuit_meta| circuit_meta.witin_num_polys + circuit_meta.fixed_num_polys)
//         .sum();
//     let batch_coeffs =
//         &transcript.sample_and_append_challenge_pows(total_num_polys, b"batch coeffs");

//     let max_num_var = *circuit_num_vars.iter().map(|(_, n)| n).max().unwrap();
//     let num_rounds = max_num_var - Spec::get_basecode_msg_size_log();

//     // prepare folding challenges via sumcheck round msg + FRI commitment
//     let mut fold_challenges: Vec<E> = Vec::with_capacity(max_num_var);
//     let commits = &proof.commits;
//     let sumcheck_messages = proof.sumcheck_proof.as_ref().unwrap();
//     for i in 0..num_rounds {
//         transcript.append_field_element_exts(sumcheck_messages[i].evaluations.as_slice());
//         fold_challenges.push(
//             transcript
//                 .sample_and_append_challenge(b"commit round")
//                 .elements,
//         );
//         if i < num_rounds - 1 {
//             write_digest_to_transcript(&commits[i], transcript);
//         }
//     }
//     let final_message = &proof.final_message;
//     transcript.append_field_element_exts_iter(proof.final_message.iter().flatten());

//     let queries: Vec<_> = transcript.sample_bits_and_append_vec(
//         b"query indices",
//         Spec::get_number_queries(),
//         max_num_var + Spec::get_rate_log(),
//     );

//     // verify basefold sumcheck + FRI codeword query
//     batch_verifier_query_phase::<E, Spec>(
//         max_num_var,
//         &queries,
//         &vp.encoding_params,
//         final_message,
//         batch_coeffs,
//         &proof.query_opening_proof,
//         fixed_comms,
//         witin_comms,
//         &circuit_metas,
//         &proof.commits,
//         &fold_challenges,
//         sumcheck_messages,
//         &point_evals,
//     );

//     Ok(())
// }