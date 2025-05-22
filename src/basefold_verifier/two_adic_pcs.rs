use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_stark_backend::{
    p3_commit::{LagrangeSelectors, TwoAdicMultiplicativeCoset},
    p3_field::{Field, FieldAlgebra, FieldExtensionAlgebra, TwoAdicField},
};
use p3_symmetric::Hash;

use super::{
    commit::{PcsVariable, PolynomialSpaceVariable},
    types::{
        BasefoldConfigVariable, BasefoldProofVariable, DimensionsVariable, TwoAdicPcsMatsVariable,
        TwoAdicPcsRoundVariable,
    },
    verify_batch, verify_query, NestedOpenedValues, TwoAdicMultiplicativeCosetVariable,
};
use openvm_native_recursion::{challenger::ChallengerVariable, digest::DigestVariable};

// The maximum two-adicity of Felt `C::F`. This means `C::F` does not have a multiplicative subgroup
// of order 2^{MAX_TWO_ADICITY + 1}. Currently set to 27 for BabyBear.
pub const MAX_TWO_ADICITY: usize = 27;

/// TODO: Modify this function to replace FRI by BaseFold verifier
/// Note: Change as few code as possible. For this purpose:
/// - Try not to touch most of the existing codes in `verify_two_adic_pcs`.
///

/// Notes:
/// 1. FieldMerkleTreeMMCS sorts traces by height in descending order when committing data.
/// 2. **Required** that `C::F` has two-adicity <= [MAX_TWO_ADICITY]. In particular this implies that all LDE matrices have
///    `log2(lde_height) <= MAX_TWO_ADICITY`.
/// 3. **Required** that the maximum trace height is `2^log_max_height - 1`.
///
/// Reference:
/// <https://github.com/Plonky3/Plonky3/blob/27b3127dab047e07145c38143379edec2960b3e1/merkle-tree/src/merkle_tree.rs#L53>
/// So traces are sorted in `opening_proof`.
///
/// 2. FieldMerkleTreeMMCS::poseidon2 keeps the raw values in the original order. So traces are not sorted in `opened_values`.
///
/// Reference:
/// <https://github.com/Plonky3/Plonky3/blob/27b3127dab047e07145c38143379edec2960b3e1/merkle-tree/src/mmcs.rs#L87>
/// <https://github.com/Plonky3/Plonky3/blob/27b3127dab047e07145c38143379edec2960b3e1/merkle-tree/src/merkle_tree.rs#L100>
/// <https://github.com/Plonky3/Plonky3/blob/784b7dd1fa87c1202e63350cc8182d7c5327a7af/fri/src/verifier.rs#L22>
pub fn verify_two_adic_pcs<C: Config>(
    builder: &mut Builder<C>,
    config: &BasefoldConfigVariable<C>,
    rounds: Array<C, TwoAdicPcsRoundVariable<C>>,
    proof: BasefoldProofVariable<C>,
    log_max_height: RVar<C::N>,
    challenger: &mut impl ChallengerVariable<C>,
) where
    C::F: TwoAdicField,
    C::EF: TwoAdicField,
{
    // Currently do not support other final poly len (i.e., do not support early stopping)
    builder.assert_var_eq(RVar::from(config.log_final_poly_len), RVar::zero());
    // The `proof.final_poly` length is in general `2^{log_final_poly_len + log_blowup}`.
    // We require `log_final_poly_len = 0`, so `proof.final_poly` has length `2^log_blowup`.
    // In fact, the FRI low-degree test requires that `proof.final_poly = [constant, 0, ..., 0]`.
    builder.assert_usize_eq(proof.final_poly.len(), RVar::from(config.blowup));
    // Constant term of final poly
    let final_poly_ct = builder.get(&proof.final_poly, 0);
    // TODO: why sending these zero entries in the first place?
    for i in 1..config.blowup {
        let term = builder.get(&proof.final_poly, i);
        builder.assert_ext_eq(term, C::EF::ZERO.cons());
    }

    let g = builder.generator();

    // Write the statements to prove to the transcript. More precisely,
    // for every round, write every opened value in every matrix to the transcript.
    let log_blowup = config.log_blowup;
    iter_zip!(builder, rounds).for_each(|ptr_vec, builder| {
        let round = builder.iter_ptr_get(&rounds, ptr_vec[0]);
        iter_zip!(builder, round.mats).for_each(|ptr_vec, builder| {
            let mat = builder.iter_ptr_get(&round.mats, ptr_vec[0]);
            iter_zip!(builder, mat.values).for_each(|ptr_vec, builder| {
                let value = builder.iter_ptr_get(&mat.values, ptr_vec[0]);
                iter_zip!(builder, value).for_each(|ptr_vec, builder| {
                    if builder.flags.static_only {
                        let ext = builder.iter_ptr_get(&value, ptr_vec[0]);
                        let arr = builder.ext2felt(ext);
                        challenger.observe_slice(builder, arr);
                    } else {
                        let ptr = ptr_vec[0];
                        for i in 0..C::EF::D {
                            let f: Felt<_> = builder.uninit();
                            builder.load(
                                f,
                                Ptr {
                                    address: ptr.variable(),
                                },
                                MemIndex {
                                    index: RVar::from(i),
                                    offset: 0,
                                    size: 1,
                                },
                            );
                            challenger.observe(builder, f);
                        }
                    }
                });
            });
        });
    });
    // TODO: should send the initial sumcheck message before the first squeeze
    let alpha = challenger.sample_ext(builder);
    if builder.flags.static_only {
        builder.ext_reduce_circuit(alpha);
    }

    builder.cycle_tracker_start("stage-d-verifier-verify");
    // **ATTENTION**: always check shape of user inputs.
    builder.assert_usize_eq(proof.query_proofs.len(), RVar::from(config.num_queries));
    builder.assert_usize_eq(proof.commit_phase_commits.len(), log_max_height);
    builder.assert_usize_eq(proof.commit_phase_sumcheck_messages.len(), log_max_height);
    let betas: Array<C, Ext<C::F, C::EF>> = builder.array(log_max_height);

    // Write the commit phase commitments to the challenger.
    iter_zip!(
        builder,
        proof.commit_phase_commits,
        proof.commit_phase_sumcheck_messages,
        betas
    )
    .for_each(|ptr_vec, builder| {
        let comm_ptr = ptr_vec[0];
        let sumcheck_ptr = ptr_vec[1];
        let beta_ptr = ptr_vec[2];

        // Write commitment to transcript
        let comm = builder.iter_ptr_get(&proof.commit_phase_commits, comm_ptr);
        challenger.observe_digest(builder, comm);

        // Write the next round sumcheck message to transcript
        let sumcheck_message =
            builder.iter_ptr_get(&proof.commit_phase_sumcheck_messages, sumcheck_ptr);
        challenger.observe_slice(builder, sumcheck_message);

        // Squeeze the next challenge
        let sample = challenger.sample_ext(builder);
        builder.iter_ptr_set(&betas, beta_ptr, sample);
    });

    // Write the final polynomial to the challenger
    iter_zip!(builder, proof.final_poly).for_each(|ptr_vec, builder| {
        let final_poly_elem = builder.iter_ptr_get(&proof.final_poly, ptr_vec[0]);
        let final_poly_elem_felts = builder.ext2felt(final_poly_elem);
        challenger.observe_slice(builder, final_poly_elem_felts);
    });

    challenger.check_witness(builder, config.proof_of_work_bits, proof.pow_witness);

    let log_max_lde_height = builder.eval_expr(log_max_height + RVar::from(log_blowup));
    // tag_exp is a shared buffer.
    let tag_exp: Array<C, Felt<C::F>> = builder.array(log_max_lde_height);
    let w = config.get_two_adic_generator(builder, log_max_lde_height);
    let max_gen_pow = config.get_two_adic_generator(builder, 1);
    let one_var: Felt<C::F> = builder.eval(C::F::ONE);

    builder.cycle_tracker_start("pre-compute-rounds-context");
    // Round context: some assistant data needed for verifying consistency in each
    // round, including powers of alpha, permuted matrix dimensions, etc.
    let rounds_context = compute_rounds_context(builder, &rounds, log_blowup, alpha);
    // Only used in static mode.
    // Prepare vector (1, alpha, alpha^2, ..., alpha^max_width)
    let alpha_pows = if builder.flags.static_only {
        let max_width = get_max_matrix_width(builder, &rounds);
        let mut ret = Vec::with_capacity(max_width + 1);
        ret.push(C::EF::ONE.cons());
        for i in 1..=max_width {
            let curr = builder.eval(ret[i - 1].clone() * alpha);
            builder.ext_reduce_circuit(curr);
            ret.push(curr.into());
        }
        ret
    } else {
        vec![]
    };
    builder.cycle_tracker_end("pre-compute-rounds-context");

    // Accumulators of the reduced opening sums, reset per query. The array `ro` is indexed by log_height.
    let ro: Array<C, Ext<C::F, C::EF>> = builder.array(MAX_TWO_ADICITY + 1);
    let alpha_pow: Array<C, Ext<C::F, C::EF>> = builder.array(MAX_TWO_ADICITY + 1);

    // TODO: Check the correctness of the sum-check messages.
    // Compute the new sum for each round, then check the final value is equal to final_poly_ct.
    // Following is the native verifier code for this step:
    // 1. check initial claim match with first round sumcheck value
    // assert_eq!(
    //     // we need to scale up with scalar for witin_num_vars < max_num_var
    //     dot_product::<E, _, _>(
    //         batch_coeffs.iter().copied(),
    //         point_evals.iter().zip_eq(circuit_meta.iter()).flat_map(
    //             |((_, evals), CircuitIndexMeta { witin_num_vars, .. })| {
    //                 evals.iter().copied().map(move |eval| {
    //                     eval * E::from_u64(1 << (max_num_var - witin_num_vars) as u64)
    //                 })
    //             }
    //         )
    //     ),
    //     { sumcheck_messages[0].evaluations[0] + sumcheck_messages[0].evaluations[1] }
    // );
    // // 2. check every round of sumcheck match with prev claims
    // for i in 0..fold_challenges.len() - 1 {
    //     assert_eq!(
    //         interpolate_uni_poly(&sumcheck_messages[i].evaluations, fold_challenges[i]),
    //         { sumcheck_messages[i + 1].evaluations[0] + sumcheck_messages[i + 1].evaluations[1] }
    //     );
    // }
    // // 3. check final evaluation are correct
    // assert_eq!(
    //     interpolate_uni_poly(
    //         &sumcheck_messages[fold_challenges.len() - 1].evaluations,
    //         fold_challenges[fold_challenges.len() - 1]
    //     ),
    //     izip!(final_message, point_evals.iter().map(|(point, _)| point))
    //         .map(|(final_message, point)| {
    //             // coeff is the eq polynomial evaluated at the first challenge.len() variables
    //             let num_vars_evaluated = point.len()
    //                 - <Spec::EncodingScheme as EncodingScheme<E>>::get_basecode_msg_size_log();
    //             let coeff = eq_eval(
    //                 &point[..num_vars_evaluated],
    //                 &fold_challenges[fold_challenges.len() - num_vars_evaluated..],
    //             );
    //             // Compute eq as the partially evaluated eq polynomial
    //             let eq = build_eq_x_r_vec(&point[num_vars_evaluated..]);
    //             dot_product(
    //                 final_message.iter().copied(),
    //                 eq.into_iter().map(|e| e * coeff),
    //             )
    //         })
    //         .sum()
    // );

    // Finally, check the correctness of each query
    iter_zip!(builder, proof.query_proofs).for_each(|ptr_vec, builder| {
        let query_proof = builder.iter_ptr_get(&proof.query_proofs, ptr_vec[0]);
        let index_bits = challenger.sample_bits(builder, log_max_lde_height);

        // We reset the reduced opening accumulators at the start of each query.
        // We describe what `ro[log_height]` computes per query in pseduo-code, where `log_height` is log2 of the size of the LDE domain:
        // ro[log_height] = 0
        // alpha_pow[log_height] = 1
        // for round in rounds:
        //   for mat in round.mats where (mat.domain.log_n + log_blowup == log_height): // preserving order of round.mats
        //      // g is generator of F
        //      // w_{log_height} is generator of subgroup of F of order 2^log_height
        //      x = g * w_{log_height}^{reverse_bits(index >> (log_max_height - log_height), log_height)}
        //      // reverse_bits(x, bits) takes an unsigned integer x with `bits` bits and returns the unsigned integer with the bits of x reversed.
        //      // x is a rotated evaluation point in a coset of the LDE domain.
        //      ps_at_x = [claimed evaluation of p at x for each polynomial p corresponding to column of mat]
        //      // ps_at_x is array of Felt
        //      for (z, ps_at_z) in zip(mat.points, mat.values):
        //        // z is an out of domain point in Ext. There may be multiple per round to account for rotations in AIR constraints.
        //        // ps_at_z is array of Ext for [claimed evaluation of p at z for each polyomial p corresponding to column of mat]
        //        for (p_at_x, p_at_z) in zip(ps_at_x, ps_at_z):
        //          ro[log_height] += alpha_pow[log_height] * (p_at_x - p_at_z) / (x - z)
        //          alpha_pow[log_height] *= alpha
        //
        // The final value of ro[log_height] is the reduced opening value for log_height.
        if builder.flags.static_only {
            for j in 0..=MAX_TWO_ADICITY {
                // ATTENTION: don't use set_value here, Fixed will share the same variable.
                builder.set(&ro, j, C::EF::ZERO.cons());
                builder.set(&alpha_pow, j, C::EF::ONE.cons());
            }
        } else {
            let zero_ef = builder.eval(C::EF::ZERO.cons());
            let one_ef = builder.eval(C::EF::ONE.cons());
            for j in 0..=MAX_TWO_ADICITY {
                // Use set_value here to save a copy.
                builder.set_value(&ro, j, zero_ef);
                builder.set_value(&alpha_pow, j, one_ef);
            }
        }
        // **ATTENTION**: always check shape of user inputs.
        builder.assert_usize_eq(query_proof.input_proof.len(), rounds.len());

        // Pre-compute tag_exp
        builder.cycle_tracker_start("cache-generator-powers");
        {
            // truncate index_bits to log_max_height
            let index_bits_truncated = index_bits.slice(builder, 0, log_max_lde_height);

            // b = index_bits
            // w = generator of order 2^log_max_height
            // we first compute `w ** (b[0] * 2^(log_max_height - 1) + ... + b[log_max_height - 1])` using a square-and-multiply algorithm.
            let res = builder.exp_bits_big_endian(w, &index_bits_truncated);

            // we now compute:
            // tag_exp[log_max_height - i] = g * w ** (b[log_max_height - i] * 2^(log_max_height - 1) + ... + b[log_max_height - 1] * 2^(log_max_height - i))
            // using a square-and-divide algorithm.
            // g * res is tag_exp[0]
            // `tag_exp` is used below as a rotated evaluation point in a coset of the LDE domain.
            iter_zip!(builder, index_bits_truncated, tag_exp).for_each(|ptr_vec, builder| {
                builder.iter_ptr_set(&tag_exp, ptr_vec[1], g * res);

                let bit = builder.iter_ptr_get(&index_bits_truncated, ptr_vec[0]);
                let div = builder.select_f(bit, max_gen_pow, one_var);
                builder.assign(&res, res / div);
                builder.assign(&res, res * res);
            });
        };
        builder.cycle_tracker_end("cache-generator-powers");

        iter_zip!(builder, query_proof.input_proof, rounds, rounds_context).for_each(
            |ptr_vec, builder| {
                let batch_opening = builder.iter_ptr_get(&query_proof.input_proof, ptr_vec[0]);
                let round = builder.iter_ptr_get(&rounds, ptr_vec[1]);
                let round_context = builder.iter_ptr_get(&rounds_context, ptr_vec[2]);

                let batch_commit = round.batch_commit;
                let mats = round.mats;
                let RoundContext {
                    ov_ptrs,
                    perm_ov_ptrs,
                    batch_dims,
                    mat_alpha_pows,
                    log_batch_max_height,
                } = round_context;

                // **ATTENTION**: always check shape of user inputs.
                builder.assert_usize_eq(ov_ptrs.len(), mats.len());

                let hint_id = batch_opening.opened_values.id.clone();
                // For static to track the offset in the hint space.
                let mut hint_offset = 0;
                builder.cycle_tracker_start("compute-reduced-opening");
                iter_zip!(builder, ov_ptrs, mats, mat_alpha_pows).for_each(|ptr_vec, builder| {
                    let mat_opening = builder.iter_ptr_get(&ov_ptrs, ptr_vec[0]);
                    let mat = builder.iter_ptr_get(&mats, ptr_vec[1]);
                    let mat_alpha_pow = if builder.flags.static_only {
                        builder.uninit()
                    } else {
                        builder.iter_ptr_get(&mat_alpha_pows, ptr_vec[2])
                    };
                    let mat_points = mat.points;
                    let mat_values = mat.values;
                    let log2_domain_size = mat.domain.log_n;
                    let log_height = builder.eval_expr(log2_domain_size + RVar::from(log_blowup));

                    let cur_ro = builder.get(&ro, log_height);
                    let cur_alpha_pow = builder.get(&alpha_pow, log_height);

                    builder.cycle_tracker_start("exp-reverse-bits-len");
                    let height_idx = builder.eval_expr(log_max_lde_height - log_height);
                    let x = builder.get(&tag_exp, height_idx);
                    builder.cycle_tracker_end("exp-reverse-bits-len");

                    let is_init: Usize<C::N> = builder.eval(C::N::ZERO);
                    iter_zip!(builder, mat_points, mat_values).for_each(|ptr_vec, builder| {
                        let z: Ext<C::F, C::EF> = builder.iter_ptr_get(&mat_points, ptr_vec[0]);
                        let ps_at_z = builder.iter_ptr_get(&mat_values, ptr_vec[1]);

                        builder.cycle_tracker_start("single-reduced-opening-eval");

                        if builder.flags.static_only {
                            let n: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
                            let width = ps_at_z.len().value();
                            if is_init.value() == 0 {
                                let mat_opening_vals = {
                                    let witness_refs = builder.get_witness_refs(hint_id.clone());
                                    let start = hint_offset;
                                    witness_refs[start..start + width].to_vec()
                                };
                                for (i, v) in mat_opening_vals.into_iter().enumerate() {
                                    builder.set_value(&mat_opening, i, v.into());
                                }
                            }
                            for (t, alpha_pow) in alpha_pows.iter().take(width).enumerate() {
                                let p_at_x = builder.get(&mat_opening, t);
                                let p_at_z = builder.get(&ps_at_z, t);
                                builder.assign(&n, n + (p_at_z - p_at_x) * alpha_pow.clone());
                            }
                            builder.assign(&cur_ro, cur_ro + n / (z - x) * cur_alpha_pow);
                            builder
                                .assign(&cur_alpha_pow, cur_alpha_pow * alpha_pows[width].clone());
                        } else {
                            let mat_ro = builder.fri_single_reduced_opening_eval(
                                alpha,
                                hint_id.get_var(),
                                is_init.get_var(),
                                &mat_opening,
                                &ps_at_z,
                            );
                            builder.assign(&cur_ro, cur_ro + (mat_ro * cur_alpha_pow / (z - x)));
                            builder.assign(&cur_alpha_pow, cur_alpha_pow * mat_alpha_pow);
                        }
                        // The buffer `mat_opening` has now been written to, so we set `is_init` to 1.
                        builder.assign(&is_init, C::N::ONE);
                        builder.cycle_tracker_end("single-reduced-opening-eval");
                    });
                    if builder.flags.static_only {
                        hint_offset += mat_opening.len().value();
                    }
                    builder.set_value(&ro, log_height, cur_ro);
                    builder.set_value(&alpha_pow, log_height, cur_alpha_pow);
                });
                builder.cycle_tracker_end("compute-reduced-opening");

                let bits_reduced: Usize<_> =
                    builder.eval(log_max_lde_height - log_batch_max_height);
                let index_bits_shifted_v1 = index_bits.shift(builder, bits_reduced);

                builder.cycle_tracker_start("verify-batch");
                verify_batch::<C>(
                    builder,
                    &batch_commit,
                    batch_dims,
                    index_bits_shifted_v1,
                    &NestedOpenedValues::Felt(perm_ov_ptrs),
                    &batch_opening.opening_proof,
                );
                builder.cycle_tracker_end("verify-batch");
            },
        );

        let folded_eval = verify_query(
            builder,
            config,
            &proof.commit_phase_commits,
            &index_bits,
            &query_proof,
            &betas,
            &ro,
            log_max_lde_height,
        );

        builder.assert_ext_eq(folded_eval, final_poly_ct);
    });
    builder.cycle_tracker_end("stage-d-verifier-verify");
}

impl<C: Config> FromConstant<C> for TwoAdicPcsRoundVariable<C>
where
    C::F: TwoAdicField,
{
    type Constant = (
        Hash<C::F, C::F, DIGEST_SIZE>,
        Vec<(TwoAdicMultiplicativeCoset<C::F>, Vec<(C::EF, Vec<C::EF>)>)>,
    );

    fn constant(value: Self::Constant, builder: &mut Builder<C>) -> Self {
        let (commit_val, domains_and_openings_val) = value;

        // Allocate the commitment.
        let commit = builder.dyn_array::<Felt<_>>(DIGEST_SIZE);
        let commit_val: [C::F; DIGEST_SIZE] = commit_val.into();
        for (i, f) in commit_val.into_iter().enumerate() {
            builder.set(&commit, i, f);
        }

        let mats = builder
            .dyn_array::<TwoAdicPcsMatsVariable<C>>(RVar::from(domains_and_openings_val.len()));

        for (i, (domain, opening)) in domains_and_openings_val.into_iter().enumerate() {
            let domain = builder.constant::<TwoAdicMultiplicativeCosetVariable<_>>(domain);

            let points_val = opening.iter().map(|(p, _)| *p).collect::<Vec<_>>();
            let values_val = opening.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>();
            let points: Array<_, Ext<_, _>> = builder.dyn_array(points_val.len());
            for (j, point) in points_val.into_iter().enumerate() {
                let el: Ext<_, _> = builder.eval(point.cons());
                builder.set_value(&points, j, el);
            }
            let values: Array<_, Array<_, Ext<_, _>>> = builder.dyn_array(values_val.len());
            for (j, val) in values_val.into_iter().enumerate() {
                let tmp = builder.dyn_array(val.len());
                for (k, v) in val.into_iter().enumerate() {
                    let el: Ext<_, _> = builder.eval(v.cons());
                    builder.set_value(&tmp, k, el);
                }
                builder.set_value(&values, j, tmp);
            }
            let mat = TwoAdicPcsMatsVariable {
                domain,
                points,
                values,
            };
            builder.set_value(&mats, i, mat);
        }

        Self {
            batch_commit: DigestVariable::Felt(commit),
            mats,
            permutation: builder.dyn_array(0),
        }
    }
}

impl<C: Config> PolynomialSpaceVariable<C> for TwoAdicMultiplicativeCosetVariable<C>
where
    C::F: TwoAdicField,
{
    type Constant = TwoAdicMultiplicativeCoset<C::F>;

    fn next_point(
        &self,
        builder: &mut Builder<C>,
        point: Ext<<C as Config>::F, <C as Config>::EF>,
    ) -> Ext<<C as Config>::F, <C as Config>::EF> {
        builder.eval(point * self.gen())
    }

    fn selectors_at_point(
        &self,
        builder: &mut Builder<C>,
        point: Ext<<C as Config>::F, <C as Config>::EF>,
    ) -> LagrangeSelectors<Ext<<C as Config>::F, <C as Config>::EF>> {
        let unshifted_point: Ext<_, _> = builder.eval(point * self.shift.inverse());
        let z_h_expr =
            builder.exp_power_of_2_v::<Ext<_, _>>(unshifted_point, self.log_n.clone()) - C::EF::ONE;
        let z_h: Ext<_, _> = builder.eval(z_h_expr);

        LagrangeSelectors {
            is_first_row: builder.eval(z_h / (unshifted_point - C::EF::ONE)),
            is_last_row: builder.eval(z_h / (unshifted_point - self.gen().inverse())),
            is_transition: builder.eval(unshifted_point - self.gen().inverse()),
            inv_zeroifier: builder.eval(z_h.inverse()),
        }
    }

    fn zp_at_point(
        &self,
        builder: &mut Builder<C>,
        point: Ext<<C as Config>::F, <C as Config>::EF>,
    ) -> Ext<<C as Config>::F, <C as Config>::EF> {
        let unshifted_power =
            builder.exp_power_of_2_v::<Ext<_, _>>(point * self.shift.inverse(), self.log_n.clone());
        builder.eval(unshifted_power - C::EF::ONE)
    }

    fn split_domains(
        &self,
        builder: &mut Builder<C>,
        log_num_chunks: impl Into<RVar<C::N>>,
        num_chunks: impl Into<RVar<C::N>>,
    ) -> Array<C, Self> {
        let log_num_chunks = log_num_chunks.into();
        let num_chunks = num_chunks.into();
        let log_n = builder.eval_expr(self.log_n.clone() - log_num_chunks);

        let g_dom = self.gen();
        let g = builder.exp_power_of_2_v::<Felt<C::F>>(g_dom, log_num_chunks);

        let domain_power: Felt<_> = builder.eval(C::F::ONE);

        let domains = builder.array(num_chunks);

        builder.range(0, num_chunks).for_each(|i_vec, builder| {
            let log_n = builder.eval(log_n);
            let domain = TwoAdicMultiplicativeCosetVariable {
                log_n,
                shift: builder.eval(self.shift * domain_power),
                g,
            };
            // ATTENTION: here must use `builder.set_value`. `builder.set` will convert `Usize::Const`
            // to `Usize::Var` because it calls `builder.eval`.
            builder.set_value(&domains, i_vec[0], domain);
            builder.assign(&domain_power, domain_power * g_dom);
        });

        domains
    }

    fn split_domains_const(&self, builder: &mut Builder<C>, log_num_chunks: usize) -> Vec<Self> {
        let num_chunks = 1 << log_num_chunks;
        let log_n: Usize<_> =
            builder.eval(self.log_n.clone() - C::N::from_canonical_usize(log_num_chunks));

        let g_dom = self.gen();
        let g = builder.exp_power_of_2_v::<Felt<C::F>>(g_dom, log_num_chunks);

        let domain_power: Felt<_> = builder.eval(C::F::ONE);
        let mut domains = vec![];

        for _ in 0..num_chunks {
            domains.push(TwoAdicMultiplicativeCosetVariable {
                log_n: log_n.clone(),
                shift: builder.eval(self.shift * domain_power),
                g,
            });
            builder.assign(&domain_power, domain_power * g_dom);
        }
        domains
    }

    fn create_disjoint_domain(
        &self,
        builder: &mut Builder<C>,
        log_degree: RVar<<C as Config>::N>,
        config: Option<BasefoldConfigVariable<C>>,
    ) -> Self {
        let domain = config.unwrap().get_subgroup(builder, log_degree);
        TwoAdicMultiplicativeCosetVariable {
            log_n: domain.log_n,
            shift: builder.eval(self.shift * C::F::GENERATOR),
            g: domain.g,
        }
    }
}

#[derive(Clone)]
pub struct TwoAdicBasefoldPcsVariable<C: Config> {
    pub config: BasefoldConfigVariable<C>,
}

impl<C: Config> PcsVariable<C> for TwoAdicBasefoldPcsVariable<C>
where
    C::F: TwoAdicField,
    C::EF: TwoAdicField,
{
    type Domain = TwoAdicMultiplicativeCosetVariable<C>;

    type Commitment = DigestVariable<C>;

    type Proof = BasefoldProofVariable<C>;

    fn natural_domain_for_log_degree(
        &self,
        builder: &mut Builder<C>,
        log_degree: RVar<C::N>,
    ) -> Self::Domain {
        self.config.get_subgroup(builder, log_degree)
    }

    fn verify(
        &self,
        builder: &mut Builder<C>,
        rounds: Array<C, TwoAdicPcsRoundVariable<C>>,
        proof: Self::Proof,
        log_max_height: RVar<C::N>,
        challenger: &mut impl ChallengerVariable<C>,
    ) {
        verify_two_adic_pcs(
            builder,
            &self.config,
            rounds,
            proof,
            log_max_height,
            challenger,
        )
    }
}

fn get_max_matrix_width<C: Config>(
    builder: &mut Builder<C>,
    rounds: &Array<C, TwoAdicPcsRoundVariable<C>>,
) -> usize {
    let mut ret = 0;
    for i in 0..rounds.len().value() {
        let round = builder.get(rounds, i);
        for j in 0..round.mats.len().value() {
            let mat = builder.get(&round.mats, j);
            let local = builder.get(&mat.values, 0);
            ret = ret.max(local.len().value());
        }
    }
    ret
}

#[derive(DslVariable, Clone)]
struct RoundContext<C: Config> {
    /// Opened values buffer.
    ov_ptrs: Array<C, Array<C, Felt<C::F>>>,
    /// Permuted opened values buffer.
    perm_ov_ptrs: Array<C, Array<C, Felt<C::F>>>,
    /// Permuted matrix dimensions.
    batch_dims: Array<C, DimensionsVariable<C>>,
    /// Alpha pows for each matrix.
    mat_alpha_pows: Array<C, Ext<C::F, C::EF>>,
    /// Max height in the matrices.
    log_batch_max_height: Usize<C::N>,
}

fn compute_rounds_context<C: Config>(
    builder: &mut Builder<C>,
    rounds: &Array<C, TwoAdicPcsRoundVariable<C>>,
    log_blowup: usize,
    alpha: Ext<C::F, C::EF>,
) -> Array<C, RoundContext<C>> {
    let ret: Array<C, RoundContext<C>> = builder.array(rounds.len());

    // This maximum is safe because the log width of any matrix in an AIR must fit
    // within a single field element.
    const MAX_LOG_WIDTH: usize = 31;
    let pow_of_alpha: Array<C, Ext<_, _>> = builder.array(MAX_LOG_WIDTH);
    if !builder.flags.static_only {
        // Repeatedly square alpha to get (alpha, alpha^2, alpha^4, ...)
        let current: Ext<_, _> = builder.eval(alpha);
        for i in 0..MAX_LOG_WIDTH {
            builder.set(&pow_of_alpha, i, current);
            builder.assign(&current, current * current);
        }
    }

    iter_zip!(builder, rounds, ret).for_each(|ptr_vec, builder| {
        let round = builder.iter_ptr_get(rounds, ptr_vec[0]);
        let permutation = round.permutation;
        // to_perm_index(k) = if static or permutation.is_empty() { k } else { permutation[k] }
        let to_perm_index = |builder: &mut Builder<_>, k: RVar<_>| {
            // Always no permutation in static mode
            if builder.flags.static_only {
                builder.eval(k)
            } else {
                let ret: Usize<_> = builder.uninit();
                builder.if_eq(permutation.len(), RVar::zero()).then_or_else(
                    |builder| {
                        builder.assign(&ret, k);
                    },
                    |builder| {
                        let value = builder.get(&permutation, k);
                        builder.assign(&ret, value);
                    },
                );
                ret
            }
        };

        let ov_ptrs: Array<C, Array<C, Felt<C::F>>> = builder.array(round.mats.len());
        let perm_ov_ptrs: Array<C, Array<C, Felt<C::F>>> = builder.array(round.mats.len());
        let batch_dims: Array<C, DimensionsVariable<C>> = builder.array(round.mats.len());
        let mat_alpha_pows: Array<C, Ext<_, _>> = builder.array(round.mats.len());
        let log_batch_max_height: Usize<_> = {
            let log_batch_max_index = to_perm_index(builder, RVar::zero());
            let mat = builder.get(&round.mats, log_batch_max_index);
            let domain = mat.domain;
            builder.eval(domain.log_n + RVar::from(log_blowup))
        };

        iter_zip!(builder, round.mats, ov_ptrs, mat_alpha_pows).for_each(|ptr_vec, builder| {
            let mat = builder.iter_ptr_get(&round.mats, ptr_vec[0]);
            let local = builder.get(&mat.values, 0);
            // We allocate the underlying buffer for the current `ov_ptr` here. On allocation, it is uninit, and
            // will be written to on the first call of `basefold_single_reduced_opening_eval` for this `ov_ptr`.
            let buf = builder.array(local.len());
            let width = buf.len();
            builder.iter_ptr_set(&ov_ptrs, ptr_vec[1], buf);

            if !builder.flags.static_only {
                // Split width into bits, and compute alpha^width using the
                // precomputed powers of alpha.
                let width = width.get_var();
                // This is dynamic only so safe to cast.
                let width_f = builder.unsafe_cast_var_to_felt(width);
                let bits = builder.num2bits_f(width_f, MAX_LOG_WIDTH as u32);
                let mat_alpha_pow: Ext<_, _> = builder.eval(C::EF::ONE.cons());
                for i in 0..MAX_LOG_WIDTH {
                    let bit = builder.get(&bits, i);
                    builder.if_eq(bit, RVar::one()).then(|builder| {
                        let to_mul = builder.get(&pow_of_alpha, i);
                        builder.assign(&mat_alpha_pow, mat_alpha_pow * to_mul);
                    });
                }
                builder.iter_ptr_set(&mat_alpha_pows, ptr_vec[2], mat_alpha_pow);
            }
        });
        builder
            .range(0, round.mats.len())
            .for_each(|i_vec, builder| {
                let i = i_vec[0];
                let perm_i = to_perm_index(builder, i);
                let mat = builder.get(&round.mats, perm_i.clone());

                let domain = mat.domain;
                let dim = DimensionsVariable::<C> {
                    log_height: builder.eval(domain.log_n + RVar::from(log_blowup)),
                };
                builder.set_value(&batch_dims, i, dim);
                let perm_ov_ptr = builder.get(&ov_ptrs, perm_i);
                // Note both `ov_ptrs` and `perm_ov_ptrs` point to the same memory.
                builder.set_value(&perm_ov_ptrs, i, perm_ov_ptr);
            });
        builder.iter_ptr_set(
            &ret,
            ptr_vec[1],
            RoundContext {
                ov_ptrs,
                perm_ov_ptrs,
                batch_dims,
                mat_alpha_pows,
                log_batch_max_height,
            },
        );
    });
    ret
}

pub mod tests {
    use std::cmp::Reverse;

    use itertools::Itertools;
    use openvm_circuit::arch::instructions::program::Program;
    use openvm_native_compiler::{
        asm::AsmBuilder,
        ir::{Array, RVar, DIGEST_SIZE},
    };
    use openvm_stark_backend::{
        config::{StarkGenericConfig, Val},
        p3_challenger::{CanObserve, FieldChallenger},
        p3_commit::{Pcs, TwoAdicMultiplicativeCoset},
        p3_matrix::dense::RowMajorMatrix,
    };
    use openvm_stark_sdk::{
        config::baby_bear_poseidon2::{default_engine, BabyBearPoseidon2Config},
        p3_baby_bear::BabyBear,
    };
    use rand::rngs::OsRng;

    use crate::basefold_verifier::{
        commit::PcsVariable,
        two_adic_pcs::TwoAdicBasefoldPcsVariable,
        types::{InnerBasefoldProof, TwoAdicPcsRoundVariable},
    };
    use openvm_native_recursion::{
        challenger::{duplex::DuplexChallengerVariable, CanObserveDigest, FeltChallenger},
        digest::DigestVariable,
        fri::TwoAdicMultiplicativeCosetVariable,
        hints::{Hintable, InnerVal},
        utils::const_fri_config as const_basefold_config,
    };

    #[allow(dead_code)]
    pub fn build_test_basefold_with_cols_and_log2_rows(
        nb_cols: usize,
        nb_log2_rows: usize,
    ) -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        type SC = BabyBearPoseidon2Config;
        type F = Val<SC>;
        type EF = <SC as StarkGenericConfig>::Challenge;
        type Challenger = <SC as StarkGenericConfig>::Challenger;
        type ScPcs = <SC as StarkGenericConfig>::Pcs;

        let mut rng = &mut OsRng;
        let log_degrees = &[nb_log2_rows];
        let engine = default_engine();
        let pcs = engine.config.pcs();
        let perm = engine.perm;

        // Generate proof.
        let domains_and_polys = log_degrees
            .iter()
            .map(|&d| {
                (
                    <ScPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(pcs, 1 << d),
                    RowMajorMatrix::<F>::rand(&mut rng, 1 << d, nb_cols),
                )
            })
            .sorted_by_key(|(dom, _)| Reverse(dom.log_n))
            .collect::<Vec<_>>();
        let (commit, data) = <ScPcs as Pcs<EF, Challenger>>::commit(pcs, domains_and_polys.clone());
        let mut challenger = Challenger::new(perm.clone());
        challenger.observe(commit);
        let zeta = challenger.sample_ext_element::<EF>();
        let points = domains_and_polys
            .iter()
            .map(|_| vec![zeta])
            .collect::<Vec<_>>();
        let (opening, proof) = pcs.open(vec![(&data, points)], &mut challenger);

        // Verify proof.
        let mut challenger = Challenger::new(perm.clone());
        challenger.observe(commit);
        challenger.sample_ext_element::<EF>();
        let os: Vec<(TwoAdicMultiplicativeCoset<F>, Vec<_>)> = domains_and_polys
            .iter()
            .zip(&opening[0])
            .map(|((domain, _), mat_openings)| (*domain, vec![(zeta, mat_openings[0].clone())]))
            .collect();
        pcs.verify(vec![(commit, os.clone())], &proof, &mut challenger)
            .unwrap();

        // Test the recursive Pcs.
        let mut builder = AsmBuilder::<F, EF>::default();
        let config = const_basefold_config(&mut builder, &engine.fri_params);
        let pcs_var = TwoAdicBasefoldPcsVariable { config };
        let rounds =
            builder.constant::<Array<_, TwoAdicPcsRoundVariable<_>>>(vec![(commit, os.clone())]);

        // Test natural domain for degree.
        for log_d_val in log_degrees.iter() {
            let log_d = *log_d_val;
            let domain = pcs_var.natural_domain_for_log_degree(&mut builder, RVar::from(log_d));

            let domain_val =
                <ScPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(pcs, 1 << log_d_val);

            let expected_domain: TwoAdicMultiplicativeCosetVariable<_> =
                builder.constant(domain_val);

            builder.assert_eq::<TwoAdicMultiplicativeCosetVariable<_>>(domain, expected_domain);
        }

        // Test proof verification.
        let proofvar = InnerBasefoldProof::read(&mut builder);
        let mut challenger = DuplexChallengerVariable::new(&mut builder);
        let commit = <[InnerVal; DIGEST_SIZE]>::from(commit).to_vec();
        let commit = DigestVariable::Felt(builder.constant::<Array<_, _>>(commit));
        challenger.observe_digest(&mut builder, commit);
        challenger.sample_ext(&mut builder);
        pcs_var.verify(
            &mut builder,
            rounds,
            proofvar,
            RVar::from(nb_log2_rows),
            &mut challenger,
        );
        builder.halt();

        let program = builder.compile_isa();
        let mut witness_stream = Vec::new();
        witness_stream.extend(proof.write());
        (program, witness_stream)
    }

    #[test]
    fn test_two_adic_basefold_pcs_single_batch() {
        let (program, witness) = build_test_basefold_with_cols_and_log2_rows(10, 10);
        openvm_native_circuit::execute_program(program, witness);
    }
}
