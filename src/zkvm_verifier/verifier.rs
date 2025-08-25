use super::binding::{
    ClaimAndPoint, GKRClaimEvaluation, RotationClaim, ZKVMChipProofInputVariable,
    ZKVMProofInputVariable,
};
use crate::arithmetics::{
    challenger_multi_observe, eq_eval, eval_ceno_expr_with_instance, PolyEvaluator,
    UniPolyExtrapolator,
};
use crate::basefold_verifier::basefold::{
    BasefoldCommitmentVariable, RoundOpeningVariable, RoundVariable,
};
use crate::basefold_verifier::mmcs::MmcsCommitmentVariable;
use crate::basefold_verifier::query_phase::PointAndEvalsVariable;
use crate::basefold_verifier::utils::pow_2;
// use crate::basefold_verifier::verifier::batch_verify;
use crate::tower_verifier::program::verify_tower_proof;
use crate::transcript::transcript_observe_label;
use crate::zkvm_verifier::binding::{
    GKRProofVariable, LayerProofVariable, SumcheckLayerProofVariable,
};
use crate::{
    arithmetics::{
        build_eq_x_r_vec_sequential, ceil_log2, concat, dot_product as ext_dot_product,
        eq_eval_less_or_equal_than, eval_wellform_address_vec, gen_alpha_pows, max_usize_arr,
        max_usize_vec, nested_product,
    },
    tower_verifier::{
        binding::{PointAndEvalVariable, PointVariable},
        program::iop_verifier_state_verify,
    },
};
use ceno_mle::expression::{Expression, Instance, StructuralWitIn};
use ceno_zkvm::structs::VerifyingKey;
use ceno_zkvm::{
    circuit_builder::SetTableSpec, scheme::verifier::ZKVMVerifier, structs::ComposedConstrainSystem,
};
use ff_ext::BabyBearExt4;
use gkr_iop::gkr::layer::ROTATION_OPENING_COUNT;
use gkr_iop::{
    evaluation::EvalExpression,
    gkr::{booleanhypercube::BooleanHypercube, layer::Layer, GKRCircuit},
    selector::SelectorType,
};
use itertools::{interleave, izip, Itertools};
use mpcs::{Basefold, BasefoldRSParams};
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::{
    duplex::DuplexChallengerVariable, CanObserveVariable, FeltChallenger,
};
use openvm_stark_backend::p3_field::FieldAlgebra;
use p3_baby_bear::BabyBear;

type F = BabyBear;
type E = BabyBearExt4;
type Pcs = Basefold<E, BasefoldRSParams>;

const NUM_FANIN: usize = 2;

pub fn transcript_group_observe_label<C: Config>(
    builder: &mut Builder<C>,
    challenger_group: &mut Vec<DuplexChallengerVariable<C>>,
    label: &[u8],
) {
    for t in challenger_group {
        transcript_observe_label(builder, t, label);
    }
}

pub fn transcript_group_observe_f<C: Config>(
    builder: &mut Builder<C>,
    challenger_group: &mut Vec<DuplexChallengerVariable<C>>,
    f: Felt<C::F>,
) {
    for t in challenger_group {
        t.observe(builder, f);
    }
}

pub fn transcript_group_sample_ext<C: Config>(
    builder: &mut Builder<C>,
    challenger_group: &mut Vec<DuplexChallengerVariable<C>>,
) -> Ext<C::F, C::EF> {
    let e: Ext<C::F, C::EF> = challenger_group[0].sample_ext(builder);

    challenger_group.into_iter().skip(1).for_each(|c| {
        c.sample_ext(builder);
    });

    e
}

pub fn verify_zkvm_proof<C: Config<F = F>>(
    builder: &mut Builder<C>,
    zkvm_proof_input: ZKVMProofInputVariable<C>,
    vk: &ZKVMVerifier<E, Pcs>,
) {
    let mut challenger = DuplexChallengerVariable::new(builder);
    transcript_observe_label(builder, &mut challenger, b"riscv");

    let prod_r: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let prod_w: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let logup_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    iter_zip!(builder, zkvm_proof_input.raw_pi).for_each(|ptr_vec, builder| {
        let v = builder.iter_ptr_get(&zkvm_proof_input.raw_pi, ptr_vec[0]);

        challenger_multi_observe(builder, &mut challenger, &v);
    });

    iter_zip!(builder, zkvm_proof_input.raw_pi, zkvm_proof_input.pi_evals).for_each(
        |ptr_vec, builder| {
            let raw = builder.iter_ptr_get(&zkvm_proof_input.raw_pi, ptr_vec[0]);
            let eval = builder.iter_ptr_get(&zkvm_proof_input.pi_evals, ptr_vec[1]);
            let raw0 = builder.get(&raw, 0);

            builder.if_eq(raw.len(), Usize::from(1)).then(|builder| {
                let raw0_ext = builder.ext_from_base_slice(&[raw0]);
                builder.assert_ext_eq(raw0_ext, eval);
            });
        },
    );

    let fixed_commit = if let Some(fixed_commit) = vk.vk.fixed_commit.as_ref() {
        let commit: crate::basefold_verifier::hash::Hash = fixed_commit.commit().into();
        let commit_array: Array<C, Felt<C::F>> = builder.dyn_array(commit.value.len());
        commit.value.into_iter().enumerate().for_each(|(i, v)| {
            let v = builder.constant(v);
            // TODO: put fixed commit to public values
            // builder.commit_public_value(v);

            builder.set_value(&commit_array, i, v);
        });
        challenger_multi_observe(builder, &mut challenger, &commit_array);

        // FIXME: do not hardcode this in the program
        let log2_max_codeword_size_felt = builder.constant(C::F::from_canonical_usize(
            fixed_commit.log2_max_codeword_size,
        ));
        let log2_max_codeword_size: Var<C::N> = builder.constant(C::N::from_canonical_usize(
            fixed_commit.log2_max_codeword_size,
        ));

        challenger.observe(builder, log2_max_codeword_size_felt);

        Some(BasefoldCommitmentVariable {
            commit: MmcsCommitmentVariable {
                value: commit_array,
            },
            log2_max_codeword_size: log2_max_codeword_size.into(),
        })
    } else {
        None
    };

    let zero_f: Felt<C::F> = builder.constant(C::F::ZERO);
    iter_zip!(builder, zkvm_proof_input.chip_proofs).for_each(|ptr_vec, builder| {
        let chip_proof = builder.iter_ptr_get(&zkvm_proof_input.chip_proofs, ptr_vec[0]);
        let num_instances = builder.unsafe_cast_var_to_felt(chip_proof.num_instances.get_var());

        challenger.observe(builder, chip_proof.idx_felt);
        challenger.observe(builder, zero_f);
        challenger.observe(builder, num_instances);
        challenger.observe(builder, zero_f);
    });

    challenger_multi_observe(
        builder,
        &mut challenger,
        &zkvm_proof_input.witin_commit.commit.value,
    );
    {
        let log2_max_codeword_size = builder.unsafe_cast_var_to_felt(
            zkvm_proof_input
                .witin_commit
                .log2_max_codeword_size
                .get_var(),
        );
        challenger.observe(builder, log2_max_codeword_size);
    }

    let alpha = challenger.sample_ext(builder);
    let beta = challenger.sample_ext(builder);

    let challenges: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(2);
    builder.set(&challenges, 0, alpha.clone());
    builder.set(&challenges, 1, beta.clone());

    let mut unipoly_extrapolator = UniPolyExtrapolator::new(builder);
    let mut poly_evaluator = PolyEvaluator::new(builder);

    let dummy_table_item = alpha.clone();
    let dummy_table_item_multiplicity: Var<C::N> = builder.constant(C::N::ZERO);

    let num_fixed_opening = vk
        .vk
        .circuit_vks
        .values()
        .filter(|c| c.get_cs().num_fixed() > 0)
        .count();

    let witin_openings: Array<C, RoundOpeningVariable<C>> =
        builder.dyn_array(zkvm_proof_input.chip_proofs.len());
    let fixed_openings: Array<C, RoundOpeningVariable<C>> =
        builder.dyn_array(Usize::from(num_fixed_opening));

    let num_chips_verified: Usize<C::N> = builder.eval(C::N::ZERO);
    let num_chips_have_fixed: Usize<C::N> = builder.eval(C::N::ZERO);

    let chip_indices: Array<C, Var<C::N>> = builder.dyn_array(zkvm_proof_input.chip_proofs.len());
    builder
        .range(0, chip_indices.len())
        .for_each(|idx_vec, builder| {
            let i = idx_vec[0];
            let chip_proof = builder.get(&zkvm_proof_input.chip_proofs, i);
            builder.set(&chip_indices, i, chip_proof.idx);
        });

    for (i, (circuit_name, chip_vk)) in vk.vk.circuit_vks.iter().enumerate() {
        let chip_id: Var<C::N> = builder.get(&chip_indices, num_chips_verified.get_var());

        builder.if_eq(chip_id, RVar::from(i)).then(|builder| {
            let chip_proof =
                builder.get(&zkvm_proof_input.chip_proofs, num_chips_verified.get_var());
            let circuit_vk = &vk.vk.circuit_vks[circuit_name];

            builder.assert_usize_eq(
                chip_proof.wits_in_evals.len(),
                Usize::from(circuit_vk.get_cs().num_witin()),
            );
            builder.assert_usize_eq(
                chip_proof.fixed_in_evals.len(),
                Usize::from(circuit_vk.get_cs().num_fixed()),
            );
            builder.assert_usize_eq(
                chip_proof.record_r_out_evals.len(),
                Usize::from(circuit_vk.get_cs().num_reads()),
            );
            builder.assert_usize_eq(
                chip_proof.record_w_out_evals.len(),
                Usize::from(circuit_vk.get_cs().num_writes()),
            );
            builder.assert_usize_eq(
                chip_proof.record_lk_out_evals.len(),
                Usize::from(circuit_vk.get_cs().num_lks()),
            );

            let chip_logup_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
            iter_zip!(builder, chip_proof.record_lk_out_evals).for_each(|ptr_vec, builder| {
                let evals = builder.iter_ptr_get(&chip_proof.record_lk_out_evals, ptr_vec[0]);
                let p1 = builder.get(&evals, 0);
                let p2 = builder.get(&evals, 1);
                let q1 = builder.get(&evals, 2);
                let q2 = builder.get(&evals, 3);

                builder.assign(&chip_logup_sum, chip_logup_sum + p1 * q1.inverse());
                builder.assign(&chip_logup_sum, chip_logup_sum + p2 * q2.inverse());
            });
            challenger.observe(builder, chip_proof.idx_felt);

            builder.cycle_tracker_start("Verify chip proof");
            let input_opening_point = if chip_vk.get_cs().is_opcode_circuit() {
                // getting the number of dummy padding item that we used in this opcode circuit
                let num_lks = chip_vk.get_cs().num_lks();
                // FIXME: use builder to compute this
                let num_instances = pow_2(builder, chip_proof.log2_num_instances.get_var());
                let num_padded_instance: Var<C::N> =
                    builder.eval(num_instances - chip_proof.num_instances.clone());

                let new_multiplicity: Usize<C::N> =
                    builder.eval(Usize::from(num_lks) * Usize::from(num_padded_instance));
                builder.assign(
                    &dummy_table_item_multiplicity,
                    dummy_table_item_multiplicity + new_multiplicity,
                );

                builder.assign(&logup_sum, logup_sum + chip_logup_sum);
                verify_opcode_proof(
                    builder,
                    &mut challenger,
                    &chip_proof,
                    &zkvm_proof_input.pi_evals,
                    &challenges,
                    &chip_vk,
                    &mut unipoly_extrapolator,
                )
            } else {
                builder.assign(&logup_sum, logup_sum - chip_logup_sum);
                verify_table_proof(
                    builder,
                    &mut challenger,
                    &chip_proof,
                    &zkvm_proof_input.raw_pi,
                    &zkvm_proof_input.raw_pi_num_variables,
                    &zkvm_proof_input.pi_evals,
                    &challenges,
                    &chip_vk,
                    &mut unipoly_extrapolator,
                    &mut poly_evaluator,
                )
            };
            // root cause: for keccak, the input_opening_point has length=12
            // but outside the loop, it becomes 7
            builder.print_v(input_opening_point.len().get_var());
            builder.cycle_tracker_end("Verify chip proof");

            let witin_round: RoundOpeningVariable<C> = builder.eval(RoundOpeningVariable {
                num_var: chip_proof.log2_num_instances.get_var(),
                point_and_evals: PointAndEvalsVariable {
                    point: PointVariable {
                        fs: input_opening_point.clone(),
                    },
                    evals: chip_proof.wits_in_evals,
                },
            });
            builder.set_value(&witin_openings, num_chips_verified.get_var(), witin_round);

            if chip_vk.get_cs().num_fixed() > 0 {
                let fixed_round: RoundOpeningVariable<C> = builder.eval(RoundOpeningVariable {
                    num_var: chip_proof.log2_num_instances.get_var(),
                    point_and_evals: PointAndEvalsVariable {
                        point: PointVariable {
                            fs: input_opening_point.clone(),
                        },
                        evals: chip_proof.fixed_in_evals,
                    },
                });

                builder.set_value(&fixed_openings, num_chips_have_fixed.get_var(), fixed_round);

                builder.inc(&num_chips_have_fixed);
            }

            let record_r_out_evals_prod = nested_product(builder, &chip_proof.record_r_out_evals);
            builder.assign(&prod_r, prod_r * record_r_out_evals_prod);

            let record_w_out_evals_prod = nested_product(builder, &chip_proof.record_w_out_evals);
            builder.assign(&prod_w, prod_w * record_w_out_evals_prod);

            builder.inc(&num_chips_verified);
        });
    }

    builder.assert_usize_eq(num_chips_have_fixed, Usize::from(num_fixed_opening));
    builder.assert_eq::<Usize<_>>(num_chips_verified, chip_indices.len());

    let dummy_table_item_multiplicity =
        builder.unsafe_cast_var_to_felt(dummy_table_item_multiplicity);
    builder.assign(
        &logup_sum,
        logup_sum - dummy_table_item_multiplicity * dummy_table_item.inverse(),
    );

    let rounds: Array<C, RoundVariable<C>> = if num_fixed_opening > 0 {
        builder.dyn_array(2)
    } else {
        builder.dyn_array(1)
    };
    builder.set(
        &rounds,
        0,
        RoundVariable {
            commit: zkvm_proof_input.witin_commit,
            openings: witin_openings,
            perm: zkvm_proof_input.witin_perm.clone(),
        },
    );

    if num_fixed_opening > 0 {
        builder.set(
            &rounds,
            1,
            RoundVariable {
                commit: fixed_commit.unwrap(),
                openings: fixed_openings,
                perm: zkvm_proof_input.fixed_perm,
            },
        );
    }

    batch_verify(
        builder,
        zkvm_proof_input.max_num_var,
        rounds,
        zkvm_proof_input.pcs_proof,
        &mut challenger,
    );

    let empty_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(0);
    let initial_global_state = eval_ceno_expr_with_instance(
        builder,
        &empty_arr,
        &empty_arr,
        &empty_arr,
        &zkvm_proof_input.pi_evals,
        &challenges,
        &vk.vk.initial_global_state_expr,
    );
    builder.assign(&prod_w, prod_w * initial_global_state);

    let finalize_global_state = eval_ceno_expr_with_instance(
        builder,
        &empty_arr,
        &empty_arr,
        &empty_arr,
        &zkvm_proof_input.pi_evals,
        &challenges,
        &vk.vk.finalize_global_state_expr,
    );
    builder.assign(&prod_r, prod_r * finalize_global_state);

    /* TODO: Temporarily disable product check for missing subcircuits
        builder.assert_ext_eq(prod_r, prod_w);
    */
}

pub fn verify_opcode_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    opcode_proof: &ZKVMChipProofInputVariable<C>,
    pi_evals: &Array<C, Ext<C::F, C::EF>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    vk: &VerifyingKey<E>,
    unipoly_extrapolator: &mut UniPolyExtrapolator<C>,
) -> Array<C, Ext<C::F, C::EF>> {
    let cs = vk.get_cs();
    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);

    let r_len = cs.zkvm_v1_css.r_expressions.len();
    let w_len = cs.zkvm_v1_css.w_expressions.len();
    let lk_len = cs.zkvm_v1_css.lk_expressions.len();

    let num_batched = r_len + w_len + lk_len;

    let r_counts_per_instance: Usize<C::N> = Usize::from(r_len);
    let w_counts_per_instance: Usize<C::N> = Usize::from(w_len);
    let lk_counts_per_instance: Usize<C::N> = Usize::from(lk_len);
    let num_batched: Usize<C::N> = Usize::from(num_batched);

    let log2_num_instances = opcode_proof.log2_num_instances.clone();

    let num_var_with_rotation: Usize<C::N> = Usize::Var(Var::uninit(builder));
    builder
        .if_eq(opcode_proof.has_gkr_proof.clone(), Usize::from(1))
        .then_or_else(
            |builder| {
                builder.assign(
                    &num_var_with_rotation,
                    opcode_proof.gkr_iop_proof.num_var_with_rotation.clone(),
                );
            },
            |builder| {
                builder.assign(&num_var_with_rotation, log2_num_instances.clone());
            },
        );

    let tower_proof = &opcode_proof.tower_proof;

    let num_variables: Array<C, Usize<C::N>> = builder.dyn_array(num_batched);
    builder
        .range(0, num_variables.len())
        .for_each(|idx_vec, builder| {
            builder.set(&num_variables, idx_vec[0], num_var_with_rotation.clone());
        });

    let prod_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>> = concat(
        builder,
        &opcode_proof.record_r_out_evals,
        &opcode_proof.record_w_out_evals,
    );

    let num_fanin: Usize<C::N> = Usize::from(NUM_FANIN);

    builder.cycle_tracker_start("verify tower proof for opcode");
    let (_, record_evals, logup_p_evals, logup_q_evals) = verify_tower_proof(
        builder,
        challenger,
        prod_out_evals,
        &opcode_proof.record_lk_out_evals,
        num_variables,
        num_fanin,
        num_var_with_rotation.clone(),
        tower_proof,
        unipoly_extrapolator,
    );
    builder.cycle_tracker_end("verify tower proof for opcode");

    let logup_p_eval = builder.get(&logup_p_evals, 0).eval;
    builder.assert_ext_eq(logup_p_eval, one);

    // verify zero statement (degree > 1) + sel sumcheck
    let _rt = builder.get(&record_evals, 0);
    let num_rw_records: Usize<C::N> = builder.eval(r_counts_per_instance + w_counts_per_instance);
    builder.assert_usize_eq(record_evals.len(), num_rw_records.clone());
    builder.assert_usize_eq(logup_p_evals.len(), lk_counts_per_instance.clone());
    builder.assert_usize_eq(logup_q_evals.len(), lk_counts_per_instance.clone());

    let composed_cs = vk.get_cs();
    let ComposedConstrainSystem {
        zkvm_v1_css: _,
        gkr_circuit,
    } = &composed_cs;
    let gkr_circuit = gkr_circuit.clone().unwrap();

    let out_evals_len: Usize<C::N> = builder.eval(record_evals.len() + logup_q_evals.len());
    let out_evals: Array<C, PointAndEvalVariable<C>> = builder.dyn_array(out_evals_len.clone());
    builder
        .range(0, record_evals.len())
        .for_each(|idx_vec, builder| {
            let cpt = builder.get(&record_evals, idx_vec[0]);
            builder.set(&out_evals, idx_vec[0], cpt);
        });
    let q_slice = out_evals.slice(builder, record_evals.len(), out_evals_len);
    builder
        .range(0, logup_q_evals.len())
        .for_each(|idx_vec, builder| {
            let cpt = builder.get(&logup_q_evals, idx_vec[0]);
            builder.set(&q_slice, idx_vec[0], cpt);
        });

    let opening_evaluations = verify_gkr_circuit(
        builder,
        challenger,
        gkr_circuit,
        &opcode_proof.gkr_iop_proof,
        challenges,
        pi_evals,
        &out_evals,
        opcode_proof,
        unipoly_extrapolator,
    );

    opening_evaluations[0].point.fs.clone()
}

pub fn verify_gkr_circuit<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    gkr_circuit: GKRCircuit<E>,
    gkr_proof: &GKRProofVariable<C>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    pub_io_evals: &Array<C, Ext<C::F, C::EF>>,
    claims: &Array<C, PointAndEvalVariable<C>>,
    opcode_proof: &ZKVMChipProofInputVariable<C>,
    unipoly_extrapolator: &mut UniPolyExtrapolator<C>,
) -> Vec<GKRClaimEvaluation<C>> {
    for (i, layer) in gkr_circuit.layers.iter().enumerate() {
        let layer_proof = builder.get(&gkr_proof.layer_proofs, i);
        let layer_challenges: Array<C, Ext<C::F, C::EF>> =
            generate_layer_challenges(builder, challenger, &challenges, layer.n_challenges);
        let eval_and_dedup_points: Array<C, ClaimAndPoint<C>> = extract_claim_and_point(
            builder,
            layer,
            &claims,
            &layer_challenges,
            &layer_proof.has_rotation,
        );

        // ZeroCheckLayer verification (might include other layer types in the future)
        let LayerProofVariable {
            main:
                SumcheckLayerProofVariable {
                    proof,
                    evals: main_evals,
                    evals_len_div_3: _main_evals_len_div_3,
                },
            rotation: rotation_proof,
            has_rotation,
        } = layer_proof;

        builder.if_eq(has_rotation, Usize::from(1)).then(|builder| {
            let first = builder.get(&eval_and_dedup_points, 0);
            builder.assert_usize_eq(first.has_point, Usize::from(1)); // Rotation proof should have at least one point
            let rt = first.point.fs.clone();

            let RotationClaim {
                left_evals,
                right_evals,
                target_evals,
                left_point,
                right_point,
                origin_point,
            } = verify_rotation(
                builder,
                gkr_proof.num_var_with_rotation.clone(),
                &rotation_proof,
                layer.rotation_cyclic_subgroup_size,
                layer.rotation_cyclic_group_log2,
                rt,
                challenger,
                unipoly_extrapolator,
            );

            let last_idx: Usize<C::N> = builder.eval(eval_and_dedup_points.len() - Usize::from(1));
            builder.set(
                &eval_and_dedup_points,
                last_idx.clone(),
                ClaimAndPoint {
                    evals: target_evals,
                    has_point: Usize::from(1),
                    point: PointVariable { fs: origin_point },
                },
            );

            builder.assign(&last_idx, last_idx.clone() - Usize::from(1));
            builder.set(
                &eval_and_dedup_points,
                last_idx.clone(),
                ClaimAndPoint {
                    evals: right_evals,
                    has_point: Usize::from(1),
                    point: PointVariable { fs: right_point },
                },
            );

            builder.assign(&last_idx, last_idx.clone() - Usize::from(1));
            builder.set(
                &eval_and_dedup_points,
                last_idx.clone(),
                ClaimAndPoint {
                    evals: left_evals,
                    has_point: Usize::from(1),
                    point: PointVariable { fs: left_point },
                },
            );
        });

        let rotation_exprs_len = layer.rotation_exprs.1.len();
        transcript_observe_label(builder, challenger, b"combine subset evals");
        let alpha_pows = gen_alpha_pows(
            builder,
            challenger,
            Usize::from(layer.exprs.len() + rotation_exprs_len * ROTATION_OPENING_COUNT),
        );

        let sigma: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
        let alpha_idx: Usize<C::N> = Usize::Var(Var::uninit(builder));
        builder.assign(&alpha_idx, C::N::from_canonical_usize(0));

        builder
            .range(0, eval_and_dedup_points.len())
            .for_each(|idx_vec, builder| {
                let ClaimAndPoint {
                    evals,
                    has_point: _,
                    point: _,
                } = builder.get(&eval_and_dedup_points, idx_vec[0]);
                let end_idx: Usize<C::N> = builder.eval(alpha_idx.clone() + evals.len());
                let alpha_slice: Array<C, Ext<<C as Config>::F, <C as Config>::EF>> =
                    alpha_pows.slice(builder, alpha_idx.clone(), end_idx.clone());

                let sub_sum = ext_dot_product(builder, &evals, &alpha_slice);
                builder.assign(&sigma, sigma.clone() + sub_sum);
                builder.assign(&alpha_idx, end_idx);
            });
        let max_degree = builder.constant(C::F::from_canonical_usize(layer.max_expr_degree + 1));
        let max_num_variables =
            builder.unsafe_cast_var_to_felt(gkr_proof.num_var_with_rotation.get_var());

        let (in_point, expected_evaluation) = iop_verifier_state_verify(
            builder,
            challenger,
            &sigma,
            &proof,
            max_num_variables,
            max_degree,
            unipoly_extrapolator,
        );

        layer
            .out_sel_and_eval_exprs
            .iter()
            .enumerate()
            .for_each(|(idx, (sel_type, _))| {
                let out_point = builder.get(&eval_and_dedup_points, idx).point.fs;
                evaluate_selector(
                    builder,
                    sel_type,
                    &main_evals,
                    &out_point,
                    &in_point,
                    opcode_proof,
                    layer.n_witin,
                );
            });

        let main_sumcheck_challenges_len: Usize<C::N> =
            builder.eval(alpha_pows.len() + Usize::from(2));
        let main_sumcheck_challenges: Array<C, Ext<C::F, C::EF>> =
            builder.dyn_array(main_sumcheck_challenges_len.clone());
        let alpha = builder.get(&challenges, 0);
        let beta = builder.get(&challenges, 1);
        builder.set(&main_sumcheck_challenges, 0, alpha);
        builder.set(&main_sumcheck_challenges, 1, beta);
        let challenge_slice =
            main_sumcheck_challenges.slice(builder, 2, main_sumcheck_challenges_len);
        builder
            .range(0, alpha_pows.len())
            .for_each(|idx_vec, builder| {
                let alpha = builder.get(&alpha_pows, idx_vec[0]);
                builder.set(&challenge_slice, idx_vec[0], alpha);
            });

        let empty_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(0);
        let got_claim = eval_ceno_expr_with_instance(
            builder,
            &empty_arr,
            &main_evals,
            &empty_arr,
            &pub_io_evals,
            &main_sumcheck_challenges,
            layer.main_sumcheck_expression.as_ref().unwrap(),
        );

        builder.assert_ext_eq(got_claim, expected_evaluation);

        // Update claim
        layer
            .in_eval_expr
            .iter()
            .enumerate()
            .for_each(|(idx, pos)| {
                let val = builder.get(&main_evals, idx);
                builder.set(
                    &claims,
                    *pos,
                    PointAndEvalVariable {
                        point: PointVariable {
                            fs: in_point.clone(),
                        },
                        eval: val,
                    },
                );
            });
    }

    // GKR Claim
    let input_layer = gkr_circuit.layers.last().unwrap();
    input_layer
        .in_eval_expr
        .iter()
        .enumerate()
        .map(|(poly, eval)| {
            let PointAndEvalVariable { point, eval } = builder.get(&claims, *eval);

            GKRClaimEvaluation {
                value: eval,
                point,
                poly: Usize::from(poly),
            }
        })
        .collect_vec()
}

pub fn verify_rotation<C: Config>(
    builder: &mut Builder<C>,
    max_num_variables: Usize<C::N>,
    rotation_proof: &SumcheckLayerProofVariable<C>,
    rotation_cyclic_subgroup_size: usize,
    rotation_cyclic_group_log2: usize,
    rt: Array<C, Ext<C::F, C::EF>>,
    challenger: &mut DuplexChallengerVariable<C>,
    unipoly_extrapolator: &mut UniPolyExtrapolator<C>,
) -> RotationClaim<C> {
    let SumcheckLayerProofVariable {
        proof,
        evals,
        evals_len_div_3: rotation_expr_len,
    } = rotation_proof;

    let rotation_expr_len = Usize::Var(rotation_expr_len.clone());
    transcript_observe_label(builder, challenger, b"combine subset evals");
    let rotation_alpha_pows = gen_alpha_pows(builder, challenger, rotation_expr_len.clone());
    let sigma: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    let max_num_variables = builder.unsafe_cast_var_to_felt(max_num_variables.get_var());
    let max_degree: Felt<C::F> = builder.constant(C::F::TWO);

    let (origin_point, expected_evaluation) = iop_verifier_state_verify(
        builder,
        challenger,
        &sigma,
        proof,
        max_num_variables,
        max_degree,
        unipoly_extrapolator,
    );

    // compute the selector evaluation
    let selector_eval = rotation_selector_eval(
        builder,
        &rt,
        &origin_point,
        rotation_cyclic_subgroup_size,
        rotation_cyclic_group_log2,
    );

    // check the final evaluations.
    let left_evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(rotation_expr_len.clone());
    let right_evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(rotation_expr_len.clone());
    let target_evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(rotation_expr_len);

    let got_claim: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let last_origin = if rotation_cyclic_group_log2 > 0 {
        builder.get(&origin_point, rotation_cyclic_group_log2 - 1)
    } else {
        one.clone()
    };

    builder
        .range(0, rotation_alpha_pows.len())
        .for_each(|idx_vec, builder| {
            let alpha = builder.get(&rotation_alpha_pows, idx_vec[0]);

            let rvar3 = RVar::from(3);
            let left_idx: Var<C::N> = builder.eval(idx_vec[0] * rvar3);
            let right_idx: Var<C::N> = builder.eval(idx_vec[0] * rvar3 + RVar::from(1));
            let target_idx: Var<C::N> = builder.eval(idx_vec[0] * rvar3 + RVar::from(2));

            let left = builder.get(&evals, left_idx);
            let right = builder.get(&evals, right_idx);
            let target = builder.get(&evals, target_idx);

            builder.set(&left_evals, idx_vec[0], left);
            builder.set(&right_evals, idx_vec[0], right);
            builder.set(&target_evals, idx_vec[0], target);

            builder.assign(
                &got_claim,
                got_claim + alpha * ((one - last_origin) * left + last_origin * right - target),
            );
        });
    builder.assign(&got_claim, got_claim * selector_eval);
    builder.assert_ext_eq(got_claim, expected_evaluation);

    let (left_point, right_point) =
        get_rotation_points(builder, rotation_cyclic_group_log2, &origin_point);

    RotationClaim {
        left_evals,
        right_evals,
        target_evals,
        left_point,
        right_point,
        origin_point,
    }
}

/// sel(rx)
/// = (\sum_{b = 0}^{cyclic_subgroup_size - 1} eq(out_point[..cyclic_group_log2_size], b) * eq(in_point[..cyclic_group_log2_size], b))
///     * \prod_{k = cyclic_group_log2_size}^{n - 1} eq(out_point[k], in_point[k])
pub fn rotation_selector_eval<C: Config>(
    builder: &mut Builder<C>,
    out_point: &Array<C, Ext<C::F, C::EF>>,
    in_point: &Array<C, Ext<C::F, C::EF>>,
    rotation_cyclic_subgroup_size: usize,
    cyclic_group_log2_size: usize,
) -> Ext<C::F, C::EF> {
    let bh = BooleanHypercube::new(5);
    let eval: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let rotation_index = bh
        .into_iter()
        .take(rotation_cyclic_subgroup_size)
        .collect_vec();

    let out_subgroup = out_point.slice(builder, 0, cyclic_group_log2_size);
    let in_subgroup = in_point.slice(builder, 0, cyclic_group_log2_size);
    let out_subgroup_eq = build_eq_x_r_vec_sequential(builder, &out_subgroup);
    let in_subgroup_eq = build_eq_x_r_vec_sequential(builder, &in_subgroup);

    for b in rotation_index {
        let out_v = builder.get(&out_subgroup_eq, b as usize);
        let in_v = builder.get(&in_subgroup_eq, b as usize);
        builder.assign(&eval, eval + in_v * out_v);
    }

    let out_subgroup = out_point.slice(builder, cyclic_group_log2_size, out_point.len());
    let in_subgroup = in_point.slice(builder, cyclic_group_log2_size, in_point.len());

    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    let eq_eval = eq_eval(builder, &out_subgroup, &in_subgroup, one, zero);
    builder.assign(&eval, eval * eq_eval);

    eval
}

pub fn evaluate_selector<C: Config>(
    builder: &mut Builder<C>,
    sel_type: &SelectorType<E>,
    evals: &Array<C, Ext<C::F, C::EF>>,
    out_point: &Array<C, Ext<C::F, C::EF>>,
    in_point: &Array<C, Ext<C::F, C::EF>>,
    opcode_proof: &ZKVMChipProofInputVariable<C>,
    offset_eq_id: usize,
) {
    let (expr, eval) = match sel_type {
        SelectorType::None => return,
        SelectorType::Whole(expr) => {
            let one = builder.constant(C::EF::ONE);
            let zero = builder.constant(C::EF::ZERO);
            (expr, eq_eval(builder, out_point, in_point, one, zero))
        }
        SelectorType::Prefix(_, expr) => (
            expr,
            eq_eval_less_or_equal_than(builder, opcode_proof, out_point, in_point),
        ),
        SelectorType::OrderedSparse32 {
            indices,
            expression,
        } => {
            let out_point_slice = out_point.slice(builder, 0, 5);
            let in_point_slice = in_point.slice(builder, 0, 5);
            let out_subgroup_eq = build_eq_x_r_vec_sequential(builder, &out_point_slice);
            let in_subgroup_eq = build_eq_x_r_vec_sequential(builder, &in_point_slice);

            let eval: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
            for idx in indices {
                let out_val = builder.get(&out_subgroup_eq, *idx);
                let in_val = builder.get(&in_subgroup_eq, *idx);
                builder.assign(&eval, eval + out_val * in_val);
            }

            let out_point_slice = out_point.slice(builder, 5, out_point.len());
            let in_point_slice = in_point.slice(builder, 5, in_point.len());

            let sel = eq_eval_less_or_equal_than(
                builder,
                opcode_proof,
                &out_point_slice,
                &in_point_slice,
            );
            builder.assign(&eval, eval * sel);

            (expression, eval)
        }
    };

    let Expression::StructuralWitIn(wit_id, _, _, _) = expr else {
        panic!("Wrong selector expression format");
    };
    let wit_id = *wit_id as usize + offset_eq_id;
    builder.set(evals, wit_id, eval);
}

pub fn get_rotation_points<C: Config>(
    builder: &mut Builder<C>,
    _num_vars: usize,
    point: &Array<C, Ext<C::F, C::EF>>,
) -> (Array<C, Ext<C::F, C::EF>>, Array<C, Ext<C::F, C::EF>>) {
    let left: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(point.len());
    let right: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(point.len());
    builder.range(0, 4).for_each(|idx_vec, builder| {
        let e = builder.get(point, idx_vec[0]);
        let dest_idx: Var<C::N> = builder.eval(idx_vec[0] + RVar::from(1));
        builder.set(&left, dest_idx, e);
        builder.set(&right, dest_idx, e);
    });

    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    builder.set(&right, 0, one);
    let r1 = builder.get(&right, 2);
    builder.set(&right, 2, one - r1);

    builder.range(5, point.len()).for_each(|idx_vec, builder| {
        let e = builder.get(point, idx_vec[0]);
        builder.set(&left, idx_vec[0], e);
        builder.set(&right, idx_vec[0], e);
    });

    (left, right)
}

pub fn evaluate_gkr_expression<C: Config>(
    builder: &mut Builder<C>,
    expr: &EvalExpression<E>,
    claims: &Array<C, PointAndEvalVariable<C>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
) -> PointAndEvalVariable<C> {
    match expr {
        EvalExpression::Zero => {
            let point = builder.get(claims, 0).point.clone();
            let eval: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
            PointAndEvalVariable { point, eval }
        }
        EvalExpression::Single(i) => builder.get(claims, *i).clone(),
        EvalExpression::Linear(i, c0, c1) => {
            let point = builder.get(claims, *i);

            let eval = point.eval.clone();
            let point = point.point.clone();

            let empty_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(0);
            let c0_eval = eval_ceno_expr_with_instance(
                builder, &empty_arr, &empty_arr, &empty_arr, &empty_arr, challenges, c0,
            );
            let c1_eval = eval_ceno_expr_with_instance(
                builder, &empty_arr, &empty_arr, &empty_arr, &empty_arr, challenges, c1,
            );

            builder.assign(&eval, eval * c0_eval + c1_eval);

            PointAndEvalVariable { point, eval }
        }
        EvalExpression::Partition(parts, indices) => {
            assert!(izip!(indices.iter(), indices.iter().skip(1)).all(|(a, b)| a.0 < b.0));
            let empty_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(0);
            let vars = indices
                .iter()
                .map(|(_, c)| {
                    eval_ceno_expr_with_instance(
                        builder, &empty_arr, &empty_arr, &empty_arr, &empty_arr, challenges, c,
                    )
                })
                .collect_vec();
            let vars_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(vars.len());
            for (i, e) in vars.iter().enumerate() {
                builder.set(&vars_arr, i, *e);
            }
            let parts = parts
                .iter()
                .map(|part| evaluate_gkr_expression(builder, part, claims, challenges))
                .collect_vec();

            assert_eq!(parts.len(), 1 << indices.len());

            // _debug
            // assert!(parts.iter().all(|part| part.point == parts[0].point));

            // FIXME: this is WRONG. we should use builder.dyn_array();
            let mut new_point: Vec<Ext<C::F, C::EF>> = vec![];
            builder
                .range(0, parts[0].point.fs.len())
                .for_each(|idx_vec, builder| {
                    let e = builder.get(&parts[0].point.fs, idx_vec[0]);
                    new_point.push(e);
                });
            for (index_in_point, c) in indices {
                let eval = eval_ceno_expr_with_instance(
                    builder, &empty_arr, &empty_arr, &empty_arr, &empty_arr, challenges, c,
                );
                new_point.insert(*index_in_point, eval);
            }

            let new_point_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(new_point.len());
            for (i, e) in new_point.iter().enumerate() {
                builder.set(&new_point_arr, i, *e);
            }
            let eq = build_eq_x_r_vec_sequential(builder, &vars_arr);

            let parts_arr: Array<C, PointAndEvalVariable<C>> = builder.dyn_array(parts.len());
            for (i, pt) in parts.iter().enumerate() {
                builder.set(&parts_arr, i, pt.clone());
            }

            let acc: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
            iter_zip!(builder, parts_arr, eq).for_each(|ptr_vec, builder| {
                let prt = builder.iter_ptr_get(&parts_arr, ptr_vec[0]);
                let eq_v = builder.iter_ptr_get(&eq, ptr_vec[1]);
                builder.assign(&acc, acc + prt.eval * eq_v);
            });

            PointAndEvalVariable {
                point: PointVariable { fs: new_point_arr },
                eval: acc,
            }
        }
    }
}

pub fn extract_claim_and_point<C: Config>(
    builder: &mut Builder<C>,
    layer: &Layer<E>,
    claims: &Array<C, PointAndEvalVariable<C>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    has_rotation: &Usize<C::N>,
) -> Array<C, ClaimAndPoint<C>> {
    let r_len: Usize<C::N> = Usize::Var(Var::uninit(builder));
    builder.assign(
        &r_len,
        has_rotation.clone() * Usize::from(3) + Usize::from(layer.out_sel_and_eval_exprs.len()),
    );

    let r = builder.dyn_array(r_len);

    layer
        .out_sel_and_eval_exprs
        .iter()
        .enumerate()
        .for_each(|(i, (_, out_evals))| {
            let evals = out_evals
                .iter()
                .map(|out_eval| {
                    let r = evaluate_gkr_expression(builder, out_eval, claims, challenges);
                    r.eval
                })
                .collect_vec();
            let evals_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(evals.len());
            for (j, e) in evals.iter().enumerate() {
                builder.set(&evals_arr, j, *e);
            }
            let point = out_evals.first().map(|out_eval| {
                let r = evaluate_gkr_expression(builder, out_eval, claims, challenges);
                r.point
            });

            if point.is_some() {
                builder.set(
                    &r,
                    i,
                    ClaimAndPoint {
                        evals: evals_arr,
                        has_point: Usize::from(1),
                        point: point.unwrap(),
                    },
                );
            } else {
                let pt = PointVariable {
                    fs: builder.dyn_array(0),
                };
                builder.set(
                    &r,
                    i,
                    ClaimAndPoint {
                        evals: evals_arr,
                        has_point: Usize::from(0),
                        point: pt,
                    },
                );
            }
        });

    r
}

pub fn generate_layer_challenges<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    n_challenges: usize,
) -> Array<C, Ext<C::F, C::EF>> {
    let r = builder.dyn_array(n_challenges + 2);

    let alpha = builder.get(challenges, 0);
    let beta = builder.get(challenges, 1);

    builder.set(&r, 0, alpha);
    builder.set(&r, 1, beta);

    transcript_observe_label(builder, challenger, b"layer challenge");
    let c = gen_alpha_pows(builder, challenger, Usize::from(n_challenges));

    for i in 0..n_challenges {
        let idx = i + 2;
        let e = builder.get(&c, i);
        builder.set(&r, idx, e);
    }

    r
}

pub fn verify_table_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    table_proof: &ZKVMChipProofInputVariable<C>,
    raw_pi: &Array<C, Array<C, Felt<C::F>>>,
    raw_pi_num_variables: &Array<C, Var<C::N>>,
    pi_evals: &Array<C, Ext<C::F, C::EF>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    vk: &VerifyingKey<E>,
    unipoly_extrapolator: &mut UniPolyExtrapolator<C>,
    poly_evaluator: &mut PolyEvaluator<C>,
) -> Array<C, Ext<C::F, C::EF>> {
    let cs = vk.get_cs();
    let tower_proof: &super::binding::TowerProofInputVariable<C> = &table_proof.tower_proof;

    let r_expected_rounds: Array<C, Usize<C::N>> =
        builder.dyn_array(cs.zkvm_v1_css.r_table_expressions.len() * 2);
    cs
        // only iterate r set, as read/write set round should match
        .zkvm_v1_css
        .r_table_expressions
        .iter()
        .enumerate()
        .for_each(|(idx, expr)| {
            let num_vars: Usize<C::N> = match expr.table_spec.len {
                Some(l) => Usize::from(ceil_log2(l)),
                None => {
                    let var_vec = expr
                        .table_spec
                        .structural_witins
                        .iter()
                        .map(|StructuralWitIn { .. }| table_proof.log2_num_instances.clone())
                        .collect::<Vec<Usize<C::N>>>();

                    max_usize_vec(builder, var_vec)
                }
            };

            builder.set(&r_expected_rounds, idx * 2, num_vars.clone());
            builder.set(&r_expected_rounds, idx * 2 + 1, num_vars.clone());
        });

    let lk_expected_rounds: Array<C, Usize<C::N>> =
        builder.dyn_array(cs.zkvm_v1_css.lk_table_expressions.len());
    cs.zkvm_v1_css
        .lk_table_expressions
        .iter()
        .enumerate()
        .for_each(|(idx, expr)| {
            let num_vars: Usize<C::N> = match expr.table_spec.len {
                Some(l) => Usize::from(ceil_log2(l)),
                None => {
                    let var_vec = expr
                        .table_spec
                        .structural_witins
                        .iter()
                        .map(|StructuralWitIn { .. }| table_proof.log2_num_instances.clone())
                        .collect::<Vec<Usize<C::N>>>();

                    max_usize_vec(builder, var_vec)
                }
            };

            builder.set(&lk_expected_rounds, idx, num_vars);
        });
    let expected_rounds = concat(builder, &r_expected_rounds, &lk_expected_rounds);
    let max_expected_rounds = max_usize_arr(builder, &expected_rounds);

    let num_fanin: Usize<C::N> = Usize::from(NUM_FANIN);
    let max_num_variables: Usize<C::N> = Usize::from(max_expected_rounds);
    let prod_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>> = concat(
        builder,
        &table_proof.record_r_out_evals,
        &table_proof.record_w_out_evals,
    );

    builder.cycle_tracker_start("verify tower proof");
    let (rt_tower, prod_point_and_eval, logup_p_point_and_eval, logup_q_point_and_eval) =
        verify_tower_proof(
            builder,
            challenger,
            prod_out_evals,
            &table_proof.record_lk_out_evals,
            expected_rounds,
            num_fanin,
            max_num_variables,
            tower_proof,
            unipoly_extrapolator,
        );
    builder.cycle_tracker_end("verify tower proof");

    builder.assert_usize_eq(
        logup_q_point_and_eval.len(),
        Usize::from(cs.zkvm_v1_css.lk_table_expressions.len()),
    );
    builder.assert_usize_eq(
        logup_p_point_and_eval.len(),
        Usize::from(cs.zkvm_v1_css.lk_table_expressions.len()),
    );
    builder.assert_usize_eq(
        prod_point_and_eval.len(),
        Usize::from(
            cs.zkvm_v1_css.r_table_expressions.len() + cs.zkvm_v1_css.w_table_expressions.len(),
        ),
    );

    // in table proof, we always skip same point sumcheck for now
    // as tower sumcheck batch product argument/logup in same length
    let _is_skip_same_point_sumcheck = true;

    // evaluate structural witness from verifier
    let set_table_exprs = cs
        .zkvm_v1_css
        .r_table_expressions
        .iter()
        .map(|r| &r.table_spec)
        .chain(
            cs.zkvm_v1_css
                .lk_table_expressions
                .iter()
                .map(|r| &r.table_spec),
        )
        .collect::<Vec<&SetTableSpec>>();
    let structural_witnesses_vec: Vec<Ext<C::F, C::EF>> = set_table_exprs
        .iter()
        .flat_map(|table_spec| {
            table_spec
                .structural_witins
                .iter()
                .map(
                    |StructuralWitIn {
                         offset,
                         multi_factor,
                         descending,
                         ..
                     }| {
                        // TODO: Remove modulo field prime
                        // OpenVM Config cannot automatically accept u32 exceeding its prime limit
                        // Use Babybear prime defined as p = 15 * 2^27 + 1
                        let babybear_prime: u32 = 2013265921;
                        let offset = if *offset > babybear_prime {
                            *offset - babybear_prime
                        } else {
                            *offset
                        };
                        let multi_factor = if *multi_factor > babybear_prime as usize {
                            *multi_factor - babybear_prime as usize
                        } else {
                            *multi_factor
                        };

                        eval_wellform_address_vec(
                            builder,
                            offset as u32,
                            multi_factor as u32,
                            &rt_tower.fs,
                            *descending,
                        )
                    },
                )
                .collect::<Vec<Ext<C::F, C::EF>>>()
        })
        .collect::<Vec<Ext<C::F, C::EF>>>();
    let structural_witnesses: Array<C, Ext<C::F, C::EF>> =
        builder.dyn_array(structural_witnesses_vec.len());
    structural_witnesses_vec
        .into_iter()
        .enumerate()
        .for_each(|(idx, e)| {
            builder.set(&structural_witnesses, idx, e);
        });

    let in_evals_len: Usize<C::N> = builder.eval(
        prod_point_and_eval.len() + logup_p_point_and_eval.len() + logup_q_point_and_eval.len(),
    );
    let in_evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(in_evals_len);
    builder
        .range(0, prod_point_and_eval.len())
        .for_each(|idx_vec, builder| {
            let e = builder.get(&prod_point_and_eval, idx_vec[0]).eval;
            builder.set(&in_evals, idx_vec[0], e);
        });
    builder
        .range(0, logup_p_point_and_eval.len())
        .for_each(|idx_vec, builder| {
            let p_e = builder.get(&logup_p_point_and_eval, idx_vec[0]).eval;
            let q_e = builder.get(&logup_q_point_and_eval, idx_vec[0]).eval;

            let p_idx: Usize<C::N> =
                builder.eval(prod_point_and_eval.len() + idx_vec[0] * Usize::from(2));
            let q_idx: Usize<C::N> = builder
                .eval(prod_point_and_eval.len() + idx_vec[0] * Usize::from(2) + Usize::from(1));

            builder.set(&in_evals, p_idx, p_e);
            builder.set(&in_evals, q_idx, q_e);
        });

    // verify records (degree = 1) statement, thus no sumcheck
    let expected_evals_vec: Vec<Ext<C::F, C::EF>> = interleave(
        &cs.zkvm_v1_css.r_table_expressions, // r
        &cs.zkvm_v1_css.w_table_expressions, // w
    )
    .map(|rw| &rw.expr)
    .chain(
        cs.zkvm_v1_css
            .lk_table_expressions
            .iter()
            .flat_map(|lk| vec![&lk.multiplicity, &lk.values]), // p, q
    )
    .enumerate()
    .map(|(_, expr)| {
        eval_ceno_expr_with_instance(
            builder,
            &table_proof.fixed_in_evals,
            &table_proof.wits_in_evals,
            &structural_witnesses,
            pi_evals,
            challenges,
            expr,
        )
    })
    .collect_vec();

    let expected_evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(expected_evals_vec.len());
    expected_evals_vec
        .into_iter()
        .enumerate()
        .for_each(|(idx, e)| {
            builder.set(&expected_evals, idx, e);
        });

    iter_zip!(builder, in_evals, expected_evals).for_each(|ptr_vec, builder| {
        let eval = builder.iter_ptr_get(&in_evals, ptr_vec[0]);
        let expected = builder.iter_ptr_get(&expected_evals, ptr_vec[1]);
        builder.assert_ext_eq(eval, expected);
    });

    // assume public io is tiny vector, so we evaluate it directly without PCS
    for &Instance(idx) in cs.instance_name_map().keys() {
        let poly = builder.get(raw_pi, idx);
        let poly_num_vars = builder.get(raw_pi_num_variables, idx);
        let eval_point = rt_tower.fs.slice(builder, 0, poly_num_vars);
        let expected_eval = poly_evaluator.evaluate_base_poly_at_point(builder, &poly, &eval_point);
        let eval = builder.get(&pi_evals, idx);

        builder.assert_ext_eq(eval, expected_eval);
    }

    rt_tower.fs
}
