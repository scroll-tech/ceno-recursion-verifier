use super::binding::{
    ZKVMOpcodeProofInputVariable, ZKVMProofInputVariable, ZKVMTableProofInputVariable,
};
use crate::arithmetics::{
    challenger_multi_observe, eval_ceno_expr_with_instance, print_ext_arr, print_felt_arr,
    PolyEvaluator, UniPolyExtrapolator,
};
use crate::e2e::SubcircuitParams;
use crate::tower_verifier::program::verify_tower_proof;
use crate::transcript::transcript_observe_label;
use crate::{
    arithmetics::{
        build_eq_x_r_vec_sequential, ceil_log2, concat, dot_product as ext_dot_product,
        eq_eval_less_or_equal_than, eval_wellform_address_vec, gen_alpha_pows, max_usize_arr,
        max_usize_vec, nested_product, next_pow2_instance_padding, product, sum as ext_sum,
    },
    tower_verifier::{binding::PointVariable, program::iop_verifier_state_verify},
};
use ceno_mle::expression::{Instance, StructuralWitIn};
use ceno_zkvm::{circuit_builder::SetTableSpec, scheme::verifier::ZKVMVerifier};
use ff_ext::BabyBearExt4;
use itertools::interleave;
use itertools::max;
use mpcs::{Basefold, BasefoldRSParams};
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::{
    duplex::DuplexChallengerVariable, CanObserveVariable, FeltChallenger,
};
use p3_field::{Field, FieldAlgebra};

type E = BabyBearExt4;
type Pcs = Basefold<E, BasefoldRSParams>;
const NUM_FANIN: usize = 2;
const MAINCONSTRAIN_SUMCHECK_BATCH_SIZE: usize = 3; // read/write/lookup
const SEL_DEGREE: usize = 2;

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

pub fn verify_zkvm_proof<C: Config>(
    builder: &mut Builder<C>,
    zkvm_proof_input: ZKVMProofInputVariable<C>,
    ceno_constraint_system: &ZKVMVerifier<E, Pcs>,
    proving_sequence: Vec<SubcircuitParams>,
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

    challenger_multi_observe(builder, &mut challenger, &zkvm_proof_input.fixed_commit);
    iter_zip!(builder, zkvm_proof_input.fixed_commit_trivial_commits).for_each(
        |ptr_vec, builder| {
            let trivial_cmt =
                builder.iter_ptr_get(&zkvm_proof_input.fixed_commit_trivial_commits, ptr_vec[0]);
            challenger_multi_observe(builder, &mut challenger, &trivial_cmt);
        },
    );
    challenger.observe(
        builder,
        zkvm_proof_input.fixed_commit_log2_max_codeword_size,
    );

    let zero_f: Felt<C::F> = builder.constant(C::F::ZERO);
    iter_zip!(builder, zkvm_proof_input.num_instances).for_each(|ptr_vec, builder| {
        let ns = builder.iter_ptr_get(&zkvm_proof_input.num_instances, ptr_vec[0]);
        let circuit_size = builder.get(&ns, 0);
        let num_var = builder.get(&ns, 1);

        challenger.observe(builder, circuit_size);
        challenger.observe(builder, zero_f);
        challenger.observe(builder, num_var);
        challenger.observe(builder, zero_f);
    });

    challenger_multi_observe(builder, &mut challenger, &zkvm_proof_input.witin_commit);

    iter_zip!(builder, zkvm_proof_input.witin_commit_trivial_commits).for_each(
        |ptr_vec, builder| {
            let trivial_cmt =
                builder.iter_ptr_get(&zkvm_proof_input.witin_commit_trivial_commits, ptr_vec[0]);
            challenger_multi_observe(builder, &mut challenger, &trivial_cmt);
        },
    );
    challenger.observe(
        builder,
        zkvm_proof_input.witin_commit_log2_max_codeword_size,
    );

    let alpha = challenger.sample_ext(builder);
    let beta = challenger.sample_ext(builder);

    let challenges: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(2);
    builder.set(&challenges, 0, alpha.clone());
    builder.set(&challenges, 1, beta.clone());

    let mut unipoly_extrapolator = UniPolyExtrapolator::new(builder);
    let mut poly_evaluator = PolyEvaluator::new(builder);

    let dummy_table_item = alpha.clone();
    let dummy_table_item_multiplicity: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    let mut rt_points: Vec<Array<C, Ext<C::F, C::EF>>> = Vec::with_capacity(proving_sequence.len());
    let mut evaluations: Vec<Array<C, Ext<C::F, C::EF>>> =
        Vec::with_capacity(2 * proving_sequence.len()); // witin + fixed thus *2

    for subcircuit_params in proving_sequence {
        if subcircuit_params.is_opcode {
            let opcode_proof = builder.get(
                &zkvm_proof_input.opcode_proofs,
                subcircuit_params.type_order_idx,
            );
            let id_f: Felt<C::F> =
                builder.constant(C::F::from_canonical_usize(subcircuit_params.id));
            challenger.observe(builder, id_f);

            builder.cycle_tracker_start("Verify opcode proof");
            let input_opening_point = verify_opcode_proof(
                builder,
                &mut challenger,
                &opcode_proof,
                &zkvm_proof_input.pi_evals,
                &challenges,
                &subcircuit_params,
                &ceno_constraint_system,
                &mut unipoly_extrapolator,
            );
            builder.cycle_tracker_end("Verify opcode proof");

            rt_points.push(input_opening_point);
            evaluations.push(opcode_proof.wits_in_evals);

            // getting the number of dummy padding item that we used in this opcode circuit
            let cs = ceno_constraint_system.vk.circuit_vks[&subcircuit_params.name].get_cs();
            let num_instances = subcircuit_params.num_instances;
            let num_lks = cs.lk_expressions.len();
            let num_padded_instance = next_pow2_instance_padding(num_instances) - num_instances;

            let new_multiplicity: Ext<C::F, C::EF> =
                builder.constant(C::EF::from_canonical_usize(num_lks * num_padded_instance));
            builder.assign(
                &dummy_table_item_multiplicity,
                dummy_table_item_multiplicity + new_multiplicity,
            );

            let record_r_out_evals_prod = nested_product(builder, &opcode_proof.record_r_out_evals);
            builder.assign(&prod_r, prod_r * record_r_out_evals_prod);

            let record_w_out_evals_prod = nested_product(builder, &opcode_proof.record_w_out_evals);
            builder.assign(&prod_w, prod_w * record_w_out_evals_prod);

            iter_zip!(builder, opcode_proof.record_lk_out_evals).for_each(|ptr_vec, builder| {
                let evals = builder.iter_ptr_get(&opcode_proof.record_lk_out_evals, ptr_vec[0]);
                let p1 = builder.get(&evals, 0);
                let p2 = builder.get(&evals, 1);
                let q1 = builder.get(&evals, 2);
                let q2 = builder.get(&evals, 3);

                builder.assign(&logup_sum, logup_sum + p1 * q1.inverse());
                builder.assign(&logup_sum, logup_sum + p2 * q2.inverse());
            });
        } else {
            let table_proof = builder.get(
                &zkvm_proof_input.table_proofs,
                subcircuit_params.type_order_idx,
            );
            let id_f: Felt<C::F> =
                builder.constant(C::F::from_canonical_usize(subcircuit_params.id));
            challenger.observe(builder, id_f);

            let input_opening_point = verify_table_proof(
                builder,
                &mut challenger,
                &table_proof,
                &zkvm_proof_input.raw_pi,
                &zkvm_proof_input.raw_pi_num_variables,
                &zkvm_proof_input.pi_evals,
                &challenges,
                &subcircuit_params,
                ceno_constraint_system,
                &mut unipoly_extrapolator,
                &mut poly_evaluator,
            );

            rt_points.push(input_opening_point);
            evaluations.push(table_proof.wits_in_evals);
            let cs = ceno_constraint_system.vk.circuit_vks[&subcircuit_params.name].get_cs();
            if cs.num_fixed > 0 {
                evaluations.push(table_proof.fixed_in_evals);
            }

            iter_zip!(builder, table_proof.record_lk_out_evals).for_each(|ptr_vec, builder| {
                let evals = builder.iter_ptr_get(&table_proof.record_lk_out_evals, ptr_vec[0]);
                let p1 = builder.get(&evals, 0);
                let p2 = builder.get(&evals, 1);
                let q1 = builder.get(&evals, 2);
                let q2 = builder.get(&evals, 3);
                builder.assign(
                    &logup_sum,
                    logup_sum - p1 * q1.inverse() - p2 * q2.inverse(),
                );
            });

            let record_w_out_evals_prod = nested_product(builder, &table_proof.record_w_out_evals);
            builder.assign(&prod_w, prod_w * record_w_out_evals_prod);
            let record_r_out_evals_prod = nested_product(builder, &table_proof.record_r_out_evals);
            builder.assign(&prod_r, prod_r * record_r_out_evals_prod);
        }
    }

    builder.assign(
        &logup_sum,
        logup_sum - dummy_table_item_multiplicity * dummy_table_item.inverse(),
    );

    /* TODO: MPCS
    PCS::batch_verify(
        &self.vk.vp,
        &vm_proof.num_instances,
        &rt_points,
        self.vk.fixed_commit.as_ref(),
        &vm_proof.witin_commit,
        &evaluations,
        &vm_proof.fixed_witin_opening_proof,
        &self.vk.circuit_num_polys,
        &mut transcript,
    )
    .map_err(ZKVMError::PCSError)?;
    */

    let empty_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(0);
    let initial_global_state = eval_ceno_expr_with_instance(
        builder,
        &empty_arr,
        &empty_arr,
        &empty_arr,
        &zkvm_proof_input.pi_evals,
        &challenges,
        &ceno_constraint_system.vk.initial_global_state_expr,
    );
    builder.assign(&prod_w, prod_w * initial_global_state);

    let finalize_global_state = eval_ceno_expr_with_instance(
        builder,
        &empty_arr,
        &empty_arr,
        &empty_arr,
        &zkvm_proof_input.pi_evals,
        &challenges,
        &ceno_constraint_system.vk.finalize_global_state_expr,
    );
    builder.assign(&prod_r, prod_r * finalize_global_state);

    /* TODO: Temporarily disable product check for missing subcircuits
        builder.assert_ext_eq(prod_r, prod_w);
    */
}

pub fn verify_opcode_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    opcode_proof: &ZKVMOpcodeProofInputVariable<C>,
    pi_evals: &Array<C, Ext<C::F, C::EF>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    subcircuit_params: &SubcircuitParams,
    cs: &ZKVMVerifier<E, Pcs>,
    unipoly_extrapolator: &mut UniPolyExtrapolator<C>,
) -> Array<C, Ext<C::F, C::EF>> {
    let cs = &cs.vk.circuit_vks[&subcircuit_params.name].cs;
    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    let r_len = cs.r_expressions.len();
    let w_len = cs.w_expressions.len();
    let lk_len = cs.lk_expressions.len();

    let num_batched = r_len + w_len + lk_len;
    let chip_record_alpha: Ext<C::F, C::EF> = builder.get(challenges, 0);

    let r_counts_per_instance: Usize<C::N> = Usize::from(r_len);
    let w_counts_per_instance: Usize<C::N> = Usize::from(w_len);
    let lk_counts_per_instance: Usize<C::N> = Usize::from(lk_len);
    let num_batched: Usize<C::N> = Usize::from(num_batched);

    let log2_r_count: Usize<C::N> = Usize::from(ceil_log2(r_len));
    let log2_w_count: Usize<C::N> = Usize::from(ceil_log2(w_len));
    let log2_lk_count: Usize<C::N> = Usize::from(ceil_log2(lk_len));

    let log2_num_instances = opcode_proof.log2_num_instances.clone();

    let tower_proof = &opcode_proof.tower_proof;

    let num_variables: Array<C, Usize<C::N>> = builder.dyn_array(num_batched);
    builder
        .range(0, num_variables.len())
        .for_each(|idx_vec, builder| {
            builder.set(&num_variables, idx_vec[0], log2_num_instances.clone());
        });

    let prod_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>> = concat(
        builder,
        &opcode_proof.record_r_out_evals,
        &opcode_proof.record_w_out_evals,
    );

    let num_fanin: Usize<C::N> = Usize::from(NUM_FANIN);
    let max_expr_len = *max([r_len, w_len, lk_len].iter()).unwrap();

    builder.cycle_tracker_start("verify tower proof for opcode");
    let (rt_tower, record_evals, logup_p_evals, logup_q_evals) = verify_tower_proof(
        builder,
        challenger,
        prod_out_evals,
        &opcode_proof.record_lk_out_evals,
        num_variables,
        num_fanin,
        log2_num_instances.clone(),
        tower_proof,
        unipoly_extrapolator,
    );
    builder.cycle_tracker_end("verify tower proof for opcode");

    let logup_p_eval = builder.get(&logup_p_evals, 0).eval;
    builder.assert_ext_eq(logup_p_eval, one);

    // verify zero statement (degree > 1) + sel sumcheck
    let rt = builder.get(&record_evals, 0);
    let num_rw_records: Usize<C::N> = builder.eval(r_counts_per_instance + w_counts_per_instance);
    builder.assert_usize_eq(record_evals.len(), num_rw_records.clone());

    let alpha_len = builder.eval(
        num_rw_records.clone()
            + lk_counts_per_instance
            + Usize::from(cs.assert_zero_sumcheck_expressions.len()),
    );
    transcript_observe_label(builder, challenger, b"combine subset evals");
    let alpha_pow = gen_alpha_pows(builder, challenger, alpha_len);

    // alpha_read * (out_r[rt] - 1) + alpha_write * (out_w[rt] - 1) + alpha_lk * (out_lk_q - chip_record_alpha)
    // + 0 // 0 come from zero check
    let claim_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let rw_logup_len: Usize<C::N> = builder.eval(num_rw_records.clone() + logup_q_evals.len());
    let alpha_rw_slice = alpha_pow.slice(builder, 0, num_rw_records.clone());
    iter_zip!(builder, alpha_rw_slice, record_evals).for_each(|ptr_vec, builder| {
        let alpha = builder.iter_ptr_get(&alpha_rw_slice, ptr_vec[0]);
        let eval = builder.iter_ptr_get(&record_evals, ptr_vec[1]);

        builder.assign(&claim_sum, claim_sum + alpha * (eval.eval - one));
    });
    let alpha_logup_slice = alpha_pow.slice(builder, num_rw_records.clone(), rw_logup_len);
    iter_zip!(builder, alpha_logup_slice, logup_q_evals).for_each(|ptr_vec, builder| {
        let alpha = builder.iter_ptr_get(&alpha_logup_slice, ptr_vec[0]);
        let eval = builder.iter_ptr_get(&logup_q_evals, ptr_vec[1]);
        builder.assign(
            &claim_sum,
            claim_sum + alpha * (eval.eval - chip_record_alpha),
        );
    });

    let log2_num_instances_var: Var<C::N> = RVar::from(log2_num_instances.clone()).variable();
    let log2_num_instances_f: Felt<C::F> = builder.unsafe_cast_var_to_felt(log2_num_instances_var);
    let max_non_lc_degree: usize = cs.max_non_lc_degree;
    let main_sel_subclaim_max_degree: Felt<C::F> = builder.constant(C::F::from_canonical_u32(
        SEL_DEGREE.max(max_non_lc_degree + 1) as u32,
    ));
    builder.cycle_tracker_start("main sumcheck");
    let (input_opening_point, expected_evaluation) = iop_verifier_state_verify(
        builder,
        challenger,
        &claim_sum,
        &opcode_proof.main_sel_sumcheck_proofs,
        log2_num_instances_f,
        main_sel_subclaim_max_degree,
        unipoly_extrapolator,
    );
    builder.cycle_tracker_end("main sumcheck");

    // sel(rt, t)
    let sel = eq_eval_less_or_equal_than(
        builder,
        challenger,
        opcode_proof,
        &input_opening_point,
        &rt.point.fs,
    );

    // derive r_records, w_records, lk_records from witness's evaluations
    let alpha_idx: Var<C::N> = builder.uninit();
    builder.assign(&alpha_idx, Usize::from(0));
    let empty_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(0);

    let rw_expressions_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    cs.r_expressions
        .iter()
        .chain(cs.w_expressions.iter())
        .for_each(|expr| {
            let e = eval_ceno_expr_with_instance(
                builder,
                &empty_arr,
                &opcode_proof.wits_in_evals,
                &empty_arr,
                pi_evals,
                challenges,
                expr,
            );
            let alpha = builder.get(&alpha_pow, alpha_idx);
            builder.assign(&alpha_idx, alpha_idx + Usize::from(1));
            builder.assign(&rw_expressions_sum, rw_expressions_sum + alpha * (e - one))
        });
    builder.assign(&rw_expressions_sum, rw_expressions_sum * sel);

    let lk_expressions_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    cs.lk_expressions.iter().for_each(|expr| {
        let e = eval_ceno_expr_with_instance(
            builder,
            &empty_arr,
            &opcode_proof.wits_in_evals,
            &empty_arr,
            pi_evals,
            challenges,
            expr,
        );
        let alpha = builder.get(&alpha_pow, alpha_idx);
        builder.assign(&alpha_idx, alpha_idx + Usize::from(1));
        builder.assign(
            &lk_expressions_sum,
            lk_expressions_sum + alpha * (e - chip_record_alpha),
        )
    });
    builder.assign(&lk_expressions_sum, lk_expressions_sum * sel);

    let zero_expressions_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    cs.assert_zero_sumcheck_expressions.iter().for_each(|expr| {
        // evaluate zero expression by all wits_in_evals because they share the unique input_opening_point opening
        let e = eval_ceno_expr_with_instance(
            builder,
            &empty_arr,
            &opcode_proof.wits_in_evals,
            &empty_arr,
            pi_evals,
            challenges,
            expr,
        );
        let alpha = builder.get(&alpha_pow, alpha_idx);
        builder.assign(&alpha_idx, alpha_idx + Usize::from(1));
        builder.assign(&zero_expressions_sum, zero_expressions_sum + alpha * e);
    });
    builder.assign(&zero_expressions_sum, zero_expressions_sum * sel);

    let computed_eval: Ext<C::F, C::EF> =
        builder.eval(rw_expressions_sum + lk_expressions_sum + zero_expressions_sum);
    builder.assert_ext_eq(computed_eval, expected_evaluation);

    // verify zero expression (degree = 1) statement, thus no sumcheck
    cs.assert_zero_expressions.iter().for_each(|expr| {
        let e = eval_ceno_expr_with_instance(
            builder,
            &empty_arr,
            &opcode_proof.wits_in_evals,
            &empty_arr,
            pi_evals,
            challenges,
            expr,
        );
        builder.assert_ext_eq(e, zero);
    });

    input_opening_point
}

pub fn verify_table_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    table_proof: &ZKVMTableProofInputVariable<C>,
    raw_pi: &Array<C, Array<C, Felt<C::F>>>,
    raw_pi_num_variables: &Array<C, Var<C::N>>,
    pi_evals: &Array<C, Ext<C::F, C::EF>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    subcircuit_params: &SubcircuitParams,
    cs: &ZKVMVerifier<E, Pcs>,
    unipoly_extrapolator: &mut UniPolyExtrapolator<C>,
    poly_evaluator: &mut PolyEvaluator<C>,
) -> Array<C, Ext<C::F, C::EF>> {
    let cs = cs.vk.circuit_vks[&subcircuit_params.name].get_cs();
    let tower_proof: &super::binding::TowerProofInputVariable<C> = &table_proof.tower_proof;

    let r_expected_rounds: Array<C, Usize<C::N>> =
        builder.dyn_array(cs.r_table_expressions.len() * 2);
    cs
        // only iterate r set, as read/write set round should match
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
        builder.dyn_array(cs.lk_table_expressions.len());
    cs.lk_table_expressions
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
        Usize::from(cs.lk_table_expressions.len()),
    );
    builder.assert_usize_eq(
        logup_p_point_and_eval.len(),
        Usize::from(cs.lk_table_expressions.len()),
    );
    builder.assert_usize_eq(
        prod_point_and_eval.len(),
        Usize::from(cs.r_table_expressions.len() + cs.w_table_expressions.len()),
    );

    // in table proof, we always skip same point sumcheck for now
    // as tower sumcheck batch product argument/logup in same length
    let _is_skip_same_point_sumcheck = true;

    // evaluate structural witness from verifier
    let set_table_exprs = cs
        .r_table_expressions
        .iter()
        .map(|r| &r.table_spec)
        .chain(cs.lk_table_expressions.iter().map(|r| &r.table_spec))
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
    interleave(
        &cs.r_table_expressions, // r
        &cs.w_table_expressions, // w
    )
    .map(|rw| &rw.expr)
    .chain(
        cs.lk_table_expressions
            .iter()
            .flat_map(|lk| vec![&lk.multiplicity, &lk.values]), // p, q
    )
    .enumerate()
    .for_each(|(idx, expr)| {
        let e = eval_ceno_expr_with_instance(
            builder,
            &table_proof.fixed_in_evals,
            &table_proof.wits_in_evals,
            &structural_witnesses,
            pi_evals,
            challenges,
            expr,
        );

        let expected_evals = builder.get(&in_evals, idx);
        builder.assert_ext_eq(e, expected_evals);
    });

    // assume public io is tiny vector, so we evaluate it directly without PCS
    for &Instance(idx) in cs.instance_name_map.keys() {
        let poly = builder.get(raw_pi, idx);
        let poly_num_vars = builder.get(raw_pi_num_variables, idx);
        let eval_point = rt_tower.fs.slice(builder, 0, poly_num_vars);
        let expected_eval = poly_evaluator.evaluate_base_poly_at_point(builder, &poly, &eval_point);
        let eval = builder.get(&pi_evals, idx);
        builder.assert_ext_eq(eval, expected_eval);
    }

    rt_tower.fs
}
