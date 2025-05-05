use super::binding::{
    ZKVMOpcodeProofInputVariable, ZKVMProofInputVariable, ZKVMTableProofInputVariable,
};
use crate::tests::SubcircuitParams;
use crate::tower_verifier::program::verify_tower_proof;
use crate::transcript::transcript_observe_label;
use crate::{
    arithmetics::{
        build_eq_x_r_vec_sequential, ceil_log2, concat, dot_product as ext_dot_product,
        eq_eval_less_or_equal_than, eval_ceno_expr_with_instance, eval_wellform_address_vec,
        gen_alpha_pows, max_usize_arr, max_usize_vec, next_pow2_instance_padding,
        product, sum as ext_sum,
    },
    tower_verifier::{
        binding::{PointVariable, TowerVerifierInputVariable},
        program::iop_verifier_state_verify,
    },
};
use ceno_zkvm::circuit_builder::SetTableSpec;
use itertools::interleave;
use itertools::max;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::{
        duplex::DuplexChallengerVariable, CanObserveVariable, FeltChallenger,
    };
use p3_field::FieldAlgebra;
use ceno_zkvm::{expression::StructuralWitIn, scheme::verifier::ZKVMVerifier};
use ff_ext::BabyBearExt4;
use mpcs::{Basefold, BasefoldRSParams};

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
        iter_zip!(builder, v).for_each(|inner_ptr_vec, builder| {
            let f = builder.iter_ptr_get(&v, inner_ptr_vec[0]);
            challenger.observe(builder, f);
        })
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
    
    iter_zip!(builder, zkvm_proof_input.fixed_commit).for_each(|ptr_vec, builder| {
        let f = builder.iter_ptr_get(&zkvm_proof_input.fixed_commit, ptr_vec[0]);
        challenger.observe(builder, f);
    });
    iter_zip!(builder, zkvm_proof_input.fixed_commit_trivial_commits).for_each(|ptr_vec, builder| {
        let trivial_cmt = builder.iter_ptr_get(&zkvm_proof_input.fixed_commit_trivial_commits, ptr_vec[0]);
        iter_zip!(builder, trivial_cmt).for_each(|t_ptr_vec, builder| {
            let f = builder.iter_ptr_get(&trivial_cmt, t_ptr_vec[0]);
            challenger.observe(builder, f);
        });
    });
    challenger.observe(builder, zkvm_proof_input.fixed_commit_log2_max_codeword_size);

    iter_zip!(builder, zkvm_proof_input.num_instances).for_each(|ptr_vec, builder| {
        let ns = builder.iter_ptr_get(&zkvm_proof_input.num_instances, ptr_vec[0]);
        let circuit_size = builder.get(&ns, 0);
        let num_var = builder.get(&ns, 1);
        challenger.observe(builder, circuit_size);
        challenger.observe(builder, num_var);
    });

    iter_zip!(builder, zkvm_proof_input.witin_commit).for_each(|ptr_vec, builder| {
        let f = builder.iter_ptr_get(&zkvm_proof_input.witin_commit, ptr_vec[0]);
        challenger.observe(builder, f);
    });
    iter_zip!(builder, zkvm_proof_input.witin_commit_trivial_commits).for_each(|ptr_vec, builder| {
        let trivial_cmt = builder.iter_ptr_get(&zkvm_proof_input.witin_commit_trivial_commits, ptr_vec[0]);
        iter_zip!(builder, trivial_cmt).for_each(|t_ptr_vec, builder| {
            let f = builder.iter_ptr_get(&trivial_cmt, t_ptr_vec[0]);
            challenger.observe(builder, f);
        });
    });
    challenger.observe(builder, zkvm_proof_input.witin_commit_log2_max_codeword_size);

    let alpha = challenger.sample_ext(builder);
    let beta = challenger.sample_ext(builder);

    let challenges: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(2);
    builder.set(&challenges, 0, alpha.clone());
    builder.set(&challenges, 1, beta.clone());

    let dummy_table_item = alpha.clone();
    let dummy_table_item_multiplicity: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    for subcircuit_params in proving_sequence {
        if subcircuit_params.is_opcode {
            let opcode_proof = builder.get(&zkvm_proof_input.opcode_proofs, subcircuit_params.type_order_idx);
            let id_f: Felt<C::F> = builder.constant(C::F::from_canonical_usize(subcircuit_params.id));
            challenger.observe(builder, id_f);

            verify_opcode_proof(
                builder,
                &mut challenger,
                &opcode_proof,
                &zkvm_proof_input.pi_evals,
                &challenges,
                &subcircuit_params,
                &ceno_constraint_system,
            );

            let cs = ceno_constraint_system.vk.circuit_vks[&subcircuit_params.name].get_cs();
            let num_lks = cs.lk_expressions.len();

            let num_instances = subcircuit_params.num_instances;
            let num_padded_lks_per_instance = next_pow2_instance_padding(num_lks) - num_lks;
            let num_padded_instance = next_pow2_instance_padding(num_instances) - num_instances;
            let new_multiplicity: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_usize(
                num_padded_lks_per_instance * num_instances
                    + num_lks.next_power_of_two() * num_padded_instance,
            ));

            builder.assign(
                &dummy_table_item_multiplicity,
                dummy_table_item_multiplicity + new_multiplicity,
            );

            let record_r_out_evals_prod = product(builder, &opcode_proof.record_r_out_evals);
            builder.assign(&prod_r, prod_r * record_r_out_evals_prod);

            let record_w_out_evals_prod = product(builder, &opcode_proof.record_w_out_evals);
            builder.assign(&prod_w, prod_w * record_w_out_evals_prod);

            builder.assign(
                &logup_sum,
                logup_sum + opcode_proof.lk_p1_out_eval * opcode_proof.lk_q1_out_eval.inverse(),
            );
            builder.assign(
                &logup_sum,
                logup_sum + opcode_proof.lk_p2_out_eval * opcode_proof.lk_q2_out_eval.inverse(),
            );
        } else {
            let table_proof =
                builder.get(&zkvm_proof_input.table_proofs, subcircuit_params.type_order_idx);
            let id_f: Felt<C::F> = builder.constant(C::F::from_canonical_usize(subcircuit_params.id));
            challenger.observe(builder, id_f);

            verify_table_proof(
                builder,
                &mut challenger,
                &table_proof,
                &zkvm_proof_input.raw_pi,
                &zkvm_proof_input.raw_pi_num_variables,
                &zkvm_proof_input.pi_evals,
                &challenges,
                &subcircuit_params,
                ceno_constraint_system,
            );

            let step = C::N::from_canonical_usize(4);
            builder
                .range_with_step(0, table_proof.lk_out_evals.len(), step)
                .for_each(|idx_vec, builder| {
                    let p2_idx: Usize<C::N> = builder.eval(idx_vec[0] + RVar::from(1));
                    let q1_idx: Usize<C::N> = builder.eval(p2_idx.clone() + RVar::from(1));
                    let q2_idx: Usize<C::N> = builder.eval(q1_idx.clone() + RVar::from(1));

                    let p1 = builder.get(&table_proof.lk_out_evals, idx_vec[0]);
                    let p2 = builder.get(&table_proof.lk_out_evals, p2_idx);
                    let q1 = builder.get(&table_proof.lk_out_evals, q1_idx);
                    let q2 = builder.get(&table_proof.lk_out_evals, q2_idx);

                    builder.assign(
                        &logup_sum,
                        logup_sum - p1 * q1.inverse() - p2 * q2.inverse(),
                    );
                });

            let w_out_evals_prod = product(builder, &table_proof.w_out_evals);
            builder.assign(&prod_w, prod_w * w_out_evals_prod);
            let r_out_evals_prod = product(builder, &table_proof.r_out_evals);
            builder.assign(&prod_r, prod_r * r_out_evals_prod);
        }
    }

    builder.assign(
        &logup_sum,
        logup_sum - dummy_table_item_multiplicity * dummy_table_item.inverse(),
    );

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

    // builder.assert_ext_eq(prod_r, prod_w);
}

pub fn verify_opcode_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    opcode_proof: &ZKVMOpcodeProofInputVariable<C>,
    pi_evals: &Array<C, Ext<C::F, C::EF>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    subcircuit_params: &SubcircuitParams,
    cs: &ZKVMVerifier<E, Pcs>,
) {
    let cs = &cs.vk.circuit_vks[&subcircuit_params.name].cs;
    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    let r_len = cs.r_expressions.len();
    let w_len = cs.w_expressions.len();
    let lk_len = cs.lk_expressions.len();

    let max_expr_len = *max([r_len, w_len, lk_len].iter()).unwrap();

    let r_counts_per_instance: Usize<C::N> = Usize::from(r_len);
    let w_counts_per_instance: Usize<C::N> = Usize::from(w_len);
    let lk_counts_per_instance: Usize<C::N> = Usize::from(lk_len);

    let log2_r_count: Usize<C::N> = Usize::from(ceil_log2(r_len));
    let log2_w_count: Usize<C::N> = Usize::from(ceil_log2(w_len));
    let log2_lk_count: Usize<C::N> = Usize::from(ceil_log2(lk_len));
    let log2_num_instances = opcode_proof.log2_num_instances.clone();

    let num_variables: Array<C, Usize<C::N>> = builder.dyn_array(3);
    let num_variables_r: Usize<C::N> =
        builder.eval(log2_num_instances.clone() + log2_r_count.clone());
    builder.set(&num_variables, 0, num_variables_r);
    let num_variables_w: Usize<C::N> =
        builder.eval(log2_num_instances.clone() + log2_w_count.clone());
    builder.set(&num_variables, 1, num_variables_w);
    let num_variables_lk: Usize<C::N> =
        builder.eval(log2_num_instances.clone() + log2_lk_count.clone());
    builder.set(&num_variables, 2, num_variables_lk);
    let max_num_variables: Usize<C::N> =
        builder.eval(log2_num_instances.clone() + Usize::from(ceil_log2(max_expr_len)));
    let tower_proof = &opcode_proof.tower_proof;

    let num_proofs = tower_proof.proofs.len();
    let num_prod_specs = tower_proof.prod_specs_eval.len();
    let num_logup_specs = tower_proof.logup_specs_eval.len();
    let num_fanin: Usize<C::N> = Usize::from(NUM_FANIN);

    let prod_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>> = builder.dyn_array(2);
    builder.set(&prod_out_evals, 0, opcode_proof.record_r_out_evals.clone());
    builder.set(&prod_out_evals, 1, opcode_proof.record_w_out_evals.clone());

    let logup_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>> = builder.dyn_array(1);
    let logup_inner_evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(4);
    builder.set(&logup_inner_evals, 0, opcode_proof.lk_p1_out_eval);
    builder.set(&logup_inner_evals, 1, opcode_proof.lk_p2_out_eval);
    builder.set(&logup_inner_evals, 2, opcode_proof.lk_q1_out_eval);
    builder.set(&logup_inner_evals, 3, opcode_proof.lk_q2_out_eval);
    builder.set(&logup_out_evals, 0, logup_inner_evals);

    let (rt_tower, record_evals, logup_p_evals, logup_q_evals) = verify_tower_proof(
        builder,
        challenger,
        TowerVerifierInputVariable {
            prod_out_evals,
            logup_out_evals,
            num_variables,
            num_fanin,
            num_proofs,
            num_prod_specs,
            num_logup_specs,
            max_num_variables,
            proofs: tower_proof.proofs.clone(),
            prod_specs_eval: tower_proof.prod_specs_eval.clone(),
            logup_specs_eval: tower_proof.logup_specs_eval.clone(),
        },
    );
    let rt_non_lc_sumcheck: Array<C, Ext<C::F, C::EF>> =
        rt_tower
            .fs
            .clone()
            .slice(builder, 0, log2_num_instances.clone());

    builder.assert_usize_eq(record_evals.len(), Usize::from(2));
    builder.assert_usize_eq(logup_q_evals.len(), Usize::from(1));
    builder.assert_usize_eq(logup_p_evals.len(), Usize::from(1));

    let logup_p_eval = builder.get(&logup_p_evals, 0).eval;
    builder.assert_ext_eq(logup_p_eval, one);

    let [rt_r, rt_w, rt_lk]: [Array<C, Ext<C::F, C::EF>>; 3] = [
        builder.get(&record_evals, 0).point.fs,
        builder.get(&record_evals, 1).point.fs,
        builder.get(&logup_q_evals, 0).point.fs,
    ];

    let zero_sumcheck_expr_len: usize = cs.assert_zero_sumcheck_expressions.len();

    let alpha_len = MAINCONSTRAIN_SUMCHECK_BATCH_SIZE + zero_sumcheck_expr_len;
    let alpha_len: Usize<C::N> = Usize::from(alpha_len);
    transcript_observe_label(builder, challenger, b"combine subset evals");
    let alpha_pow = gen_alpha_pows(builder, challenger, alpha_len);

    let [alpha_read, alpha_write, alpha_lk]: [Ext<C::F, C::EF>; 3] = [
        builder.get(&alpha_pow, 0),
        builder.get(&alpha_pow, 1),
        builder.get(&alpha_pow, 2),
    ];

    // alpha_read * (out_r[rt] - 1) + alpha_write * (out_w[rt] - 1) + alpha_lk * (out_lk_q - chip_record_alpha)
    // + 0 // 0 come from zero check
    let claim_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let record_eval_0 = builder.get(&record_evals, 0).eval;
    let record_eval_1 = builder.get(&record_evals, 1).eval;
    let logup_q_eval_0 = builder.get(&logup_q_evals, 0).eval;
    let alpha = builder.get(challenges, 0);

    builder.assign(
        &claim_sum,
        alpha_read * (record_eval_0 - one)
            + alpha_write * (record_eval_1 - one)
            + alpha_lk * (logup_q_eval_0 - alpha),
    );

    let log2_num_instances_var: Var<C::N> = RVar::from(log2_num_instances.clone()).variable();
    let log2_num_instances_f: Felt<C::F> = builder.unsafe_cast_var_to_felt(log2_num_instances_var);

    let max_non_lc_degree: usize = cs.max_non_lc_degree;
    let main_sel_subclaim_max_degree: Felt<C::F> = builder.constant(C::F::from_canonical_u32(
        SEL_DEGREE.max(max_non_lc_degree + 1) as u32,
    ));

    let main_sel_subclaim = iop_verifier_state_verify(
        builder,
        challenger,
        &claim_sum,
        &opcode_proof.main_sel_sumcheck_proofs,
        log2_num_instances_f,
        main_sel_subclaim_max_degree,
    );

    let input_opening_point = PointVariable {
        fs: main_sel_subclaim.0,
    };

    let rt_r_eq = rt_r.slice(builder, 0, log2_r_count.clone());
    let eq_r = build_eq_x_r_vec_sequential(builder, &rt_r_eq);
    let rt_w_eq = rt_w.slice(builder, 0, log2_w_count.clone());
    let eq_w = build_eq_x_r_vec_sequential(builder, &rt_w_eq);
    let rt_lk_eq = rt_lk.slice(builder, 0, log2_lk_count.clone());
    let eq_lk = build_eq_x_r_vec_sequential(builder, &rt_lk_eq);

    let rt_r_eq_less = rt_r.slice(builder, log2_r_count.clone(), rt_r.len());
    let rt_w_eq_less = rt_w.slice(builder, log2_w_count.clone(), rt_w.len());
    let rt_lk_eq_less = rt_lk.slice(builder, log2_lk_count.clone(), rt_lk.len());

    let sel_r = eq_eval_less_or_equal_than(
        builder,
        challenger,
        opcode_proof,
        &input_opening_point.fs,
        &rt_r_eq_less,
    );
    let sel_w = eq_eval_less_or_equal_than(
        builder,
        challenger,
        opcode_proof,
        &input_opening_point.fs,
        &rt_w_eq_less,
    );
    let sel_lk = eq_eval_less_or_equal_than(
        builder,
        challenger,
        opcode_proof,
        &input_opening_point.fs,
        &rt_lk_eq_less,
    );

    let sel_non_lc_zero_sumcheck: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    let zero_sumcheck_expressions_len = RVar::from(cs.assert_zero_sumcheck_expressions.len());
    builder
        .if_ne(zero_sumcheck_expressions_len, RVar::from(0))
        .then(|builder| {
            let sel_sumcheck = eq_eval_less_or_equal_than(
                builder,
                challenger,
                opcode_proof,
                &input_opening_point.fs,
                &rt_non_lc_sumcheck,
            );
            builder.assign(&sel_non_lc_zero_sumcheck, sel_sumcheck);
        });

    let r_records_slice =
        opcode_proof
            .r_records_in_evals
            .slice(builder, 0, r_counts_per_instance.clone());
    let eq_r_slice = eq_r.slice(builder, 0, r_counts_per_instance.clone());
    let eq_r_rest_slice = eq_r.slice(builder, r_counts_per_instance.clone(), eq_r.len());
    let r_prod = ext_dot_product(builder, &r_records_slice, &eq_r_slice);
    let eq_r_rest_sum = ext_sum(builder, &eq_r_rest_slice);
    let r_eval: Ext<C::F, C::EF> =
        builder.eval(alpha_read * sel_r * (r_prod + eq_r_rest_sum - one));

    let w_records_slice =
        opcode_proof
            .w_records_in_evals
            .slice(builder, 0, w_counts_per_instance.clone());
    let eq_w_slice = eq_w.slice(builder, 0, w_counts_per_instance.clone());
    let eq_w_rest_slice = eq_w.slice(builder, w_counts_per_instance.clone(), eq_w.len());
    let w_prod = ext_dot_product(builder, &w_records_slice, &eq_w_slice);
    let eq_w_rest_sum = ext_sum(builder, &eq_w_rest_slice);
    let w_eval: Ext<C::F, C::EF> =
        builder.eval(alpha_write * sel_w * (w_prod + eq_w_rest_sum - one));

    let lk_records_slice =
        opcode_proof
            .lk_records_in_evals
            .slice(builder, 0, lk_counts_per_instance.clone());
    let eq_lk_slice = eq_lk.slice(builder, 0, lk_counts_per_instance.clone());
    let eq_lk_rest_slice = eq_lk.slice(builder, lk_counts_per_instance.clone(), eq_lk.len());
    let lk_prod = ext_dot_product(builder, &lk_records_slice, &eq_lk_slice);
    let eq_lk_rest_sum = ext_sum(builder, &eq_lk_rest_slice);
    let lk_eval: Ext<C::F, C::EF> =
        builder.eval(alpha_lk * sel_lk * (lk_prod + alpha * (eq_lk_rest_sum - one)));

    let computed_eval: Ext<C::F, C::EF> = builder.eval(r_eval + w_eval + lk_eval);
    let empty_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(0);

    // sel(rt_non_lc_sumcheck, main_sel_eval_point) * \sum_j (alpha{j} * expr(main_sel_eval_point))
    let sel_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let alpha_pow_sel_sum = alpha_pow.slice(builder, 3, alpha_pow.len());
    for i in 0..cs.assert_zero_sumcheck_expressions.len() {
        let expr = &cs.assert_zero_sumcheck_expressions[i];
        let al = builder.get(&alpha_pow_sel_sum, i);

        let expr_eval = eval_ceno_expr_with_instance(
            builder,
            &empty_arr,
            &opcode_proof.wits_in_evals,
            &empty_arr,
            pi_evals,
            challenges,
            expr
        );

        builder.assign(&sel_sum, sel_sum + al * expr_eval);
    }

    builder.assign(
        &computed_eval,
        computed_eval + sel_sum * sel_non_lc_zero_sumcheck,
    );
    // builder.assert_ext_eq(computed_eval, expected_evaluation);

    // verify records (degree = 1) statement, thus no sumcheck
    let r_records = &opcode_proof
        .r_records_in_evals
        .slice(builder, 0, r_counts_per_instance);
    let w_records = &opcode_proof
        .w_records_in_evals
        .slice(builder, 0, w_counts_per_instance);
    let lk_records = &opcode_proof
        .lk_records_in_evals
        .slice(builder, 0, lk_counts_per_instance);

    let _ = &cs.r_expressions.iter().enumerate().for_each(|(idx, expr)| {
        let expected_eval = builder.get(&r_records, idx);
        let e = eval_ceno_expr_with_instance(
            builder,
            &empty_arr,
            &opcode_proof.wits_in_evals,
            &empty_arr,
            pi_evals,
            challenges,
            expr,
        );

        builder.assert_ext_eq(e, expected_eval);
    });

    let _ = &cs.w_expressions.iter().enumerate().for_each(|(idx, expr)| {
        let expected_eval = builder.get(&w_records, idx);
        let e = eval_ceno_expr_with_instance(
            builder,
            &empty_arr,
            &opcode_proof.wits_in_evals,
            &empty_arr,
            pi_evals,
            challenges,
            expr,
        );

        builder.assert_ext_eq(e, expected_eval);
    });

    let _ = &cs
        .lk_expressions
        .iter()
        .enumerate()
        .for_each(|(idx, expr)| {
            let expected_eval = builder.get(&lk_records, idx);
            let e = eval_ceno_expr_with_instance(
                builder,
                &empty_arr,
                &opcode_proof.wits_in_evals,
                &empty_arr,
                pi_evals,
                challenges,
                expr,
            );

            builder.assert_ext_eq(e, expected_eval);
        });

    cs.assert_zero_expressions
        .iter()
        .enumerate()
        .for_each(|(_idx, expr)| {
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

    // TODO:
    // PCS::simple_batch_verify(
    //     vp,
    //     &proof.wits_commit,
    //     &input_opening_point,
    //     &proof.wits_in_evals,
    //     &proof.wits_opening_proof,
    //     transcript,
    // )
}

pub fn verify_table_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    table_proof: &ZKVMTableProofInputVariable<C>,
    _raw_pi: &Array<C, Array<C, Felt<C::F>>>,
    _raw_pi_num_variables: &Array<C, Var<C::N>>,
    pi_evals: &Array<C, Ext<C::F, C::EF>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    subcircuit_params: &SubcircuitParams,
    cs: &ZKVMVerifier<E, Pcs>,
) {
    let cs = cs.vk.circuit_vks[&subcircuit_params.name].get_cs();
    let tower_proof = &table_proof.tower_proof;

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
                        .map(|StructuralWitIn { .. }| {
                            table_proof.log2_num_instances.clone()
                        })
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
                        .map(|StructuralWitIn { .. }| {
                            table_proof.log2_num_instances.clone()
                        })
                        .collect::<Vec<Usize<C::N>>>();

                    max_usize_vec(builder, var_vec)
                }
            };

            builder.set(&lk_expected_rounds, idx, num_vars);
        });
    let expected_rounds = concat(builder, &r_expected_rounds, &lk_expected_rounds);
    let max_expected_rounds = max_usize_arr(builder, &expected_rounds);

    let prod_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>> =
        builder.dyn_array(table_proof.r_out_evals.len());
    builder
        .range_with_step(
            0,
            table_proof.r_out_evals.len().clone(),
            C::N::from_canonical_usize(2),
        )
        .for_each(|idx_vec, builder| {
            let r2_idx: Usize<C::N> = builder.eval(idx_vec[0] + Usize::from(1));
            let r1 = builder.get(&table_proof.r_out_evals, idx_vec[0]);
            let r2 = builder.get(&table_proof.r_out_evals, r2_idx.clone());
            let w1 = builder.get(&table_proof.w_out_evals, idx_vec[0]);
            let w2 = builder.get(&table_proof.w_out_evals, r2_idx.clone());

            let r_vec: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(2);
            let w_vec: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(2);

            builder.set(&r_vec, 0, r1);
            builder.set(&r_vec, 1, r2);
            builder.set(&w_vec, 0, w1);
            builder.set(&w_vec, 1, w2);

            builder.set(&prod_out_evals, idx_vec[0], r_vec);
            builder.set(&prod_out_evals, r2_idx, w_vec);
        });

    let logup_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>> =
        builder.dyn_array(table_proof.compressed_lk_out_len.clone());
    builder
        .range(0, logup_out_evals.len())
        .for_each(|idx_vec, builder| {
            let lk_vec: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(4);
            let lk2_idx: Usize<C::N> = builder.eval(idx_vec[0] + Usize::from(1));
            let lk3_idx: Usize<C::N> = builder.eval(lk2_idx.clone() + Usize::from(1));
            let lk4_idx: Usize<C::N> = builder.eval(lk3_idx.clone() + Usize::from(1));

            let lk1 = builder.get(&table_proof.lk_out_evals, idx_vec[0]);
            let lk2 = builder.get(&table_proof.lk_out_evals, lk2_idx);
            let lk3 = builder.get(&table_proof.lk_out_evals, lk3_idx);
            let lk4 = builder.get(&table_proof.lk_out_evals, lk4_idx);

            builder.set(&lk_vec, 0, lk1);
            builder.set(&lk_vec, 1, lk2);
            builder.set(&lk_vec, 2, lk3);
            builder.set(&lk_vec, 3, lk4);

            builder.set(&logup_out_evals, idx_vec[0], lk_vec);
        });

    let num_fanin: Usize<C::N> = Usize::from(NUM_FANIN);
    let num_proofs: Usize<C::N> = tower_proof.proofs.len();
    let num_prod_specs: Usize<C::N> = tower_proof.prod_specs_eval.len();
    let num_logup_specs: Usize<C::N> = tower_proof.logup_specs_eval.len();
    let max_num_variables: Usize<C::N> = Usize::from(max_expected_rounds);

    let (rt_tower, prod_point_and_eval, logup_p_point_and_eval, logup_q_point_and_eval) =
        verify_tower_proof(
            builder,
            challenger,
            TowerVerifierInputVariable {
                prod_out_evals,
                logup_out_evals,
                num_variables: expected_rounds,
                num_fanin,
                num_proofs,
                num_prod_specs,
                num_logup_specs,
                max_num_variables,
                proofs: tower_proof.proofs.clone(),
                prod_specs_eval: tower_proof.prod_specs_eval.clone(),
                logup_specs_eval: tower_proof.logup_specs_eval.clone(),
            },
        );

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

    // TODO: Current Ceno verifier specification
    // in table proof, we always skip same point sumcheck for now
    // as tower sumcheck batch product argument/logup in same length
    let _is_skip_same_point_sumcheck = true;

    let input_opening_point = rt_tower.clone().fs;
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
                            &input_opening_point,
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

    // // assume public io is tiny vector, so we evaluate it directly without PCS
    // for &Instance(idx) in cs.instance_name_map.keys() {
    //     let poly = builder.get(&raw_pi, idx);
    //     let poly_num_variables = builder.get(raw_pi_num_variables, idx);
    //     let pts = input_opening_point.slice(builder, 0, poly_num_variables.clone());
    //     let eval: Ext<C::F, C::EF> = evaluate_felt_poly(builder, &poly, &pts, poly_num_variables);

    //     let expected_eval = builder.get(pi_evals, idx);
    //     builder.assert_ext_eq(eval, expected_eval);
    // }

    // TODO: PCS
    // // do optional check of fixed_commitment openings by vk
    // if circuit_vk.fixed_commit.is_some() {
    // let Some(fixed_opening_proof) = &proof.fixed_opening_proof else {
    //     return Err(ZKVMError::VerifyError(
    //         "fixed openning proof shoudn't be none".into(),
    //     ));
    // };

    // PCS::simple_batch_verify(
    //     vp,
    //     circuit_vk.fixed_commit.as_ref().unwrap(),
    //     &input_opening_point,
    //     &proof.fixed_in_evals,
    //     fixed_opening_proof,
    //     transcript,
    // )
    // .map_err(ZKVMError::PCSError)?;
    // }

    // TODO: PCS
    // PCS::simple_batch_verify(
    //     vp,
    //     &proof.wits_commit,
    //     &input_opening_point,
    //     &proof.wits_in_evals,
    //     &proof.wits_opening_proof,
    //     transcript,
    // )
}
