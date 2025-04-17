use super::binding::{
    ZKVMOpcodeProofInputVariable, ZKVMProofInputVariable, ZKVMTableProofInputVariable,
};
use crate::arithmetics::pow_of_2_var;
use crate::constants::OPCODE_KEYS;
use crate::tower_verifier::program::verify_tower_proof;
use crate::{
    arithmetics::{
        build_eq_x_r_vec_sequential, dot_product as ext_dot_product, eq_eval_less_or_equal_than,
        gen_alpha_pows, product, sum as ext_sum, ceil_log2, next_pow2_instance_padding,
    },
    json::parser::parse_zkvm_proof_json,
    tower_verifier::{
        binding::{Point, PointAndEvalVariable, PointVariable, TowerVerifierInputVariable},
        program::iop_verifier_state_verify,
    },
};
use ceno_zkvm::{error, structs::PointAndEval};
use itertools::max;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler::{asm::AsmConfig, ir::MemVariable};
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::{
    challenger::{
        duplex::DuplexChallengerVariable, CanObserveVariable, ChallengerVariable, FeltChallenger,
    },
    hints::{InnerChallenge, InnerVal},
};
use p3_field::{dot_product, FieldAlgebra, FieldExtensionAlgebra};

use ceno_zkvm::{
    scheme::{
        verifier::ZKVMVerifier,
    },
};
use ff_ext::BabyBearExt4;
use mpcs::{Basefold, BasefoldRSParams};

type E = BabyBearExt4;
type Pcs = Basefold<E, BasefoldRSParams>;
type InnerConfig = AsmConfig<InnerVal, InnerChallenge>;
const NUM_FANIN: usize = 2;
const MAX_DEGREE: usize = 3;
const DIGEST_WIDTH: usize = 8;
const MAINCONSTRAIN_SUMCHECK_BATCH_SIZE: usize = 3; // read/write/lookup

pub fn verify_zkvm_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    zkvm_proof_input: ZKVMProofInputVariable<C>,
    ceno_constraint_system: &ZKVMVerifier<E, Pcs>,
) {
    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
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
            // _debug
            // builder.assert_var_eq(raw.len(), RVar::from(1));
            // builder.assert_ext_eq(raw0, eval);
        },
    );

    let digest_width: RVar<C::N> = RVar::from(DIGEST_WIDTH);
    iter_zip!(builder, zkvm_proof_input.circuit_vks_fixed_commits).for_each(|ptr_vec, builder| {
        let cmt = builder.iter_ptr_get(&zkvm_proof_input.circuit_vks_fixed_commits, ptr_vec[0]);
        // _debug
        // builder.assert_var_eq(cmt.len(), digest_width);

        iter_zip!(builder, cmt).for_each(|inner_ptr_vec, builder| {
            let f = builder.iter_ptr_get(&cmt, inner_ptr_vec[0]);
            challenger.observe(builder, f);
        })
    });

    iter_zip!(builder, zkvm_proof_input.opcode_proofs).for_each(|ptr_vec, builder| {
        let cmt = builder
            .iter_ptr_get(&zkvm_proof_input.opcode_proofs, ptr_vec[0])
            .wits_commit;
        // _debug
        // builder.assert_var_eq(cmt.len(), digest_width);

        iter_zip!(builder, cmt).for_each(|inner_ptr_vec, builder| {
            let f = builder.iter_ptr_get(&cmt, inner_ptr_vec[0]);
            challenger.observe(builder, f);
        })
    });

    iter_zip!(builder, zkvm_proof_input.table_proofs).for_each(|ptr_vec, builder| {
        let cmt = builder
            .iter_ptr_get(&zkvm_proof_input.table_proofs, ptr_vec[0])
            .wits_commit;
        // _debug
        // builder.assert_var_eq(cmt.len(), digest_width);

        iter_zip!(builder, cmt).for_each(|inner_ptr_vec, builder| {
            let f = builder.iter_ptr_get(&cmt, inner_ptr_vec[0]);
            challenger.observe(builder, f);
        })
    });

    let alpha = challenger.sample_ext(builder);
    let beta = challenger.sample_ext(builder);

    let dummy_table_item = alpha.clone();
    let dummy_table_item_multiplicity: RVar<C::N> = RVar::from(0);
    let dummy_table_item_multiplicity_ext: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    let mut sub_opcode_constraint_idx: usize = 0;
    iter_zip!(builder, zkvm_proof_input.opcode_proofs).for_each(|ptr_vec, builder| {
        let opcode_proof = &builder.iter_ptr_get(&zkvm_proof_input.opcode_proofs, ptr_vec[0]);
        let idx = opcode_proof.idx.clone();
        let circuit_vk = builder.get(&zkvm_proof_input.circuit_vks_fixed_commits, idx);

        // Construct a forked challenger
        let mut forked_challenger = (*challenger).clone();
        forked_challenger.observe(builder, opcode_proof.idx_felt);

        verify_opcode_proof(
            builder,
            &mut forked_challenger,
            circuit_vk,
            opcode_proof,
            &zkvm_proof_input.pi_evals,
            alpha.clone(),
            beta.clone(),
            sub_opcode_constraint_idx,
            ceno_constraint_system,
        );

        


        // _debug
        //         // getting the number of dummy padding item that we used in this opcode circuit
        //         let num_lks = circuit_vk.get_cs().lk_expressions.len();
        //         let num_padded_lks_per_instance = next_pow2_instance_padding(num_lks) - num_lks;
        //         let num_padded_instance =
        //             next_pow2_instance_padding(opcode_proof.num_instances) - opcode_proof.num_instances;
        //         dummy_table_item_multiplicity += num_padded_lks_per_instance
        //             * opcode_proof.num_instances
        //             + num_lks.next_power_of_two() * num_padded_instance;

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

        sub_opcode_constraint_idx += 1;
    });

    let mut sub_table_constraint_idx: usize = 0;
    iter_zip!(builder, zkvm_proof_input.table_proofs).for_each(|ptr_vec, builder| {
        let table_proof = &builder.iter_ptr_get(&zkvm_proof_input.table_proofs, ptr_vec[0]);
        let idx = table_proof.idx.clone();
        let circuit_vk = builder.get(&zkvm_proof_input.circuit_vks_fixed_commits, idx);

        // Construct a forked challenger
        let mut forked_challenger = (*challenger).clone();
        forked_challenger.observe(builder, table_proof.idx_felt);

        verify_table_proof(
            builder,
            &mut forked_challenger,
            circuit_vk,
            table_proof,
            &zkvm_proof_input.raw_pi,
            &zkvm_proof_input.pi_evals,
            sub_table_constraint_idx,
            ceno_constraint_system,
        );

        let step = C::N::from_canonical_usize(4);
        builder.range_with_step(0, table_proof.lk_out_evals.len(), step).for_each(|idx_vec, builder| {
            let one_var: Var<C::N> = Var::<C::N>::new(1);
            let p1 = builder.get(&table_proof.lk_out_evals, idx_vec[0]);
            let p2_idx: Var<C::N> = builder.eval(idx_vec[0] + one_var);
            let p2 = builder.get(&table_proof.lk_out_evals, p2_idx);
            let q1_idx: Var<C::N> = builder.eval(p2_idx + one_var);
            let q1 = builder.get(&table_proof.lk_out_evals, q1_idx);
            let q2_idx: Var<C::N> = builder.eval(q1_idx + one_var);
            let q2 = builder.get(&table_proof.lk_out_evals, q2_idx);

            builder.assign(&logup_sum, logup_sum - p1 * q1.inverse() - p2 * q2.inverse());
        });

        let w_out_evals_prod = product(builder, &table_proof.w_out_evals);
        builder.assign(&prod_w, prod_w * w_out_evals_prod);
        let r_out_evals_prod = product(builder, &table_proof.r_out_evals);
        builder.assign(&prod_r, prod_r * r_out_evals_prod);

        sub_table_constraint_idx += 1;
    });

    builder.assign(
        &logup_sum,
        logup_sum - dummy_table_item_multiplicity_ext * dummy_table_item.inverse(),
    );

    // _debug
    // builder.assert_ext_eq(logup_sum, zero);

    // _debug
    //     let initial_global_state = eval_by_expr_with_instance(
    //         &[],
    //         &[],
    //         &[],
    //         pi_evals,
    //         &challenges,
    //         &self.vk.initial_global_state_expr,
    //     );
    //     prod_w *= initial_global_state;

    //     let finalize_global_state = eval_by_expr_with_instance(
    //         &[],
    //         &[],
    //         &[],
    //         pi_evals,
    //         &challenges,
    //         &self.vk.finalize_global_state_expr,
    //     );
    //     prod_r *= finalize_global_state;

    // _debug
    // builder.assert_ext_eq(prod_r, prod_w);
}

pub fn verify_opcode_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    circuit_vk: Array<C, Felt<C::F>>,
    opcode_proof: &ZKVMOpcodeProofInputVariable<C>,
    pi_evals: &Array<C, Ext<C::F, C::EF>>,
    alpha: Ext<C::F, C::EF>,
    beta: Ext<C::F, C::EF>,
    sub_constraint_idx: usize,
    ceno_constraint_system: &ZKVMVerifier<E, Pcs>,
) {
    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    let sub_constraint_name = OPCODE_KEYS[sub_constraint_idx];
    let cs = &ceno_constraint_system.vk.circuit_vks[sub_constraint_name].cs;

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

    let num_instances = opcode_proof.num_instances.clone();
    let next_pow2_instance = next_pow2_instance_padding(num_instances.0 as usize);
    let log2_num_instances = Var::<C::N>::new(ceil_log2(next_pow2_instance) as u32);

    let num_variables: Array<C, Var<C::N>> = builder.dyn_array(3);
    let num_variables_r: Var<C::N> = builder.eval(log2_num_instances + log2_r_count.clone());
    builder.set(&num_variables, 0, num_variables_r);
    let num_variables_w: Var<C::N> = builder.eval(log2_num_instances + log2_w_count.clone());
    builder.set(&num_variables, 1, num_variables_w);
    let num_variables_lk: Var<C::N> = builder.eval(log2_num_instances + log2_lk_count.clone());
    builder.set(&num_variables, 2, num_variables_lk);
    let max_num_variables: Var<C::N> = builder.eval(log2_num_instances + Var::<C::N>::new(max_expr_len as u32));
    let max_num_variables_f: Felt<C::F> = builder.unsafe_cast_var_to_felt(max_num_variables);

    let max_degree: Felt<C::F> = builder.constant(C::F::from_canonical_u32(3));

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

    builder.assert_usize_eq(record_evals.len(), Usize::from(2));
    builder.assert_usize_eq(logup_q_evals.len(), Usize::from(1));
    builder.assert_usize_eq(logup_p_evals.len(), Usize::from(1));

    let logup_p_eval = builder.get(&logup_p_evals, 0).eval;
    // _debug
    // builder.assert_ext_eq(logup_p_eval, zero);

    let [rt_r, rt_w, rt_lk]: [Array<C, Ext<C::F, C::EF>>; 3] = [
        builder.get(&record_evals, 0).point.fs,
        builder.get(&record_evals, 1).point.fs,
        builder.get(&logup_q_evals, 0).point.fs,
    ];

    let alpha_len = MAINCONSTRAIN_SUMCHECK_BATCH_SIZE + cs.assert_zero_sumcheck_expressions.len();
    let alpha_len: Var<C::N> = Var::<C::N>::new(alpha_len as u32);
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

    builder.assign(
        &claim_sum,
        alpha_read * (record_eval_0 - one)
            + alpha_write * (record_eval_1 - one)
            + alpha_lk * (logup_q_eval_0 - alpha),
    );

    let main_sel_subclaim = iop_verifier_state_verify(
        builder,
        challenger,
        &claim_sum,
        &opcode_proof.main_sel_sumcheck_proofs,
        max_num_variables_f,
        max_num_variables,
        max_degree,
    );

    let input_opening_point = PointVariable {
        fs: main_sel_subclaim.0,
    };
    let expected_evaluation: Ext<C::F, C::EF> = main_sel_subclaim.1;

    let rt_r_eq = rt_r.slice(builder, 0, log2_r_count.clone());
    let eq_r = build_eq_x_r_vec_sequential(builder, &rt_r_eq);
    let rt_w_eq = rt_w.slice(builder, 0, log2_w_count.clone());
    let eq_w = build_eq_x_r_vec_sequential(builder, &rt_w_eq);
    let rt_lk_eq = rt_lk.slice(builder, 0, log2_lk_count.clone());
    let eq_lk = build_eq_x_r_vec_sequential(builder, &rt_lk_eq);

    let eq_instance: Var<C::N> = opcode_proof.num_instances.clone();
    builder.assign(&eq_instance, eq_instance - Var::<C::N>::new(1));

    let rt_r_eq_less = rt_r.slice(builder, log2_r_count.clone(), rt_r.len());
    let rt_w_eq_less = rt_w.slice(builder, log2_w_count.clone(), rt_w.len());
    let rt_lk_eq_less = rt_lk.slice(builder, log2_lk_count.clone(), rt_lk.len());

    let sel_r = eq_eval_less_or_equal_than(
        builder,
        challenger,
        eq_instance.clone(),
        &input_opening_point.fs,
        &rt_r_eq_less,
    );
    let sel_w = eq_eval_less_or_equal_than(
        builder,
        challenger,
        eq_instance.clone(),
        &input_opening_point.fs,
        &rt_w_eq_less,
    );
    let sel_lk = eq_eval_less_or_equal_than(
        builder,
        challenger,
        eq_instance.clone(),
        &input_opening_point.fs,
        &rt_lk_eq_less,
    );

    let sel_non_lc_zero_sumcheck: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let rt_non_lc_sumcheck = rt_tower.fs.slice(builder, 0, log2_num_instances);

    let has_zero_sumcheck_expressions: Var<C::N> = if cs.assert_zero_sumcheck_expressions.len() > 0 {
        Var::<C::N>::new(1)
    } else {
        Var::<C::N>::new(0)
    };

    builder
        .if_ne(has_zero_sumcheck_expressions, Var::<C::N>::new(0))
        .then(|builder| {
            let sel_sumcheck = eq_eval_less_or_equal_than(
                builder,
                challenger,
                eq_instance.clone(),
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

    // _debug
    // // sel(rt_non_lc_sumcheck, main_sel_eval_point) * \sum_j (alpha{j} * expr(main_sel_eval_point))
    // sel_non_lc_zero_sumcheck.unwrap_or(E::ZERO)
    //     * cs.assert_zero_sumcheck_expressions
    //         .iter()
    //         .zip_eq(alpha_pow_iter)
    //         .map(|(expr, alpha)| {
    //             // evaluate zero expression by all wits_in_evals because they share the unique input_opening_point opening
    //             *alpha
    //                 * eval_by_expr_with_instance(
    //                     &[],
    //                     &proof.wits_in_evals,
    //                     &[],
    //                     pi,
    //                     challenges,
    //                     expr,
    //                 )
    //         })
    //         .sum::<E>()

    // _debug
    // builder.assert_ext_eq(computed_eval, expected_evaluation);

    // _debug
    // // verify records (degree = 1) statement, thus no sumcheck
    // if izip!(
    //     chain!(&cs.r_expressions, &cs.w_expressions, &cs.lk_expressions),
    //     chain!(
    //         &proof.r_records_in_evals[..r_counts_per_instance],
    //         &proof.w_records_in_evals[..w_counts_per_instance],
    //         &proof.lk_records_in_evals[..lk_counts_per_instance]
    //     )
    // )
    // .any(|(expr, expected_evals)| {
    //     eval_by_expr_with_instance(&[], &proof.wits_in_evals, &[], pi, challenges, expr)
    //         != *expected_evals
    // }) {
    //     return Err(ZKVMError::VerifyError(
    //         "record evaluate != expected_evals".into(),
    //     ));
    // }

    // _debug
    // // verify zero expression (degree = 1) statement, thus no sumcheck
    // if cs.assert_zero_expressions.iter().any(|expr| {
    //     eval_by_expr_with_instance(&[], &proof.wits_in_evals, &[], pi, challenges, expr)
    //         != E::ZERO
    // }) {
    //     return Err(ZKVMError::VerifyError("zero expression != 0".into()));
    // }

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
    circuit_vk: Array<C, Felt<C::F>>,
    table_proof: &ZKVMTableProofInputVariable<C>,
    raw_pi: &Array<C, Array<C, Felt<C::F>>>,
    pi_evals: &Array<C, Ext<C::F, C::EF>>,
    sub_constraint_idx: usize,
    ceno_constraint_system: &ZKVMVerifier<E, Pcs>,
) {

    // TODO

    // #[allow(clippy::too_many_arguments)]
    // pub fn verify_table_proof(
    //     &self,
    //     name: &str,
    //     vp: &PCS::VerifierParam,
    //     circuit_vk: &VerifyingKey<E, PCS>,
    //     proof: &ZKVMTableProof<E, PCS>,
    //     raw_pi: &[Vec<E::BaseField>],
    //     pi: &[E],
    //     transcript: &mut impl Transcript<E>,
    //     num_logup_fanin: usize,
    //     _out_evals: &PointAndEval<E>,
    //     challenges: &[E; 2],
    // ) -> Result<Point<E>, ZKVMError> {

    let is_skip_same_point_sumcheck: Usize<C::N> = Usize::from(1);
    let tower_proof = &table_proof.tower_proof;


    //     let expected_rounds = cs
    //         // only iterate r set, as read/write set round should match
    //         .r_table_expressions
    //         .iter()
    //         .flat_map(|r| {
    //             // iterate through structural witins and collect max round.
    //             let num_vars = r.table_spec.len.map(ceil_log2).unwrap_or_else(|| {
    //                 r.table_spec
    //                     .structural_witins
    //                     .iter()
    //                     .map(|StructuralWitIn { id, max_len, .. }| {
    //                         let hint_num_vars = proof.rw_hints_num_vars[*id as usize];
    //                         assert!((1 << hint_num_vars) <= *max_len);
    //                         hint_num_vars
    //                     })
    //                     .max()
    //                     .unwrap()
    //             });
    //             [num_vars, num_vars] // format: [read_round, write_round]
    //         })
    //         .chain(cs.lk_table_expressions.iter().map(|l| {
    //             // iterate through structural witins and collect max round.
    //             let num_vars = l.table_spec.len.map(ceil_log2).unwrap_or_else(|| {
    //                 l.table_spec
    //                     .structural_witins
    //                     .iter()
    //                     .map(|StructuralWitIn { id, max_len, .. }| {
    //                         let hint_num_vars = proof.rw_hints_num_vars[*id as usize];
    //                         assert!((1 << hint_num_vars) <= *max_len);
    //                         hint_num_vars
    //                     })
    //                     .max()
    //                     .unwrap()
    //             });
    //             num_vars
    //         }))
    //         .collect_vec();

    //     for var in proof.rw_hints_num_vars.iter() {
    //         transcript.append_message(&var.to_le_bytes());
    //     }

    //     let expected_max_rounds = expected_rounds.iter().cloned().max().unwrap();
    //     let (rt_tower, prod_point_and_eval, logup_p_point_and_eval, logup_q_point_and_eval) =
    //         TowerVerify::verify(
    //             proof
    //                 .r_out_evals
    //                 .iter()
    //                 .zip(proof.w_out_evals.iter())
    //                 .flat_map(|(r_evals, w_evals)| [r_evals.to_vec(), w_evals.to_vec()])
    //                 .collect_vec(),
    //             proof
    //                 .lk_out_evals
    //                 .iter()
    //                 .map(|eval| eval.to_vec())
    //                 .collect_vec(),
    //             tower_proofs,
    //             expected_rounds,
    //             num_logup_fanin,
    //             transcript,
    //         )?;
    //     assert_eq!(
    //         logup_q_point_and_eval.len(),
    //         cs.lk_table_expressions.len(),
    //         "[lk_q_record] mismatch length"
    //     );
    //     assert_eq!(
    //         logup_p_point_and_eval.len(),
    //         cs.lk_table_expressions.len(),
    //         "[lk_p_record] mismatch length"
    //     );
    //     assert_eq!(
    //         prod_point_and_eval.len(),
    //         cs.r_table_expressions.len() + cs.w_table_expressions.len(),
    //         "[prod_record] mismatch length"
    //     );

    //     let (input_opening_point, in_evals) = if is_skip_same_point_sumcheck {
    //         (
    //             rt_tower,
    //             prod_point_and_eval
    //                 .into_iter()
    //                 .chain(
    //                     logup_p_point_and_eval
    //                         .into_iter()
    //                         .zip_eq(logup_q_point_and_eval)
    //                         .flat_map(|(p_point_and_eval, q_point_and_eval)| {
    //                             [p_point_and_eval, q_point_and_eval]
    //                         }),
    //                 )
    //                 .map(|point_and_eval| point_and_eval.eval)
    //                 .collect_vec(),
    //         )
    //     } else {
    //         assert!(proof.same_r_sumcheck_proofs.is_some());

    //         // verify opening same point layer sumcheck
    //         let alpha_pow = get_challenge_pows(
    //             cs.r_table_expressions.len()
    //                 + cs.w_table_expressions.len()
    //                 + cs.lk_table_expressions.len() * 2, // 2 for lk numerator and denominator
    //             transcript,
    //         );

    //         //  \sum_i alpha_{i} * (out_r_eval{i})
    //         //  + \sum_i alpha_{i} * (out_w_eval{i})
    //         //  + \sum_i alpha_{i} * (out_lk_n{i})
    //         //  + \sum_i alpha_{i} * (out_lk_d{i})
    //         let claim_sum = prod_point_and_eval
    //             .iter()
    //             .zip(alpha_pow.iter())
    //             .map(|(point_and_eval, alpha)| *alpha * point_and_eval.eval)
    //             .sum::<E>()
    //             + interleave(&logup_p_point_and_eval, &logup_q_point_and_eval)
    //                 .zip_eq(alpha_pow.iter().skip(prod_point_and_eval.len()))
    //                 .map(|(point_n_eval, alpha)| *alpha * point_n_eval.eval)
    //                 .sum::<E>();
    //         let sel_subclaim = IOPVerifierState::verify(
    //             claim_sum,
    //             &IOPProof {
    //                 point: vec![], // final claimed point will be derived from sumcheck protocol
    //                 proofs: proof.same_r_sumcheck_proofs.clone().unwrap(),
    //             },
    //             &VPAuxInfo {
    //                 max_degree: SEL_DEGREE,
    //                 max_num_variables: expected_max_rounds,
    //                 phantom: PhantomData,
    //             },
    //             transcript,
    //         );
    //         let (input_opening_point, expected_evaluation) = (
    //             sel_subclaim.point.iter().map(|c| c.elements).collect_vec(),
    //             sel_subclaim.expected_evaluation,
    //         );

    //         let computed_evals = [
    //             // r, w
    //             prod_point_and_eval
    //                 .into_iter()
    //                 .zip_eq(proof.rw_in_evals.iter())
    //                 .zip(alpha_pow.iter())
    //                 .map(|((point_and_eval, in_eval), alpha)| {
    //                     let eq = eq_eval(
    //                         &point_and_eval.point,
    //                         &input_opening_point[0..point_and_eval.point.len()],
    //                     );
    //                     // TODO times multiplication factor
    //                     *alpha * eq * *in_eval
    //                 })
    //                 .sum::<E>(),
    //             interleave(logup_p_point_and_eval, logup_q_point_and_eval)
    //                 .zip_eq(proof.lk_in_evals.iter())
    //                 .zip_eq(
    //                     alpha_pow
    //                         .iter()
    //                         .skip(cs.r_table_expressions.len() + cs.w_table_expressions.len()),
    //                 )
    //                 .map(|((point_and_eval, in_eval), alpha)| {
    //                     let eq = eq_eval(
    //                         &point_and_eval.point,
    //                         &input_opening_point[0..point_and_eval.point.len()],
    //                     );
    //                     // TODO times multiplication factor
    //                     *alpha * eq * *in_eval
    //                 })
    //                 .sum::<E>(),
    //         ]
    //         .iter()
    //         .sum::<E>();
    //         if computed_evals != expected_evaluation {
    //             return Err(ZKVMError::VerifyError(
    //                 "sel evaluation verify failed".into(),
    //             ));
    //         }
    //         (
    //             input_opening_point,
    //             [proof.rw_in_evals.to_vec(), proof.lk_in_evals.to_vec()].concat(),
    //         )
    //     };

    //     // evaluate structural witness from verifier succinctly
    //     let structural_witnesses = cs
    //         .r_table_expressions
    //         .iter()
    //         .map(|r| &r.table_spec)
    //         .chain(cs.lk_table_expressions.iter().map(|r| &r.table_spec))
    //         .flat_map(|table_spec| {
    //             table_spec
    //                 .structural_witins
    //                 .iter()
    //                 .map(
    //                     |StructuralWitIn {
    //                          offset,
    //                          multi_factor,
    //                          ..
    //                      }| {
    //                         eval_wellform_address_vec(
    //                             *offset as u64,
    //                             *multi_factor as u64,
    //                             &input_opening_point,
    //                         )
    //                     },
    //                 )
    //                 .collect_vec()
    //         })
    //         .collect_vec();

    //     // verify records (degree = 1) statement, thus no sumcheck
    //     if interleave(
    //         &cs.r_table_expressions, // r
    //         &cs.w_table_expressions, // w
    //     )
    //     .map(|rw| &rw.expr)
    //     .chain(
    //         cs.lk_table_expressions
    //             .iter()
    //             .flat_map(|lk| vec![&lk.multiplicity, &lk.values]), // p, q
    //     )
    //     .zip_eq(in_evals)
    //     .any(|(expr, expected_evals)| {
    //         eval_by_expr_with_instance(
    //             &proof.fixed_in_evals,
    //             &proof.wits_in_evals,
    //             &structural_witnesses,
    //             pi,
    //             challenges,
    //             expr,
    //         ) != expected_evals
    //     }) {
    //         return Err(ZKVMError::VerifyError(
    //             "record evaluate != expected_evals".into(),
    //         ));
    //     }

    //     // assume public io is tiny vector, so we evaluate it directly without PCS
    //     for &Instance(idx) in cs.instance_name_map.keys() {
    //         let poly = raw_pi[idx].to_vec().into_mle();
    //         let expected_eval = poly.evaluate(&input_opening_point[..poly.num_vars()]);
    //         let eval = pi[idx];
    //         if expected_eval != eval {
    //             return Err(ZKVMError::VerifyError(format!(
    //                 "pub input on index {idx} mismatch  {expected_eval:?} != {eval:?}"
    //             )));
    //         }
    //         tracing::debug!(
    //             "[table {name}] verified public inputs on index {idx} with point {input_opening_point:?}",
    //         );
    //     }














    
    //     TODO:
    //     // do optional check of fixed_commitment openings by vk
    //     if circuit_vk.fixed_commit.is_some() {
    //         let Some(fixed_opening_proof) = &proof.fixed_opening_proof else {
    //             return Err(ZKVMError::VerifyError(
    //                 "fixed openning proof shoudn't be none".into(),
    //             ));
    //         };
    //         PCS::simple_batch_verify(
    //             vp,
    //             circuit_vk.fixed_commit.as_ref().unwrap(),
    //             &input_opening_point,
    //             &proof.fixed_in_evals,
    //             fixed_opening_proof,
    //             transcript,
    //         )
    //         .map_err(ZKVMError::PCSError)?;
    //     }

    //     TODO:
    //     PCS::simple_batch_verify(
    //         vp,
    //         &proof.wits_commit,
    //         &input_opening_point,
    //         &proof.wits_in_evals,
    //         &proof.wits_opening_proof,
    //         transcript,
    //     )
}
