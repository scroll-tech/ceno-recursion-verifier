use crate::basefold_verifier::query_phase::{
    batch_verifier_query_phase, QueryPhaseVerifierInputVariable,
};

use super::{basefold::*, extension_mmcs::*, mmcs::*, rs::*, structs::*, utils::*};
use ff_ext::{BabyBearExt4, ExtensionField, PoseidonField};
use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::{
    challenger::{
        duplex::DuplexChallengerVariable, CanObserveDigest, CanObserveVariable,
        CanSampleBitsVariable, FeltChallenger,
    },
    hints::{Hintable, VecAutoHintable},
    vars::HintSlice,
};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use std::fmt::Debug;

pub type F = BabyBear;
pub type E = BabyBearExt4;
pub type InnerConfig = AsmConfig<F, E>;

pub(crate) fn batch_verifier<C: Config + Debug>(
    builder: &mut Builder<C>,
    rounds: Array<C, RoundVariable<C>>,
    proof: BasefoldProofVariable<C>,
    challenger: &mut DuplexChallengerVariable<C>,
) {
    builder.assert_nonzero(&proof.final_message.len());
    let expected_final_message_size: Var<C::N> = builder.eval(Usize::<C::N>::from(1usize)); // TODO: support early stop?
    iter_zip!(builder, proof.final_message).for_each(|ptr_vec, builder| {
        let final_message_len = builder.iter_ptr_get(&proof.final_message, ptr_vec[0]).len();
        builder.assert_eq::<Var<C::N>>(final_message_len, expected_final_message_size);
    });

    builder.assert_nonzero(&proof.sumcheck_proof.len());
    // TODO: get this number from some config instead of hardcoding
    let expected_num_queries: Var<C::N> = builder.eval(Usize::<C::N>::from(100usize));
    builder.assert_eq::<Var<C::N>>(proof.query_opening_proof.len(), expected_num_queries);

    // Compute the total number of polynomials across all rounds
    let total_num_polys: Var<C::N> = builder.eval(Usize::<C::N>::from(0));
    iter_zip!(builder, rounds).for_each(|ptr_vec, builder| {
        let openings = builder.iter_ptr_get(&rounds, ptr_vec[0]).openings;
        iter_zip!(builder, openings).for_each(|ptr_vec_openings, builder| {
            let evals_num = builder
                .iter_ptr_get(&openings, ptr_vec_openings[0])
                .point_and_evals
                .evals
                .len();
            builder.assign(&total_num_polys, total_num_polys + evals_num);
        });
    });

    let batch_coeffs: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(total_num_polys);
    iter_zip!(builder, batch_coeffs).for_each(|ptr_vec_batch_coeffs, builder| {
        let coeff = challenger.sample_ext(builder);
        builder.iter_ptr_set(&batch_coeffs, ptr_vec_batch_coeffs[0], coeff);
    });

    // Instead of computing the max num var, we let the prover provide it, and
    // check that it is greater than or equal to every num var, and that it is
    // equal to at least one of the num vars by multiplying all the differences
    // together and check if the product is zero.
    let max_num_var = builder.hint_var();
    let diff_product: Var<C::N> = builder.eval(Usize::from(1));
    let max_num_var_plus_one: Var<C::N> = builder.eval(max_num_var + Usize::from(1));
    iter_zip!(builder, rounds).for_each(|ptr_vec, builder| {
        let round = builder.iter_ptr_get(&rounds, ptr_vec[0]);
        // Need to compute the max num var for each round separately. This time
        // don't need to provide by hint because we have
        // commit.log2_max_codeword_size = max_num_var + rate_log
        // We need to ensure that rate_log < commit.log2_max_codeword_size
        // TODO: rate_log is temporarily hardcoded to 1
        builder.assert_less_than_slow_small_rhs(
            Usize::from(1),
            round.commit.log2_max_codeword_size.clone(),
        );
        let max_num_var_round: Var<C::N> =
            builder.eval(round.commit.log2_max_codeword_size - Usize::from(1));
        // Although max_num_var_round_plus_one is the same as log2_max_codeword_size
        // in the current code, it may not be so when the log rate is updated. So
        // let's keep the code more general for now.
        let max_num_var_round_plus_one: Var<C::N> =
            builder.eval(max_num_var_round + Usize::from(1));
        let diff_product_round: Var<C::N> = builder.eval(Usize::from(1));
        iter_zip!(builder, round.openings).for_each(|ptr_vec_opening, builder| {
            let opening = builder.iter_ptr_get(&round.openings, ptr_vec_opening[0]);
            builder.assert_less_than_slow_small_rhs(opening.num_var, max_num_var_round_plus_one);
            builder.assign(
                &diff_product_round,
                diff_product_round * (max_num_var_round - opening.num_var),
            );
        });
        // Check that at least one opening.num_var is equal to max_num_var_round
        builder.assert_eq::<Var<C::N>>(diff_product_round, Usize::from(0));

        // Now work with the outer max num var
        builder.assert_less_than_slow_small_rhs(max_num_var_round, max_num_var_plus_one);
        builder.assign(
            &diff_product,
            diff_product * (max_num_var - max_num_var_round),
        );
    });
    // Check that at least one max_num_var_round is equal to max_num_var
    builder.assert_eq::<Var<C::N>>(diff_product, Usize::from(0));

    // TODO: num rounds should be max num var - base message size log, but
    // base message size log is 0 for now
    let num_rounds = max_num_var;

    let fold_challenges: Array<C, Ext<_, _>> = builder.dyn_array(max_num_var);
    builder.range(0, num_rounds).for_each(|ptr_vec, builder| {
        let sumcheck_message = builder
            .iter_ptr_get(&proof.sumcheck_proof, ptr_vec[0])
            .evaluations;
        iter_zip!(builder, sumcheck_message).for_each(|ptr_vec_sumcheck_message, builder| {
            let elem = builder.iter_ptr_get(&sumcheck_message, ptr_vec_sumcheck_message[0]);
            let elem_felts = builder.ext2felt(elem);
            challenger.observe_slice(builder, elem_felts);
        });

        let challenge = challenger.sample_ext(builder);
        builder.iter_ptr_set(&fold_challenges, ptr_vec[0], challenge);
        builder
            .if_ne(ptr_vec[0], num_rounds - Usize::from(1))
            .then(|builder| {
                let commit = builder.iter_ptr_get(&proof.commits, ptr_vec[0]);
                challenger.observe_digest(builder, commit.value.into());
            });
    });

    iter_zip!(builder, proof.final_message).for_each(|ptr_vec_sumcheck_message, builder| {
        // Each final message should contain a single element, since the final
        // message size log is assumed to be zero
        let elems = builder.iter_ptr_get(&proof.final_message, ptr_vec_sumcheck_message[0]);
        let elem = builder.get(&elems, 0);
        let elem_felts = builder.ext2felt(elem);
        challenger.observe_slice(builder, elem_felts);
    });

    let queries: Array<C, Var<C::N>> = builder.dyn_array(100); // TODO: avoid hardcoding
    builder.range(0, 100).for_each(|ptr_vec, builder| {
        let number_of_bits = builder.eval_expr(max_num_var + Usize::from(1));
        let query = challenger.sample_bits(builder, number_of_bits);
        // TODO: the index will need to be split back to bits in query phase, so it's
        // probably better to avoid converting bits to integer altogether
        let number_of_bits = builder.eval(max_num_var + Usize::from(1));
        let query = bin_to_dec(builder, &query, number_of_bits);
        builder.iter_ptr_set(&queries, ptr_vec[0], query);
    });

    let input = QueryPhaseVerifierInputVariable {
        max_num_var: builder.eval(max_num_var),
        batch_coeffs,
        fold_challenges,
        indices: queries,
        proof,
        rounds,
    };
    batch_verifier_query_phase(builder, input);
}
