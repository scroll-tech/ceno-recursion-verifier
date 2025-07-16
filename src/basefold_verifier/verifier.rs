use super::{basefold::*, extension_mmcs::*, mmcs::*, rs::*, structs::*, utils::*};
use ff_ext::{BabyBearExt4, ExtensionField, PoseidonField};
use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::{
    challenger::duplex::DuplexChallengerVariable,
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
}
