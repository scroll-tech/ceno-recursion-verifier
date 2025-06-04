use crate::tower_verifier::binding::IOPProverMessage;
use crate::zkvm_verifier::binding::ZKVMProofInput;
use crate::zkvm_verifier::binding::{
    TowerProofInput, ZKVMOpcodeProofInput, ZKVMTableProofInput, E, F,
};
use crate::zkvm_verifier::verifier::verify_zkvm_proof;
use ff_ext::BabyBearExt4;
use itertools::Itertools;
use mpcs::BasefoldCommitment;
use mpcs::{Basefold, BasefoldRSParams};
use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
use openvm_native_circuit::{Native, NativeConfig};
use openvm_native_compiler::{asm::AsmBuilder, conversion::CompilerOptions};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_backend::config::StarkGenericConfig;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Config, p3_baby_bear::BabyBear,
};
use std::collections::HashMap;
use std::fs::File;
use crate::e2e::SubcircuitParams;
use crate::tower_verifier::program::verify_tower_proof;
use crate::transcript::transcript_observe_label;
use crate::{
    arithmetics::{
        build_eq_x_r_vec_sequential, ceil_log2, concat, dot_product as ext_dot_product,
        eq_eval_less_or_equal_than, eval_ceno_expr_with_instance, eval_wellform_address_vec,
        gen_alpha_pows, max_usize_arr, max_usize_vec, next_pow2_instance_padding, product,
        sum as ext_sum,
    },
    tower_verifier::{
        binding::{PointVariable, TowerVerifierInputVariable},
        program::iop_verifier_state_verify,
    },
};
use ceno_zkvm::circuit_builder::SetTableSpec;
use ceno_zkvm::{expression::StructuralWitIn, scheme::verifier::ZKVMVerifier};
use itertools::interleave;
use itertools::max;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::{
    duplex::DuplexChallengerVariable, CanObserveVariable, FeltChallenger,
};
use p3_field::{Field, FieldAlgebra};

type Pcs = Basefold<E, BasefoldRSParams>;
const NUM_FANIN: usize = 2;
const MAINCONSTRAIN_SUMCHECK_BATCH_SIZE: usize = 3; // read/write/lookup
const SEL_DEGREE: usize = 2;

type SC = BabyBearPoseidon2Config;
type EF = <SC as StarkGenericConfig>::Challenge;

#[test]
pub fn test_native_multi_observe() {
    // OpenVM DSL
    let mut builder = AsmBuilder::<F, EF>::default();

    vm_program(&mut builder);

    builder.halt();

    // Pass in witness stream
    let witness_stream: Vec<
        Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
    > = Vec::new();

    // Compile program
    let program: Program<
        p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
    > = builder.compile_isa_with_options(CompilerOptions::default().with_cycle_tracker());

    println!("=> program instructions:");
    println!("=> {:?}", program.instructions_and_debug_infos);
    println!();

    let mut system_config = SystemConfig::default()
        .with_public_values(4)
        .with_max_segment_len((1 << 25) - 100);
    system_config.profiling = true;
    let config = NativeConfig::new(system_config, Native);

    let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
    
    // Alternative execution
    // executor.execute(program, witness_stream).unwrap();

    let res = executor.execute_and_then(
        program,
        witness_stream,
        |_, seg| {
            Ok(seg)
        },
        |err| err,
    ).unwrap();

    for (i, seg) in res.iter().enumerate() {
        println!("=> segment {:?} metrics: {:?}", i, seg.metrics);
    }
}

fn vm_program<C: Config>(
    builder: &mut Builder<C>,
) {
    let mut challenger = DuplexChallengerVariable::new(builder);
    let arr: Array<C, Felt<C::F>> = builder.dyn_array(20);
    builder.range(0, arr.len()).for_each(|idx_vec, builder| {
        builder.if_eq(idx_vec[0], RVar::from(5)).then_or_else(|builder| {
            let val: Felt<C::F> = builder.constant(C::F::ZERO);
            builder.set(&arr, idx_vec[0], val);
        }, |builder| {
            let val: Felt<C::F> = builder.constant(C::F::TWO);
            builder.set(&arr, idx_vec[0], val);
        });
    });

    builder.range(0, arr.len()).for_each(|idx_vec, builder| {
        let val = builder.get(&arr, idx_vec[0]);
        challenger.observe(builder, val);
    });   
}
