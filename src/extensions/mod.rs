use crate::arithmetics::{challenger_multi_observe, exts_to_felts, print_felt_arr};
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
use openvm_native_recursion::challenger::CanSampleVariable;
use openvm_native_recursion::hints::Hintable;
use openvm_stark_backend::config::StarkGenericConfig;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Config, p3_baby_bear::BabyBear,
};
use openvm_native_compiler::conversion::convert_program;
use std::collections::HashMap;
use std::fs::File;
use std::marker::PhantomData;
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
use p3_field::{Field, FieldAlgebra, FieldExtensionAlgebra};

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
    let options = CompilerOptions::default().with_cycle_tracker();
    let mut compiler = AsmCompiler::new(options.word_size);
    compiler.build(builder.operations);
    let asm_code = compiler.code();
    let program = convert_program(asm_code, options);

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
    let e1: Ext<C::F, C::EF> = builder.constant(C::EF::GENERATOR.exp_power_of_2(16));
    let e2: Ext<C::F, C::EF> = builder.constant(C::EF::GENERATOR.exp_power_of_2(32));
    let e3: Ext<C::F, C::EF> = builder.constant(C::EF::GENERATOR.exp_power_of_2(64));
    let e4: Ext<C::F, C::EF> = builder.constant(C::EF::GENERATOR.exp_power_of_2(128));
    let e5: Ext<C::F, C::EF> = builder.constant(C::EF::GENERATOR.exp_power_of_2(256));
    let len: usize = 5;

    let e_arr: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(len);
    builder.set(&e_arr, 0, e1);
    builder.set(&e_arr, 1, e2);
    builder.set(&e_arr, 2, e3);
    builder.set(&e_arr, 3, e4);
    builder.set(&e_arr, 4, e5);

    unsafe {
        let mut c1 = DuplexChallengerVariable::new(builder);
        let f_arr1 = exts_to_felts(builder, &e_arr); 
        challenger_multi_observe(builder, &mut c1, &f_arr1);
    }
}
