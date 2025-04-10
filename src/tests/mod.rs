use crate::tower_verifier::binding::F;
use crate::zkvm_verifier::verifier::verify_zkvm_proof;
use mpcs::{Basefold, BasefoldRSParams};
use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
use openvm_native_circuit::{Native, NativeConfig};
use openvm_native_compiler::asm::AsmBuilder;
use openvm_native_recursion::{
    challenger::duplex::DuplexChallengerVariable,
    hints::Hintable,
};
use openvm_stark_backend::config::StarkGenericConfig;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::{default_engine, BabyBearPoseidon2Config},
    p3_baby_bear::BabyBear,
};
use crate::zkvm_verifier::binding::ZKVMProofInput;
use crate::json::parser::parse_zkvm_proof_json;

type SC = BabyBearPoseidon2Config;
type EF = <SC as StarkGenericConfig>::Challenge;
type Challenger = <SC as StarkGenericConfig>::Challenger;

use crate::tower_verifier::binding::E;

type B = BabyBear;
type Pcs = Basefold<E, BasefoldRSParams>;

#[allow(dead_code)]
fn build_zkvm_proof_verifier_test() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
    // OpenVM DSL
    let engine = default_engine();
    let mut builder = AsmBuilder::<F, EF>::default();
    let mut challenger = DuplexChallengerVariable::new(&mut builder);

    // Obtain witness inputs
    let zkvm_proof_input_variables = ZKVMProofInput::read(&mut builder);
    verify_zkvm_proof(&mut builder, &mut challenger, zkvm_proof_input_variables);
    builder.halt();

    // Pass in witness stream
    let mut witness_stream: Vec<
        Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
    > = Vec::new();

    let zkvm_proof_input = parse_zkvm_proof_json();

    // witness_stream.extend(zkvm_proof_input.write());

    // Compile program
    let program: Program<
        p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
    > = builder.compile_isa();

    (program, witness_stream)
}

#[test]
fn test_zkvm_proof_verifier() {
    let (program, witness) = build_zkvm_proof_verifier_test();

    // let system_config = SystemConfig::default()
    //     .with_public_values(4)
    //     .with_max_segment_len((1 << 25) - 100);
    // let config = NativeConfig::new(system_config, Native);

    // let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
    // executor.execute(program, witness).unwrap();
}
