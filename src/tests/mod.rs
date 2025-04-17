use crate::json::parser::parse_zkvm_proof_json;
use crate::tower_verifier::binding::F;
use crate::zkvm_verifier::binding::ZKVMProofInput;
use crate::zkvm_verifier::verifier::verify_zkvm_proof;
use mpcs::{Basefold, BasefoldRSParams};
use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
use openvm_native_circuit::{Native, NativeConfig};
use openvm_native_compiler::asm::AsmBuilder;
use openvm_native_recursion::{challenger::duplex::DuplexChallengerVariable, hints::Hintable};
use openvm_stark_backend::config::StarkGenericConfig;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::{default_engine, BabyBearPoseidon2Config},
    p3_baby_bear::BabyBear,
};
use ff_ext::BabyBearExt4;
use itertools::Itertools;
use std::fs;
use ceno_emul::{IterAddresses, Program as CenoProgram, WORD_SIZE, Word};
use mpcs::PolynomialCommitmentScheme;

type SC = BabyBearPoseidon2Config;
type E = BabyBearExt4;
type EF = <SC as StarkGenericConfig>::Challenge;
type Challenger = <SC as StarkGenericConfig>::Challenger;
type B = BabyBear;
type Pcs = Basefold<E, BasefoldRSParams>;

use ceno_zkvm::{
    instructions::riscv::{DummyExtraConfig, MemPadder, MmuConfig, Rv32imConfig},
    scheme::{
        PublicValues, ZKVMProof,
        constants::MAX_NUM_VARIABLES,
        mock_prover::{LkMultiplicityKey, MockProver},
        prover::ZKVMProver,
        verifier::ZKVMVerifier,
    },
    state::GlobalState,
    structs::{
        ProgramParams, ZKVMConstraintSystem, ZKVMFixedTraces, ZKVMProvingKey, ZKVMWitnesses,
    },
    e2e::{Checkpoint, Preset, run_e2e_with_checkpoint, setup_platform, construct_configs, init_mem, ConstraintSystemConfig, InitMemState, generate_fixed_traces},
    tables::{MemFinalRecord, MemInitRecord, ProgramTableCircuit, ProgramTableConfig},
    with_panic_hook,
};

fn build_constraint_system() -> ZKVMVerifier<E, Pcs> {
    let elf_filename = "./src/tests/elf/fibonacci.elf";
    let elf_bytes = fs::read(elf_filename).expect("read elf file");
    let program = CenoProgram::load_elf(&elf_bytes, u32::MAX).unwrap();

    let stack_size = (32000u32).next_multiple_of(WORD_SIZE as u32);
    let heap_size = (131072u32).next_multiple_of(WORD_SIZE as u32);
    let pub_io_size = 16; // TODO: configure.

    let platform = setup_platform(
        Preset::Sp1,
        &program,
        stack_size,
        heap_size,
        pub_io_size,
    );
    let mem_init = init_mem(&program, &platform);
    let pub_io_len = platform.public_io.iter_addresses().len();
    
    let program_params = ProgramParams {
        platform: platform.clone(),
        program_size: program.instructions.len(),
        static_memory_len: mem_init.len(),
        pub_io_len,
    };
    let system_config = construct_configs::<E>(program_params);

    let reg_init = system_config.mmu_config.initial_registers();
    let io_init = MemPadder::init_mem(platform.public_io.clone(), pub_io_len, &[]);
    let init_full_mem = InitMemState {
        mem: mem_init,
        reg: reg_init,
        io: io_init,
        priv_io: vec![],
    };

    // Generate fixed traces
    let zkvm_fixed_traces = generate_fixed_traces(&system_config, &init_full_mem, &program);

    // Keygen
    let pcs_param = Pcs::setup(1 << MAX_NUM_VARIABLES).expect("Basefold PCS setup");
    let (pp, vp) = Pcs::trim(pcs_param, 1 << MAX_NUM_VARIABLES).expect("Basefold trim");
    let pk = system_config
        .zkvm_cs
        .clone()
        .key_gen::<Pcs>(pp.clone(), vp.clone(), zkvm_fixed_traces.clone())
        .expect("keygen failed");
    let vk = pk.get_vk();

    let verifier = ZKVMVerifier::new(vk);

    verifier
}

#[allow(dead_code)]
fn build_zkvm_proof_verifier_test() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
    let ceno_constraint_system = build_constraint_system();

    // OpenVM DSL
    let engine = default_engine();
    let mut builder = AsmBuilder::<F, EF>::default();
    let mut challenger = DuplexChallengerVariable::new(&mut builder);

    // Obtain witness inputs
    let zkvm_proof_input_variables = ZKVMProofInput::read(&mut builder);
    verify_zkvm_proof(&mut builder, &mut challenger, zkvm_proof_input_variables, &ceno_constraint_system);
    builder.halt();

    // Pass in witness stream
    let mut witness_stream: Vec<
        Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
    > = Vec::new();

    let zkvm_proof_input = parse_zkvm_proof_json();
    witness_stream.extend(zkvm_proof_input.write());

    // Compile program
    let program: Program<
        p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
    > = builder.compile_isa();

    (program, witness_stream)
}

#[test]
fn test_zkvm_proof_verifier() {
    let (program, witness) = build_zkvm_proof_verifier_test();

    let system_config = SystemConfig::default()
        .with_public_values(4)
        .with_max_segment_len((1 << 25) - 100);
    let config = NativeConfig::new(system_config, Native);

    let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
    // executor.execute(program, witness).unwrap();
}
