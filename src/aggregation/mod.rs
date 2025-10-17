pub mod aggregate;

#[cfg(test)]
mod tests {
    use crate::zkvm_verifier::binding::{E, F};
    use ceno_zkvm::scheme::ZKVMProof;
    use ceno_zkvm::structs::ZKVMVerifyingKey;
    use mpcs::{Basefold, BasefoldRSParams};
    use openvm_stark_sdk::config::{
        baby_bear_poseidon2::BabyBearPoseidon2Engine,
        FriParameters,
    };
    use openvm_sdk::{
        config::{AggStarkConfig, AppConfig, SdkVmConfig, SdkSystemConfig, DEFAULT_APP_LOG_BLOWUP, DEFAULT_LEAF_LOG_BLOWUP, DEFAULT_INTERNAL_LOG_BLOWUP, DEFAULT_ROOT_LOG_BLOWUP}, keygen::AggStarkProvingKey, prover::StarkProver, Sdk
    };
    use openvm_circuit::arch::{instructions::exe::VmExe, SystemConfig};
    use openvm_native_recursion::hints::Hintable;
    use crate::e2e::{build_zkvm_verifier_program, parse_zkvm_proof_import};
    use std::fs::File;
    use std::sync::Arc;
    use crate::aggregation::aggregate::compress_to_root_proof;
    use openvm_native_compiler::{conversion::CompilerOptions};
    use openvm_sdk::commit::commit_app_exe;
    /* _debug: single proof verification
    use openvm_stark_sdk::engine::StarkFriEngine;
    use openvm_circuit::arch::verify_single;
    use openvm_circuit::arch::VirtualMachine;
    use openvm_native_circuit::{Native, NativeConfig};
    */
    use openvm_stark_sdk::config::setup_tracing_with_log_level;
    use openvm_rv32im_circuit::Rv32ImConfig;

    const NUM_PUB_VALUES: usize = 32;
    const APP_LOG_BLOWUP: usize = 1;
    const LEAF_LOG_BLOWUP: usize = 1;
    const INTERNAL_LOG_BLOWUP: usize = 2;
    const ROOT_LOG_BLOWUP: usize = 3;

    pub fn aggregation_inner_thread() {
        setup_tracing_with_log_level(tracing::Level::WARN);

        let proof_path = "./src/e2e/encoded/proof.bin";
        let vk_path = "./src/e2e/encoded/vk.bin";

        let zkvm_proof: ZKVMProof<E, Basefold<E, BasefoldRSParams>> =
            bincode::deserialize_from(File::open(proof_path).expect("Failed to open proof file"))
                .expect("Failed to deserialize proof file");

        let vk: ZKVMVerifyingKey<E, Basefold<E, BasefoldRSParams>> =
            bincode::deserialize_from(File::open(vk_path).expect("Failed to open vk file"))
                .expect("Failed to deserialize vk file");

        let program = build_zkvm_verifier_program(&vk);
        
        // Construct zkvm proof input
        let zkvm_proof_input = parse_zkvm_proof_import(zkvm_proof, &vk);
        let mut witness_stream: Vec<Vec<F>> = Vec::new();
        witness_stream.extend(zkvm_proof_input.write());

        let sdk = Sdk::new();
        let exe: VmExe<F> = program.into();

        let app_vm_config = SdkVmConfig::builder()
            .system(SdkSystemConfig {
                config: SystemConfig::default()
                    // .with_max_segment_len(500000)    // _debug: param
                    .with_continuations()
                    .with_public_values(NUM_PUB_VALUES),
            })
            .native(Default::default())
            .build();

        let app_config = AppConfig {
            app_fri_params: FriParameters::standard_with_100_bits_conjectured_security(
                APP_LOG_BLOWUP,
            )
            .into(),
            app_vm_config,
            leaf_fri_params: FriParameters::standard_with_100_bits_conjectured_security(
                LEAF_LOG_BLOWUP,
            )
            .into(),
            compiler_options: CompilerOptions {
                enable_cycle_tracker: false,
                ..Default::default()
            },
        };
        let app_pk = Arc::new(sdk.app_keygen(app_config).expect("app_keygen"));
        let app_committed_exe = commit_app_exe(app_pk.app_fri_params(), exe);
        
        let [leaf_fri_params, internal_fri_params, root_fri_params] =
            [LEAF_LOG_BLOWUP, INTERNAL_LOG_BLOWUP, ROOT_LOG_BLOWUP]
                .map(FriParameters::standard_with_100_bits_conjectured_security);

        let agg_stark_config = AggStarkConfig {
            leaf_fri_params,
            internal_fri_params,
            root_fri_params,
            profiling: false,
            compiler_options: CompilerOptions {
                enable_cycle_tracker: false,
                ..Default::default()
            },
            root_max_constraint_degree: root_fri_params.max_constraint_degree(),
            ..Default::default()
        };

        let (agg_stark_pk, _dummy_internal_proof) =
            AggStarkProvingKey::dummy_proof_and_keygen(agg_stark_config);

        let stark_prover: StarkProver<SdkVmConfig, BabyBearPoseidon2Engine> = StarkProver::new(app_pk, app_committed_exe, agg_stark_pk, *sdk.agg_tree_config());
        compress_to_root_proof(stark_prover, witness_stream);

        /* _debug: verify single passes
        let log_blowup = 1;
        let poseidon2_max_constraint_degree: usize = 3;
        let fri_params = if matches!(std::env::var("OPENVM_FAST_TEST"), Ok(x) if &x == "1") {
            FriParameters {
                log_blowup,
                log_final_poly_len: 0,
                num_queries: 10,
                proof_of_work_bits: 0,
            }
        } else {
            standard_fri_params_with_100_bits_conjectured_security(log_blowup)
        };

        let engine = BabyBearPoseidon2Engine::new(fri_params);
        let mut config = NativeConfig::aggregation(0, poseidon2_max_constraint_degree);
        config.system.memory_config.max_access_adapter_n = 16;

        let vm = VirtualMachine::new(engine, config);

        let pk = vm.keygen();
        let result = vm.execute_and_generate(program, witness_stream).unwrap();
        let proofs = vm.prove(&pk, result);
        for proof in proofs {
            verify_single(&vm.engine, &pk.get_vk(), &proof).expect("Verification failed");
        }
        */
    }

    #[test]
    pub fn test_aggregation() {
        let stack_size = 256 * 1024 * 1024; // 64 MB

        let handler = std::thread::Builder::new()
            .stack_size(stack_size)
            .spawn(aggregation_inner_thread)
            .expect("Failed to spawn thread");

        handler.join().expect("Thread panicked");
    }
}