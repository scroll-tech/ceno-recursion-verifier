pub mod aggregate;

#[cfg(test)]
mod tests {
    use crate::zkvm_verifier::binding::{E, F};
    use ceno_zkvm::scheme::ZKVMProof;
    use ceno_zkvm::structs::ZKVMVerifyingKey;
    use mpcs::{Basefold, BasefoldRSParams};
    use openvm_stark_sdk::config::{
        baby_bear_poseidon2::BabyBearPoseidon2Engine,
        fri_params::standard_fri_params_with_100_bits_conjectured_security,
        FriParameters,
    };
    use openvm_sdk::{
        config::{AggConfig, AppConfig, SdkVmConfig}, Sdk, StdIn,
        keygen::AggStarkProvingKey,
        prover::StarkProver,
    };
    use openvm_circuit::arch::instructions::exe::VmExe;
    use openvm_native_recursion::hints::Hintable;
    use crate::e2e::{build_zkvm_verifier_program, parse_zkvm_proof_import};
    use std::fs::File;
    use std::sync::Arc;
    use crate::aggregation::aggregate::compress_to_root_proof;

    pub fn aggregation_inner_thread() {
        let proof_path = "./src/e2e/encoded/proof.bin";
        let vk_path = "./src/e2e/encoded/vk.bin";

        let zkvm_proof: ZKVMProof<E, Basefold<E, BasefoldRSParams>> =
            bincode::deserialize_from(File::open(proof_path).expect("Failed to open proof file"))
                .expect("Failed to deserialize proof file");

        let vk: ZKVMVerifyingKey<E, Basefold<E, BasefoldRSParams>> =
            bincode::deserialize_from(File::open(vk_path).expect("Failed to open vk file"))
                .expect("Failed to deserialize vk file");

        let program = build_zkvm_verifier_program(&vk);
        let exe: VmExe<_> = program.into();

        // Construct zkvm proof input
        let zkvm_proof_input = parse_zkvm_proof_import(zkvm_proof, &vk);
        let mut witness_stream: Vec<Vec<F>> = Vec::new();
        witness_stream.extend(zkvm_proof_input.write());
        let mut stdin = StdIn::default();
        stdin.write(&witness_stream);

        let log_blowup = 1;
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
        let vm_config = SdkVmConfig::builder()
            .system(Default::default())
            .rv32i(Default::default())
            .rv32m(Default::default())
            .io(Default::default())
            .build();
        let app_config = AppConfig::new(fri_params, vm_config);

        let sdk = Sdk::new();
        let app_committed_exe = sdk.commit_app_exe(fri_params, exe).expect("commit_app_exe");
        let app_pk = Arc::new(sdk.app_keygen(app_config).expect("app_keygen"));

        let agg_config = AggConfig::default();
        let (agg_stark_pk, _dummy_internal_proof) =
            AggStarkProvingKey::dummy_proof_and_keygen(agg_config.agg_stark_config);
        let stark_prover: StarkProver<SdkVmConfig, BabyBearPoseidon2Engine> = StarkProver::new(app_pk, app_committed_exe, agg_stark_pk, *sdk.agg_tree_config());
        compress_to_root_proof(stark_prover, stdin);
    }

    #[test]
    pub fn test_aggregation() {
        let stack_size = 64 * 1024 * 1024; // 64 MB

        let handler = std::thread::Builder::new()
            .stack_size(stack_size)
            .spawn(aggregation_inner_thread)
            .expect("Failed to spawn thread");

        handler.join().expect("Thread panicked");
    }
}