use crate::basefold_verifier::basefold::BasefoldCommitment;
use crate::basefold_verifier::query_phase::QueryPhaseVerifierInput;
use crate::tower_verifier::binding::{IOPProverMessage, IOPProverMessageVec};
use crate::zkvm_verifier::binding::ZKVMProofInput;
use crate::zkvm_verifier::binding::{TowerProofInput, ZKVMChipProofInput, E, F};
use crate::zkvm_verifier::verifier::verify_zkvm_proof;
use ceno_mle::util::ceil_log2;
use ff_ext::BabyBearExt4;
use itertools::Itertools;
use mpcs::{Basefold, BasefoldRSParams};
use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
use openvm_native_circuit::{Native, NativeConfig};
use openvm_native_compiler::{
    asm::AsmBuilder,
    conversion::{convert_program, CompilerOptions},
    prelude::AsmCompiler,
};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_backend::config::StarkGenericConfig;
use openvm_stark_sdk::config::setup_tracing_with_log_level;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Config, p3_baby_bear::BabyBear,
};
use p3_fri::prover;
use std::fs::File;

type SC = BabyBearPoseidon2Config;
type EF = <SC as StarkGenericConfig>::Challenge;

use ceno_zkvm::{
    scheme::{verifier::ZKVMVerifier, ZKVMProof},
    structs::ZKVMVerifyingKey,
};

pub fn parse_zkvm_proof_import(
    zkvm_proof: ZKVMProof<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
    verifier: &ZKVMVerifier<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
) -> ZKVMProofInput {
    let raw_pi = zkvm_proof
        .raw_pi
        .iter()
        .map(|m_vec| {
            m_vec
                .iter()
                .map(|m| {
                    let f_v: F =
                        serde_json::from_value(serde_json::to_value(m.clone()).unwrap()).unwrap();
                    f_v
                })
                .collect::<Vec<F>>()
        })
        .collect::<Vec<Vec<F>>>();

    let pi_evals = zkvm_proof
        .pi_evals
        .iter()
        .map(|e| {
            let e_v: E = serde_json::from_value(serde_json::to_value(e.clone()).unwrap()).unwrap();
            e_v
        })
        .collect::<Vec<E>>();

    let mut chip_proofs: Vec<ZKVMChipProofInput> = vec![];
    for (chip_id, chip_proof) in &zkvm_proof.chip_proofs {
        let mut record_r_out_evals: Vec<Vec<E>> = vec![];
        let mut record_w_out_evals: Vec<Vec<E>> = vec![];
        let mut record_lk_out_evals: Vec<Vec<E>> = vec![];

        let record_r_out_evals_len: usize = chip_proof.r_out_evals.len();
        for v_vec in &chip_proof.r_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E =
                    serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_r_out_evals.push(arr);
        }
        let record_w_out_evals_len: usize = chip_proof.w_out_evals.len();
        for v_vec in &chip_proof.w_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E =
                    serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_w_out_evals.push(arr);
        }
        let record_lk_out_evals_len: usize = chip_proof.lk_out_evals.len();
        for v_vec in &chip_proof.lk_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E =
                    serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_lk_out_evals.push(arr);
        }

        // Tower proof
        let mut tower_proof = TowerProofInput::default();
        let mut proofs: Vec<IOPProverMessageVec> = vec![];

        for proof in &chip_proof.tower_proof.proofs {
            let mut proof_messages: Vec<E> = vec![];
            let mut prover_message_size = None;
            for m in proof {
                let mut evaluations_vec: Vec<E> = vec![];

                for v in &m.evaluations {
                    let v_e: E =
                        serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                    evaluations_vec.push(v_e);
                }
                if let Some(size) = prover_message_size {
                    assert_eq!(size, evaluations_vec.len());
                } else {
                    prover_message_size = Some(evaluations_vec.len());
                }
                proof_messages.extend_from_slice(&evaluations_vec);
            }
            proofs.push(IOPProverMessageVec {
                prover_message_size: prover_message_size.unwrap(),
                data: proof_messages,
            });
        }
        tower_proof.num_proofs = proofs.len();
        tower_proof.proofs = proofs;

        let mut prod_specs_eval: Vec<Vec<Vec<E>>> = vec![];
        for inner_val in &chip_proof.tower_proof.prod_specs_eval {
            let mut inner_v: Vec<Vec<E>> = vec![];
            for inner_evals_val in inner_val {
                let mut inner_evals_v: Vec<E> = vec![];

                for v in inner_evals_val {
                    let v_e: E =
                        serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                    inner_evals_v.push(v_e);
                }
                inner_v.push(inner_evals_v);
            }
            prod_specs_eval.push(inner_v);
        }
        tower_proof.num_prod_specs = prod_specs_eval.len();
        tower_proof.prod_specs_eval = prod_specs_eval.into();

        let mut logup_specs_eval: Vec<Vec<Vec<E>>> = vec![];
        for inner_val in &chip_proof.tower_proof.logup_specs_eval {
            let mut inner_v: Vec<Vec<E>> = vec![];
            for inner_evals_val in inner_val {
                let mut inner_evals_v: Vec<E> = vec![];

                for v in inner_evals_val {
                    let v_e: E =
                        serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                    inner_evals_v.push(v_e);
                }
                inner_v.push(inner_evals_v);
            }
            logup_specs_eval.push(inner_v);
        }
        tower_proof.num_logup_specs = logup_specs_eval.len();
        tower_proof.logup_specs_eval = logup_specs_eval.into();

        // main constraint and select sumcheck proof
        let main_sumcheck_proofs = if chip_proof.main_sumcheck_proofs.is_some() {
            let mut main_sumcheck_proofs: Vec<E> = vec![];
            let mut prover_message_size = None;
            for m in chip_proof.main_sumcheck_proofs.as_ref().unwrap() {
                let mut evaluations_vec: Vec<E> = vec![];
                for v in &m.evaluations {
                    let v_e: E =
                        serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                    evaluations_vec.push(v_e);
                }
                main_sumcheck_proofs.extend_from_slice(&evaluations_vec);
                if let Some(size) = prover_message_size {
                    assert_eq!(size, evaluations_vec.len());
                } else {
                    prover_message_size = Some(evaluations_vec.len());
                }
            }
            IOPProverMessageVec {
                prover_message_size: prover_message_size.unwrap(),
                data: main_sumcheck_proofs,
            }
        } else {
            IOPProverMessageVec {
                prover_message_size: 0,
                data: vec![],
            }
        };

        let mut wits_in_evals: Vec<E> = vec![];
        for v in &chip_proof.wits_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            wits_in_evals.push(v_e);
        }

        let mut fixed_in_evals: Vec<E> = vec![];
        for v in &chip_proof.fixed_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            fixed_in_evals.push(v_e);
        }

        chip_proofs.push(ZKVMChipProofInput {
            idx: chip_id.clone(),
            num_instances: chip_proof.num_instances,
            record_r_out_evals_len,
            record_w_out_evals_len,
            record_lk_out_evals_len,
            record_r_out_evals,
            record_w_out_evals,
            record_lk_out_evals,
            tower_proof,
            main_sumcheck_proofs,
            wits_in_evals,
            fixed_in_evals,
        });
    }

    let witin_commit: mpcs::BasefoldCommitment<BabyBearExt4> =
        serde_json::from_value(serde_json::to_value(zkvm_proof.witin_commit).unwrap()).unwrap();
    let witin_commit: BasefoldCommitment = witin_commit.into();

    let pcs_proof = zkvm_proof.opening_proof.into();

    ZKVMProofInput {
        raw_pi,
        pi_evals,
        chip_proofs,
        witin_commit,
        pcs_proof,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use metrics_tracing_context::MetricsLayer;
    use openvm_stark_sdk::config::setup_tracing_with_log_level;
    use tracing_forest::ForestLayer;
    use tracing_subscriber::{layer::SubscriberExt, EnvFilter, Registry};

    pub fn inner_test_thread() {
        setup_tracing_with_log_level(tracing::Level::WARN);

        let proof_path = "./src/e2e/encoded/proof.bin";
        let vk_path = "./src/e2e/encoded/vk.bin";

        let zkvm_proof: ZKVMProof<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>> =
            bincode::deserialize_from(File::open(proof_path).expect("Failed to open proof file"))
                .expect("Failed to deserialize proof file");

        let vk: ZKVMVerifyingKey<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>> =
            bincode::deserialize_from(File::open(vk_path).expect("Failed to open vk file"))
                .expect("Failed to deserialize vk file");

        let verifier = ZKVMVerifier::new(vk);
        let zkvm_proof_input = parse_zkvm_proof_import(zkvm_proof, &verifier);

        // OpenVM DSL
        let mut builder = AsmBuilder::<F, EF>::default();

        // Obtain witness inputs
        builder.cycle_tracker_start("Read");
        let zkvm_proof_input_variables = ZKVMProofInput::read(&mut builder);
        builder.cycle_tracker_end("Read");
        builder.cycle_tracker_start("ZKVM verifier");
        verify_zkvm_proof(&mut builder, zkvm_proof_input_variables, &verifier);
        builder.cycle_tracker_end("ZKVM verifier");
        builder.halt();

        // Pass in witness stream
        let mut witness_stream: Vec<
            Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
        > = Vec::new();

        witness_stream.extend(zkvm_proof_input.write());

        // Compile program
        let options = CompilerOptions::default().with_cycle_tracker();
        let mut compiler = AsmCompiler::new(options.word_size);
        compiler.build(builder.operations);
        let asm_code = compiler.code();

        // _debug: print out assembly
        /*
        println!("=> AssemblyCode:");
        println!("{asm_code}");
        return ();
        */

        let program: Program<
            p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
        > = convert_program(asm_code, options);
        let mut system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100);
        system_config.profiling = true;
        let config = NativeConfig::new(system_config, Native);

        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);

        let res = executor
            .execute_and_then(program, witness_stream, |_, seg| Ok(seg), |err| err)
            .unwrap();

        for (i, seg) in res.iter().enumerate() {
            println!("=> segment {:?} metrics: {:?}", i, seg.metrics);
        }
    }

    #[test]
    pub fn test_zkvm_proof_verifier_from_bincode_exports() {
        let stack_size = 64 * 1024 * 1024; // 64 MB

        // Set up tracing:
        let env_filter =
            EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info,p3_=warn"));
        let subscriber = Registry::default()
            .with(env_filter)
            .with(ForestLayer::default())
            .with(MetricsLayer::new());
        tracing::subscriber::set_global_default(subscriber).unwrap();

        let handler = std::thread::Builder::new()
            .stack_size(stack_size)
            .spawn(inner_test_thread)
            .expect("Failed to spawn thread");

        handler.join().expect("Thread panicked");
    }
}
