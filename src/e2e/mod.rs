use crate::basefold_verifier::basefold::BasefoldCommitment;
use crate::basefold_verifier::query_phase::QueryPhaseVerifierInput;
use crate::tower_verifier::binding::IOPProverMessage;
use crate::zkvm_verifier::binding::{
    GKRProofInput, LayerProofInput, SumcheckLayerProofInput, TowerProofInput, ZKVMChipProofInput,
    ZKVMProofInput, E, F,
};
use crate::zkvm_verifier::verifier::{verify_gkr_circuit, verify_zkvm_proof};
use ceno_mle::util::ceil_log2;
use ceno_transcript::BasicTranscript;
use ff_ext::BabyBearExt4;
use gkr_iop::gkr::{
    layer::sumcheck_layer::{SumcheckLayer, SumcheckLayerProof},
    GKRCircuit,
};
use itertools::Itertools;
use mpcs::{Basefold, BasefoldRSParams};
use openvm_circuit::arch::{
    instructions::program::Program, verify_single, SystemConfig, VirtualMachine, VmExecutor,
};
use openvm_native_circuit::{Native, NativeConfig};
use openvm_native_compiler::{
    asm::AsmBuilder,
    conversion::{convert_program, CompilerOptions},
    prelude::AsmCompiler,
};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_backend::config::StarkGenericConfig;
use openvm_stark_sdk::{
    config::{
        baby_bear_poseidon2::{BabyBearPoseidon2Config, BabyBearPoseidon2Engine},
        fri_params::standard_fri_params_with_100_bits_conjectured_security,
        setup_tracing_with_log_level, FriParameters,
    },
    engine::StarkFriEngine,
    p3_baby_bear::BabyBear,
};
use std::fs::File;

type SC = BabyBearPoseidon2Config;
type EF = <SC as StarkGenericConfig>::Challenge;

use ceno_zkvm::{
    scheme::{verifier::ZKVMVerifier, ZKVMProof},
    structs::{ComposedConstrainSystem, ZKVMVerifyingKey},
};

pub fn parse_zkvm_proof_import(
    zkvm_proof: ZKVMProof<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
    vk: &ZKVMVerifyingKey<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
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
        let mut proofs: Vec<Vec<IOPProverMessage>> = vec![];

        for proof in &chip_proof.tower_proof.proofs {
            let mut proof_messages: Vec<IOPProverMessage> = vec![];
            for m in proof {
                let mut evaluations_vec: Vec<E> = vec![];

                for v in &m.evaluations {
                    let v_e: E =
                        serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                    evaluations_vec.push(v_e);
                }
                proof_messages.push(IOPProverMessage {
                    evaluations: evaluations_vec,
                });
            }
            proofs.push(proof_messages);
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
        tower_proof.prod_specs_eval = prod_specs_eval;

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
        tower_proof.logup_specs_eval = logup_specs_eval;

        // main constraint and select sumcheck proof
        let mut main_sumcheck_proofs: Vec<IOPProverMessage> = vec![];
        if chip_proof.main_sumcheck_proofs.is_some() {
            for m in chip_proof.main_sumcheck_proofs.as_ref().unwrap() {
                let mut evaluations_vec: Vec<E> = vec![];
                for v in &m.evaluations {
                    let v_e: E =
                        serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                    evaluations_vec.push(v_e);
                }
                main_sumcheck_proofs.push(IOPProverMessage {
                    evaluations: evaluations_vec,
                });
            }
        }

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

        let circuit_name = &vk.circuit_index_to_name[chip_id];
        let circuit_vk = &vk.circuit_vks[circuit_name];

        let composed_cs = circuit_vk.get_cs();
        let num_instances = chip_proof.num_instances;
        let next_pow2_instance = num_instances.next_power_of_two().max(2);
        let log2_num_instances = ceil_log2(next_pow2_instance);
        let num_var_with_rotation = log2_num_instances + composed_cs.rotation_vars().unwrap_or(0);

        let has_gkr_proof = chip_proof.gkr_iop_proof.is_some();
        let mut gkr_iop_proof = GKRProofInput {
            num_var_with_rotation,
            num_instances,
            layer_proofs: vec![],
        };

        if has_gkr_proof {
            let gkr_proof = chip_proof.gkr_iop_proof.clone().unwrap();

            for layer_proof in gkr_proof.0 {
                // rotation
                let (has_rotation, rotation): (usize, SumcheckLayerProofInput) = if let Some(p) =
                    layer_proof.rotation
                {
                    let mut iop_messages: Vec<IOPProverMessage> = vec![];
                    for m in p.proof.proofs {
                        let mut evaluations: Vec<E> = vec![];
                        for e in m.evaluations {
                            let v_e: E =
                                serde_json::from_value(serde_json::to_value(e.clone()).unwrap())
                                    .unwrap();
                            evaluations.push(v_e);
                        }
                        iop_messages.push(IOPProverMessage { evaluations });
                    }
                    let mut evals: Vec<E> = vec![];
                    for e in p.evals {
                        let v_e: E =
                            serde_json::from_value(serde_json::to_value(e.clone()).unwrap())
                                .unwrap();
                        evals.push(v_e);
                    }
                    (
                        1,
                        SumcheckLayerProofInput {
                            proof: iop_messages,
                            evals,
                        },
                    )
                } else {
                    (0, SumcheckLayerProofInput::default())
                };

                // main sumcheck
                let mut iop_messages: Vec<IOPProverMessage> = vec![];
                let mut evals: Vec<E> = vec![];
                for m in layer_proof.main.proof.proofs {
                    let mut evaluations: Vec<E> = vec![];
                    for e in m.evaluations {
                        let v_e: E =
                            serde_json::from_value(serde_json::to_value(e.clone()).unwrap())
                                .unwrap();
                        evaluations.push(v_e);
                    }
                    iop_messages.push(IOPProverMessage { evaluations });
                }
                for e in layer_proof.main.evals {
                    let v_e: E =
                        serde_json::from_value(serde_json::to_value(e.clone()).unwrap()).unwrap();
                    evals.push(v_e);
                }

                let main = SumcheckLayerProofInput {
                    proof: iop_messages,
                    evals,
                };

                gkr_iop_proof.layer_proofs.push(LayerProofInput {
                    has_rotation,
                    rotation,
                    main,
                });
            }
        }

        chip_proofs.push(ZKVMChipProofInput {
            idx: chip_id.clone(),
            num_instances: chip_proof.num_instances,
            num_vars: num_var_with_rotation,
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
            has_gkr_proof,
            gkr_iop_proof,
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

/// Build Ceno's zkVM verifier program from vk in OpenVM's eDSL
pub fn build_zkvm_verifier_program(
    vk: &ZKVMVerifyingKey<E, Basefold<E, BasefoldRSParams>>,
) -> Program<F> {
    let mut builder = AsmBuilder::<F, E>::default();

    let zkvm_proof_input_variables = ZKVMProofInput::read(&mut builder);
    verify_zkvm_proof(&mut builder, zkvm_proof_input_variables, vk);
    builder.halt();

    // Compile program
    #[cfg(feature = "bench-metrics")]
    let options = CompilerOptions::default().with_cycle_tracker();
    #[cfg(not(feature = "bench-metrics"))]
    let options = CompilerOptions::default();
    let mut compiler = AsmCompiler::new(options.word_size);
    compiler.build(builder.operations);
    let asm_code = compiler.code();

    let program: Program<F> = convert_program(asm_code, options);
    program
}

pub fn inner_test_thread() {
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

    // Pass in witness stream
    let mut witness_stream: Vec<Vec<F>> = Vec::new();
    witness_stream.extend(zkvm_proof_input.write());

    let mut system_config = SystemConfig::default()
        .with_public_values(4)
        .with_max_segment_len((1 << 25) - 100);
    system_config.profiling = true;
    let config = NativeConfig::new(system_config, Native);

    let executor = VmExecutor::<F, NativeConfig>::new(config);

    let res = executor
        .execute_and_then(
            program.clone(),
            witness_stream.clone(),
            |_, seg| Ok(seg),
            |err| err,
        )
        .unwrap();

    for (i, seg) in res.iter().enumerate() {
        println!("=> segment {:?} metrics: {:?}", i, seg.metrics);
    }

    let poseidon2_max_constraint_degree = 3;
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
}

#[test]
pub fn test_zkvm_verifier() {
    let stack_size = 64 * 1024 * 1024; // 64 MB

    let handler = std::thread::Builder::new()
        .stack_size(stack_size)
        .spawn(inner_test_thread)
        .expect("Failed to spawn thread");

    handler.join().expect("Thread panicked");
}
