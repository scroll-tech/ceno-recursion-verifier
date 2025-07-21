use crate::basefold_verifier::query_phase::QueryPhaseVerifierInput;
use crate::tower_verifier::binding::IOPProverMessage;
use crate::zkvm_verifier::binding::ZKVMProofInput;
use crate::zkvm_verifier::binding::{
    TowerProofInput, ZKVMOpcodeProofInput, ZKVMTableProofInput, E, F,
};
use crate::zkvm_verifier::verifier::verify_zkvm_proof;
use ceno_mle::util::ceil_log2;
use ff_ext::BabyBearExt4;
use itertools::Itertools;
use mpcs::BasefoldCommitment;
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
use std::collections::HashMap;
use std::fs::File;
use std::thread;

type SC = BabyBearPoseidon2Config;
type EF = <SC as StarkGenericConfig>::Challenge;

use ceno_zkvm::{
    scheme::{verifier::ZKVMVerifier, ZKVMProof},
    structs::ZKVMVerifyingKey,
};

#[derive(Debug, Clone)]
pub struct SubcircuitParams {
    pub id: usize,
    pub order_idx: usize,
    pub type_order_idx: usize,
    pub name: String,
    pub num_instances: usize,
    pub is_opcode: bool,
}

pub fn parse_zkvm_proof_import(
    zkvm_proof: ZKVMProof<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
    verifier: &ZKVMVerifier<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
) -> (ZKVMProofInput, Vec<SubcircuitParams>) {
    let subcircuit_names = verifier.vk.circuit_vks.keys().collect_vec();

    let mut opcode_num_instances_lookup: HashMap<usize, usize> = HashMap::new();
    let mut table_num_instances_lookup: HashMap<usize, usize> = HashMap::new();
    for (index, chip_proof) in &zkvm_proof.chip_proofs {
        opcode_num_instances_lookup.insert(index.clone(), chip_proof.num_instances.clone());
    }

    let mut order_idx: usize = 0;
    let mut opcode_order_idx: usize = 0;
    let mut table_order_idx: usize = 0;
    let mut proving_sequence: Vec<SubcircuitParams> = vec![];
    for (index, _) in &zkvm_proof.chip_proofs {
        let name = subcircuit_names[*index].clone();
        proving_sequence.push(SubcircuitParams {
            id: *index,
            order_idx: order_idx.clone(),
            type_order_idx: opcode_order_idx.clone(),
            name: name.clone(),
            num_instances: opcode_num_instances_lookup.get(index).unwrap().clone(),
            is_opcode: true,
        });

        order_idx += 1;
    }

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

    let mut opcode_proofs_vec: Vec<ZKVMOpcodeProofInput> = vec![];
    for (opcode_id, opcode_proof) in &zkvm_proof.opcode_proofs {
        let mut record_r_out_evals: Vec<Vec<E>> = vec![];
        let mut record_w_out_evals: Vec<Vec<E>> = vec![];
        let mut record_lk_out_evals: Vec<Vec<E>> = vec![];

        let record_r_out_evals_len: usize = opcode_proof.r_out_evals.len();
        for v_vec in &opcode_proof.r_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E =
                    serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_r_out_evals.push(arr);
        }
        let record_w_out_evals_len: usize = opcode_proof.w_out_evals.len();
        for v_vec in &opcode_proof.w_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E =
                    serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_w_out_evals.push(arr);
        }
        let record_lk_out_evals_len: usize = opcode_proof.lk_out_evals.len();
        for v_vec in &opcode_proof.lk_out_evals {
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

        for proof in &opcode_proof.tower_proof.proofs {
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
        for inner_val in &opcode_proof.tower_proof.prod_specs_eval {
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
        for inner_val in &opcode_proof.tower_proof.logup_specs_eval {
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
        if opcode_proof.main_sumcheck_proofs.is_some() {
            for m in opcode_proof.main_sumcheck_proofs.as_ref().unwrap() {
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
        for v in &opcode_proof.wits_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            wits_in_evals.push(v_e);
        }

        let mut fixed_in_evals: Vec<E> = vec![];
        for v in &opcode_proof.fixed_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            fixed_in_evals.push(v_e);
        }

        opcode_proofs_vec.push(ZKVMOpcodeProofInput {
            idx: opcode_id.clone(),
            num_instances: opcode_num_instances_lookup.get(opcode_id).unwrap().clone(),
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

    let mut table_proofs_vec: Vec<ZKVMTableProofInput> = vec![];
    for (table_id, table_proof) in &zkvm_proof.table_proofs {
        let mut record_r_out_evals: Vec<Vec<E>> = vec![];
        let mut record_w_out_evals: Vec<Vec<E>> = vec![];
        let mut record_lk_out_evals: Vec<Vec<E>> = vec![];

        let record_r_out_evals_len: usize = table_proof.r_out_evals.len();
        for v_vec in &table_proof.r_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E =
                    serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_r_out_evals.push(arr);
        }
        let record_w_out_evals_len: usize = table_proof.w_out_evals.len();
        for v_vec in &table_proof.w_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E =
                    serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_w_out_evals.push(arr);
        }
        let record_lk_out_evals_len: usize = table_proof.lk_out_evals.len();
        for v_vec in &table_proof.lk_out_evals {
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

        for proof in &table_proof.tower_proof.proofs {
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
        for inner_val in &table_proof.tower_proof.prod_specs_eval {
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
        for inner_val in &table_proof.tower_proof.logup_specs_eval {
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

        let mut fixed_in_evals: Vec<E> = vec![];
        for v in &table_proof.fixed_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            fixed_in_evals.push(v_e);
        }
        let mut wits_in_evals: Vec<E> = vec![];
        for v in &table_proof.wits_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            wits_in_evals.push(v_e);
        }

        let num_instances = table_num_instances_lookup.get(table_id).unwrap().clone();

        table_proofs_vec.push(ZKVMTableProofInput {
            idx: table_id.clone(),
            num_instances,
            record_r_out_evals_len,
            record_w_out_evals_len,
            record_lk_out_evals_len,
            record_r_out_evals,
            record_w_out_evals,
            record_lk_out_evals,
            tower_proof,
            fixed_in_evals,
            wits_in_evals,
        });
    }

    let witin_commit: BasefoldCommitment<BabyBearExt4> =
        serde_json::from_value(serde_json::to_value(zkvm_proof.witin_commit).unwrap()).unwrap();
    let fixed_commit = verifier.vk.fixed_commit.clone();

    let pcs_proof = zkvm_proof.opening_proof;

    // let query_phase_verifier_input = QueryPhaseVerifierInput {
    //     max_num_var,
    //     indices,
    //     final_message,
    //     batch_coeffs,
    //     queries,
    //     fixed_comm,
    //     witin_comm,
    //     circuit_meta,
    //     commits: pcs_proof.commits,
    //     fold_challenges,
    //     sumcheck_messages: pcs_proof.sumcheck_proof.unwrap(),
    //     point_evals,
    // };

    (
        ZKVMProofInput {
            raw_pi,
            pi_evals,
            opcode_proofs: opcode_proofs_vec,
            table_proofs: table_proofs_vec,
            witin_commit,
            fixed_commit,
            num_instances: vec![], // TODO: Fixme
                                   // query_phase_verifier_input,
        },
        proving_sequence,
    )
}

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
    let (zkvm_proof_input, proving_sequence) = parse_zkvm_proof_import(zkvm_proof, &verifier);

    // OpenVM DSL
    let mut builder = AsmBuilder::<F, EF>::default();

    // Obtain witness inputs
    let zkvm_proof_input_variables = ZKVMProofInput::read(&mut builder);
    verify_zkvm_proof(
        &mut builder,
        zkvm_proof_input_variables,
        &verifier,
        proving_sequence,
    );
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

    let handler = thread::Builder::new()
        .stack_size(stack_size)
        .spawn(inner_test_thread)
        .expect("Failed to spawn thread");

    handler.join().expect("Thread panicked");
}
