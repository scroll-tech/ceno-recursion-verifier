use crate::tower_verifier::binding::IOPProverMessage;
use crate::zkvm_verifier::binding::{
    ZKVMProofInput, TowerProofInput, ZKVMOpcodeProofInput, ZKVMTableProofInput, E, F,
    GKRProofInput, LayerProofInput, SumcheckLayerProofInput,
};
use crate::zkvm_verifier::verifier::{verify_zkvm_proof, verify_precompile};
use ceno_mle::util::ceil_log2;
use ff_ext::BabyBearExt4;
use gkr_iop::gkr::layer::sumcheck_layer::{SumcheckLayer, SumcheckLayerProof};
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
use std::thread;
use std::collections::HashMap;
use std::fs::File;

type SC = BabyBearPoseidon2Config;
type EF = <SC as StarkGenericConfig>::Challenge;

use ceno_zkvm::{
    scheme::{verifier::ZKVMVerifier, ZKVMProof},
    structs::{ComposedConstrainSystem, ZKVMVerifyingKey},
};
use gkr_iop::gkr::{GKRCircuit, GKRProof};

#[derive(Debug, Clone)]
pub struct SubcircuitParams {
    pub id: usize,
    pub order_idx: usize,
    pub type_order_idx: usize,
    pub name: String,
    pub num_instances: usize,
    pub is_opcode: bool,
}

/* _debug
pub fn parse_zkvm_proof_import(
    zkvm_proof: ZKVMProof<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
    verifier: &ZKVMVerifier<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
) -> (ZKVMProofInput, Vec<SubcircuitParams>) {
    let subcircuit_names = verifier.vk.circuit_vks.keys().collect_vec();

    let mut opcode_num_instances_lookup: HashMap<usize, usize> = HashMap::new();
    let mut table_num_instances_lookup: HashMap<usize, usize> = HashMap::new();
    for (index, num_instances) in &zkvm_proof.num_instances {
        if let Some(_opcode_proof) = zkvm_proof.opcode_proofs.get(index) {
            opcode_num_instances_lookup.insert(index.clone(), num_instances.clone());
        } else if let Some(_table_proof) = zkvm_proof.table_proofs.get(index) {
            table_num_instances_lookup.insert(index.clone(), num_instances.clone());
        } else {
            unreachable!("respective proof of index {} should exist", index)
        }
    }

    let mut order_idx: usize = 0;
    let mut opcode_order_idx: usize = 0;
    let mut table_order_idx: usize = 0;
    let mut proving_sequence: Vec<SubcircuitParams> = vec![];
    for (index, _) in &zkvm_proof.num_instances {
        let name = subcircuit_names[*index].clone();
        if zkvm_proof.opcode_proofs.get(index).is_some() {
            proving_sequence.push(SubcircuitParams {
                id: *index,
                order_idx: order_idx.clone(),
                type_order_idx: opcode_order_idx.clone(),
                name: name.clone(),
                num_instances: opcode_num_instances_lookup.get(index).unwrap().clone(),
                is_opcode: true,
            });
            opcode_order_idx += 1;
        } else if zkvm_proof.table_proofs.get(index).is_some() {
            proving_sequence.push(SubcircuitParams {
                id: *index,
                order_idx: order_idx.clone(),
                type_order_idx: table_order_idx.clone(),
                name: name.clone(),
                num_instances: table_num_instances_lookup.get(index).unwrap().clone(),
                is_opcode: false,
            });
            table_order_idx += 1;
        } else {
            unreachable!("respective proof of index {} should exist", index)
        }

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
                let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_r_out_evals.push(arr);
        }
        let record_w_out_evals_len: usize = opcode_proof.w_out_evals.len();
        for v_vec in &opcode_proof.w_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_w_out_evals.push(arr);
        }
        let record_lk_out_evals_len: usize = opcode_proof.lk_out_evals.len();
        for v_vec in &opcode_proof.lk_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
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
                let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_r_out_evals.push(arr);
        }
        let record_w_out_evals_len: usize = table_proof.w_out_evals.len();
        for v_vec in &table_proof.w_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                arr.push(v_e);
            }
            record_w_out_evals.push(arr);
        }
        let record_lk_out_evals_len: usize = table_proof.lk_out_evals.len();
        for v_vec in &table_proof.lk_out_evals {
            let mut arr: Vec<E> = vec![];
            for v in v_vec {
                let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
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

    (
        ZKVMProofInput {
            raw_pi,
            pi_evals,
            opcode_proofs: opcode_proofs_vec,
            table_proofs: table_proofs_vec,
            witin_commit,
            fixed_commit,
            num_instances: zkvm_proof.num_instances.clone(),
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
*/

pub fn parse_precompile_proof_variables(
    zkvm_proof: ZKVMProof<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
    verifier: &ZKVMVerifier<BabyBearExt4, Basefold<BabyBearExt4, BasefoldRSParams>>,
) -> (GKRCircuit<BabyBearExt4>, GKRProofInput) {
    let index: usize = 18;
    let proof = &zkvm_proof.chip_proofs[&index];

    let circuit_name = &verifier.vk.circuit_index_to_name[&index];
    let circuit_vk = &verifier.vk.circuit_vks[circuit_name];

    let composed_cs = circuit_vk.get_cs();
    let ComposedConstrainSystem {
        zkvm_v1_css: _,
        gkr_circuit,
    } = &composed_cs;
    let gkr_circuit = gkr_circuit.clone().unwrap();
    let num_instances = proof.num_instances;
    let next_pow2_instance = num_instances.next_power_of_two().max(2);
    let log2_num_instances = ceil_log2(next_pow2_instance);
    let num_var_with_rotation = log2_num_instances + composed_cs.rotation_vars().unwrap_or(0);
    let gkr_proof = proof.gkr_iop_proof.clone().unwrap();

    let mut gkr_proof_input = GKRProofInput {
        num_var_with_rotation,
        layer_proofs: vec![],
    };

    for layer_proof in gkr_proof.0 {
        // rotation
        let (has_rotation, rotation): (usize, SumcheckLayerProofInput) = if let Some(p) = layer_proof.rotation {
            let mut iop_messages: Vec<IOPProverMessage> = vec![];
            for m in p.proof.proofs {
                let mut evaluations: Vec<E> = vec![];
                for e in m.evaluations {
                    let v_e: E =
                        serde_json::from_value(serde_json::to_value(e.clone()).unwrap()).unwrap();
                    evaluations.push(v_e);
                }
                iop_messages.push(IOPProverMessage { evaluations });
            }
            let mut evals: Vec<E> = vec![];
            for e in p.evals {
                let v_e: E =
                    serde_json::from_value(serde_json::to_value(e.clone()).unwrap()).unwrap();
                evals.push(v_e);
            }

            (1, SumcheckLayerProofInput { proof: iop_messages, evals })
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
                    serde_json::from_value(serde_json::to_value(e.clone()).unwrap()).unwrap();
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

        gkr_proof_input.layer_proofs.push(LayerProofInput { has_rotation, rotation, main });
    }

    (gkr_circuit, gkr_proof_input)
}

pub fn precompile_test_thread() {
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

    let (circuit, gkr_proof) = parse_precompile_proof_variables(zkvm_proof, &verifier);
    
    // OpenVM DSL
    let mut builder = AsmBuilder::<F, EF>::default();

    // Obtain witness inputs
    let gkr_proof_input = GKRProofInput::read(&mut builder);
    verify_precompile(&mut builder, circuit, gkr_proof_input);
    builder.halt();

    // Pass in witness stream
    let mut witness_stream: Vec<
        Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
    > = Vec::new();

    witness_stream.extend(gkr_proof.write());

    // Compile program
    let options = CompilerOptions::default().with_cycle_tracker();
    let mut compiler = AsmCompiler::new(options.word_size);
    compiler.build(builder.operations);
    let asm_code = compiler.code();

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
pub fn test_precompile_verification_from_bincode_exports() {
    let stack_size = 64 * 1024 * 1024; // 64 MB

    let handler = thread::Builder::new()
        .stack_size(stack_size)
        .spawn(precompile_test_thread)
        .expect("Failed to spawn thread");

    handler.join().expect("Thread panicked");
}
