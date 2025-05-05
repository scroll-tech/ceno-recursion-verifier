/*
use crate::constants::{OPCODE_KEYS, TABLE_KEYS};
use crate::tower_verifier::binding::{IOPProverMessage, Point, TowerVerifierInput, F};
use crate::zkvm_verifier::binding::{
    TowerProofInput, ZKVMOpcodeProofInput, ZKVMProofInput, ZKVMTableProofInput,
};
use ceno_zkvm::scheme::{verifier, ZKVMProof};
use mpcs::{Basefold, BasefoldCommitment, BasefoldRSParams};
use openvm::io::println;
use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
use openvm_native_circuit::{Native, NativeConfig};
use openvm_native_compiler::asm::{AsmBuilder, AsmConfig};
use openvm_native_compiler::prelude::*;
use openvm_native_recursion::challenger::ChallengerVariable;
use openvm_native_recursion::challenger::FeltChallenger;
use openvm_native_recursion::{
    challenger::{duplex::DuplexChallengerVariable, CanObserveVariable, CanSampleVariable},
    fri::witness,
    hints::Hintable,
    types::InnerConfig,
};
use openvm_stark_backend::config::StarkGenericConfig;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::{default_engine, BabyBearPoseidon2Config},
    p3_baby_bear::BabyBear,
};
use p3_field::{
    extension::BinomialExtensionField, FieldAlgebra, FieldExtensionAlgebra, PrimeField32,
    PrimeField64,
};
use p3_util::array_serialization::deserialize;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::io::Read;
use std::{default, fs::File};

type SC = BabyBearPoseidon2Config;
type EF = <SC as StarkGenericConfig>::Challenge;
type Challenger = <SC as StarkGenericConfig>::Challenger;

use crate::tower_verifier::binding::E;
use ff_ext::BabyBearExt4;

type B = BabyBear;
type Pcs = Basefold<E, BasefoldRSParams>;

fn read_json() -> Value {
    let mut file = File::open("zkvm_proof.json").unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents);
    serde_json::from_str(&contents).unwrap()
}

fn print_structure(value: &Value, indent: usize) {
    let recursive = false;
    // Generate indentation for pretty printing
    let indent_str = "  ".repeat(indent);

    match value {
        // If it's an object, recursively print each key-value pair's type
        Value::Object(obj) => {
            println!("{}Object ({} fields):", indent_str, obj.len());
            for (key, val) in obj {
                println!("{}  {}: ", indent_str, key);
                if recursive {
                    print_structure(val, indent + 1);
                }
            }
        }

        // If it's an array, recursively print the type of each item
        Value::Array(arr) => {
            println!("{}Array ({} elements):", indent_str, arr.len());
            for (i, item) in arr.iter().enumerate() {
                println!("{}  [{}]:", indent_str, i);
                if recursive {
                    print_structure(item, indent + 1);
                }
            }
        }

        // If it's a string, print its type
        Value::String(_) => {
            println!("{}String", indent_str);
        }

        // If it's a number (integer or float), print its type
        Value::Number(_) => {
            println!("{}Number", indent_str);
        }

        // If it's a boolean, print its type
        Value::Bool(_) => {
            println!("{}Boolean", indent_str);
        }

        // If it's null, print its type
        Value::Null => {
            println!("{}Null", indent_str);
        }
    }
}

pub(crate) struct ZKVMProofJSONParsed {
    raw_pi: Vec<Vec<F>>,

    circuit_vks_fixed_commits: Vec<BasefoldCommitment<BabyBearExt4>>,
    opcode_proof_commits: Vec<BasefoldCommitment<BabyBearExt4>>,
    table_proof_commits: Vec<BasefoldCommitment<BabyBearExt4>>,

    pub prod_out_evals: Vec<Vec<E>>,
    pub logup_out_evals: Vec<Vec<E>>,
    pub num_variables: Vec<usize>,
    pub num_fanin: usize,

    // TowerProof
    pub num_proofs: usize,
    pub num_prod_specs: usize,
    pub num_logup_specs: usize,
    pub max_num_variables: usize,

    proofs: Vec<Vec<IOPProverMessage>>,
    prod_specs_eval: Vec<Vec<Vec<E>>>,
    logup_specs_eval: Vec<Vec<Vec<E>>>,
}

pub fn parse_zkvm_proof_json() -> ZKVMProofInput {
    let mut res = ZKVMProofInput::default();

    let zkvm_proof_filename = "./src/json/data/zkvm_proof.json";
    let vks_filename = "./src/json/data/circuit_vks_fixed_commits.json";

    let mut zkvm_proof_file = File::open(zkvm_proof_filename).unwrap();
    let mut zkvm_proof_content = String::new();
    let _ = zkvm_proof_file.read_to_string(&mut zkvm_proof_content);
    let zkvm_proof_data: Value = serde_json::from_str(&zkvm_proof_content).unwrap();

    // Top level ZKVMProof object mapping
    let zkvm_proof_obj = zkvm_proof_data.as_object().unwrap();

    let opcode_proofs = Value::as_object(zkvm_proof_obj.get("opcode_proofs").unwrap()).unwrap();
    let table_proofs = Value::as_object(zkvm_proof_obj.get("table_proofs").unwrap()).unwrap();

    // Parse out raw_pi vector
    let mut raw_pi_vec: Vec<Vec<F>> = vec![];
    let raw_pi = Value::as_array(zkvm_proof_obj.get("raw_pi").unwrap()).unwrap();
    for pi in raw_pi {
        let mut sub_pi_vec: Vec<F> = vec![];
        let fs = Value::as_array(pi).expect("Correct 4Ext");
        for f in fs {
            let f_v: F = serde_json::from_value(f.clone()).expect("deserialization");
            sub_pi_vec.push(f_v);
        }
        raw_pi_vec.push(sub_pi_vec);
    }
    res.raw_pi = raw_pi_vec;

    // PI evaluations
    let mut pi_evals_vec: Vec<E> = vec![];
    for v in Value::as_array(zkvm_proof_obj.get("pi_evals").unwrap()).unwrap() {
        let v_e: E = serde_json::from_value(v.clone()).unwrap();
        pi_evals_vec.push(v_e);
    }
    res.pi_evals = pi_evals_vec;

    let mut opcode_proofs_vec: Vec<ZKVMOpcodeProofInput> = vec![];
    // Parse out each opcode proof
    for key in OPCODE_KEYS {
        let idx_op_proof = Value::as_array(opcode_proofs.get(key.2).unwrap()).unwrap();
        let idx: usize = serde_json::from_value(idx_op_proof[0].clone()).unwrap();

        let op_proof = &idx_op_proof[1];
        let num_instances: usize =
            serde_json::from_value(op_proof.get("num_instances").unwrap().clone()).unwrap();

        // product constraints
        let mut record_r_out_evals: Vec<E> = vec![];
        let mut record_w_out_evals: Vec<E> = vec![];
        for v in Value::as_array(op_proof.get("record_r_out_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            record_r_out_evals.push(v_e);
        }
        for v in Value::as_array(op_proof.get("record_w_out_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            record_w_out_evals.push(v_e);
        }

        // logup sum at layer 1
        let lk_p1_out_eval: E =
            serde_json::from_value(op_proof.get("lk_p1_out_eval").unwrap().clone()).unwrap();
        let lk_p2_out_eval: E =
            serde_json::from_value(op_proof.get("lk_p2_out_eval").unwrap().clone()).unwrap();
        let lk_q1_out_eval: E =
            serde_json::from_value(op_proof.get("lk_q1_out_eval").unwrap().clone()).unwrap();
        let lk_q2_out_eval: E =
            serde_json::from_value(op_proof.get("lk_q2_out_eval").unwrap().clone()).unwrap();

        // Tower proof
        let mut tower_proof = TowerProofInput::default();
        let tower_proof_obj = Value::as_object(op_proof.get("tower_proof").unwrap()).unwrap();

        let mut proofs: Vec<Vec<IOPProverMessage>> = vec![];
        for proof in Value::as_array(tower_proof_obj.get("proofs").unwrap()).unwrap() {
            let mut proof_messages: Vec<IOPProverMessage> = vec![];
            let messages = Value::as_array(proof).unwrap();

            for m in messages {
                let mut evaluations_vec: Vec<E> = vec![];
                let evaluations =
                    Value::as_array(Value::as_object(m).unwrap().get("evaluations").unwrap())
                        .unwrap();
                for v in evaluations {
                    let e_v: E = serde_json::from_value(v.clone()).unwrap();
                    evaluations_vec.push(e_v);
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
        for inner_val in Value::as_array(tower_proof_obj.get("prod_specs_eval").unwrap()).unwrap() {
            let mut inner_v: Vec<Vec<E>> = vec![];

            for inner_evals_val in Value::as_array(inner_val).unwrap() {
                let mut inner_evals_v: Vec<E> = vec![];

                for e in Value::as_array(inner_evals_val).unwrap() {
                    let e_v: E = serde_json::from_value(e.clone()).unwrap();
                    inner_evals_v.push(e_v);
                }
                inner_v.push(inner_evals_v);
            }
            prod_specs_eval.push(inner_v);
        }
        tower_proof.num_prod_specs = prod_specs_eval.len();
        tower_proof.prod_specs_eval = prod_specs_eval;

        let mut logup_specs_eval: Vec<Vec<Vec<E>>> = vec![];
        for inner_val in Value::as_array(tower_proof_obj.get("logup_specs_eval").unwrap()).unwrap()
        {
            let mut inner_v: Vec<Vec<E>> = vec![];

            for inner_evals_val in Value::as_array(inner_val).unwrap() {
                let mut inner_evals_v: Vec<E> = vec![];

                for e in Value::as_array(inner_evals_val).unwrap() {
                    let e_v: E = serde_json::from_value(e.clone()).unwrap();
                    inner_evals_v.push(e_v);
                }
                inner_v.push(inner_evals_v);
            }
            logup_specs_eval.push(inner_v);
        }
        tower_proof.num_logup_specs = logup_specs_eval.len();
        tower_proof.logup_specs_eval = logup_specs_eval;

        // main constraint and select sumcheck proof
        let mut main_sel_sumcheck_proofs: Vec<IOPProverMessage> = vec![];
        for m in Value::as_array(op_proof.get("main_sel_sumcheck_proofs").unwrap()).unwrap() {
            let mut evaluations_vec: Vec<E> = vec![];
            let evaluations =
                Value::as_array(Value::as_object(m).unwrap().get("evaluations").unwrap()).unwrap();
            for v in evaluations {
                let e_v: E = serde_json::from_value(v.clone()).unwrap();
                evaluations_vec.push(e_v);
            }
            main_sel_sumcheck_proofs.push(IOPProverMessage {
                evaluations: evaluations_vec,
            });
        }
        let mut r_records_in_evals: Vec<E> = vec![];
        for v in Value::as_array(op_proof.get("r_records_in_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            r_records_in_evals.push(v_e);
        }
        let mut w_records_in_evals: Vec<E> = vec![];
        for v in Value::as_array(op_proof.get("w_records_in_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            w_records_in_evals.push(v_e);
        }
        let mut lk_records_in_evals: Vec<E> = vec![];
        for v in Value::as_array(op_proof.get("lk_records_in_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            lk_records_in_evals.push(v_e);
        }

        // _debug
        // PCS
        // let wits_commit: BasefoldCommitment<BabyBearExt4> =
        //     serde_json::from_value(op_proof.get("wits_commit").unwrap().clone()).unwrap();
        let mut wits_in_evals: Vec<E> = vec![];
        for v in Value::as_array(op_proof.get("wits_in_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            wits_in_evals.push(v_e);
        }

        opcode_proofs_vec.push(ZKVMOpcodeProofInput {
            idx,
            num_instances,
            record_r_out_evals,
            record_w_out_evals,
            lk_p1_out_eval,
            lk_p2_out_eval,
            lk_q1_out_eval,
            lk_q2_out_eval,
            tower_proof,
            main_sel_sumcheck_proofs,
            r_records_in_evals,
            w_records_in_evals,
            lk_records_in_evals,
            // wits_commit,
            wits_in_evals,
        });
    }
    res.opcode_proofs = opcode_proofs_vec;

    let mut table_proofs_vec: Vec<ZKVMTableProofInput> = vec![];
    // Parse out each table proof
    for key in TABLE_KEYS {
        let idx_table_proof = Value::as_array(table_proofs.get(key.2).unwrap()).unwrap();
        let idx: usize = serde_json::from_value(idx_table_proof[0].clone()).unwrap();

        let table_proof = &idx_table_proof[1];

        // tower evaluation at layer 1
        let mut r_out_evals: Vec<E> = vec![]; // Vec<[E; 2]>
        let mut w_out_evals: Vec<E> = vec![]; // Vec<[E; 2]>
        let mut lk_out_evals: Vec<E> = vec![]; // Vec<[E; 4]>
        for v in Value::as_array(table_proof.get("r_out_evals").unwrap()).unwrap() {
            let v_e2: [E; 2] = serde_json::from_value(v.clone()).unwrap();
            r_out_evals.push(v_e2[0]);
            r_out_evals.push(v_e2[1]);
        }
        for v in Value::as_array(table_proof.get("w_out_evals").unwrap()).unwrap() {
            let v_e2: [E; 2] = serde_json::from_value(v.clone()).unwrap();
            w_out_evals.push(v_e2[0]);
            w_out_evals.push(v_e2[1]);
        }
        let compressed_rw_out_len: usize = r_out_evals.len() / 2;
        for v in Value::as_array(table_proof.get("lk_out_evals").unwrap()).unwrap() {
            let v_e4: [E; 4] = serde_json::from_value(v.clone()).unwrap();
            lk_out_evals.push(v_e4[0]);
            lk_out_evals.push(v_e4[1]);
            lk_out_evals.push(v_e4[2]);
            lk_out_evals.push(v_e4[3]);
        }
        let compressed_lk_out_len: usize = lk_out_evals.len() / 4;

        // _debug
        let mut has_same_r_sumcheck_proofs: usize = 0;
        let mut same_r_sumcheck_proofs: Vec<IOPProverMessage> = vec![];
        // if same_r_sumcheck_proofs_op.is_some() {
        //     for m in Value::as_array(table_proof.get("same_r_sumcheck_proofs").unwrap()).unwrap() {
        //         let mut evaluations_vec: Vec<E> = vec![];
        //         let evaluations = Value::as_array(
        //             Value::as_object(m).unwrap().get("evaluations").unwrap()
        //         ).unwrap();
        //         for v in evaluations {
        //             let e_v: E = serde_json::from_value(v.clone()).unwrap();
        //             evaluations_vec.push(e_v);
        //         }
        //         same_r_sumcheck_proofs.push(IOPProverMessage { evaluations: evaluations_vec });
        //     }
        // } else {
        //     has_same_r_sumcheck_proofs = 0;
        // }

        let mut rw_in_evals: Vec<E> = vec![];
        for v in Value::as_array(table_proof.get("rw_in_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            rw_in_evals.push(v_e);
        }
        let mut lk_in_evals: Vec<E> = vec![];
        for v in Value::as_array(table_proof.get("lk_in_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            lk_in_evals.push(v_e);
        }

        // Tower proof
        let mut tower_proof = TowerProofInput::default();
        let tower_proof_obj = Value::as_object(table_proof.get("tower_proof").unwrap()).unwrap();

        let mut proofs: Vec<Vec<IOPProverMessage>> = vec![];
        for proof in Value::as_array(tower_proof_obj.get("proofs").unwrap()).unwrap() {
            let mut proof_messages: Vec<IOPProverMessage> = vec![];
            let messages = Value::as_array(proof).unwrap();

            for m in messages {
                let mut evaluations_vec: Vec<E> = vec![];
                let evaluations =
                    Value::as_array(Value::as_object(m).unwrap().get("evaluations").unwrap())
                        .unwrap();
                for v in evaluations {
                    let e_v: E = serde_json::from_value(v.clone()).unwrap();
                    evaluations_vec.push(e_v);
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
        for inner_val in Value::as_array(tower_proof_obj.get("prod_specs_eval").unwrap()).unwrap() {
            let mut inner_v: Vec<Vec<E>> = vec![];

            for inner_evals_val in Value::as_array(inner_val).unwrap() {
                let mut inner_evals_v: Vec<E> = vec![];

                for e in Value::as_array(inner_evals_val).unwrap() {
                    let e_v: E = serde_json::from_value(e.clone()).unwrap();
                    inner_evals_v.push(e_v);
                }
                inner_v.push(inner_evals_v);
            }
            prod_specs_eval.push(inner_v);
        }
        tower_proof.num_prod_specs = prod_specs_eval.len();
        tower_proof.prod_specs_eval = prod_specs_eval;

        let mut logup_specs_eval: Vec<Vec<Vec<E>>> = vec![];
        for inner_val in Value::as_array(tower_proof_obj.get("logup_specs_eval").unwrap()).unwrap()
        {
            let mut inner_v: Vec<Vec<E>> = vec![];

            for inner_evals_val in Value::as_array(inner_val).unwrap() {
                let mut inner_evals_v: Vec<E> = vec![];

                for e in Value::as_array(inner_evals_val).unwrap() {
                    let e_v: E = serde_json::from_value(e.clone()).unwrap();
                    inner_evals_v.push(e_v);
                }
                inner_v.push(inner_evals_v);
            }
            logup_specs_eval.push(inner_v);
        }
        tower_proof.num_logup_specs = logup_specs_eval.len();
        tower_proof.logup_specs_eval = logup_specs_eval;

        let mut rw_hints_num_vars: Vec<usize> = vec![];
        for v in Value::as_array(table_proof.get("rw_hints_num_vars").unwrap()).unwrap() {
            let v_e: usize = serde_json::from_value(v.clone()).unwrap();
            rw_hints_num_vars.push(v_e);
        }
        let mut fixed_in_evals: Vec<E> = vec![];
        for v in Value::as_array(table_proof.get("fixed_in_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            fixed_in_evals.push(v_e);
        }
        let mut wits_in_evals: Vec<E> = vec![];
        for v in Value::as_array(table_proof.get("wits_in_evals").unwrap()).unwrap() {
            let v_e: E = serde_json::from_value(v.clone()).unwrap();
            wits_in_evals.push(v_e);
        }

        table_proofs_vec.push(ZKVMTableProofInput {
            idx,
            r_out_evals,
            w_out_evals,
            compressed_rw_out_len,
            lk_out_evals,
            compressed_lk_out_len,
            has_same_r_sumcheck_proofs,
            same_r_sumcheck_proofs,
            rw_in_evals,
            lk_in_evals,
            tower_proof,
            fixed_in_evals,
            wits_in_evals,
        });
    }
    res.table_proofs = table_proofs_vec;

    // parse out fixed commits
    let mut vk_file = File::open(vks_filename).unwrap();
    let mut vk_contents = String::new();
    let _ = vk_file.read_to_string(&mut vk_contents);
    let data: Value = serde_json::from_str(&vk_contents).unwrap();

    let mut circuit_vks_fixed_commits: Vec<BasefoldCommitment<BabyBearExt4>> = vec![];
    for c in Value::as_array(&data).expect("conversion") {
        let cmt: BasefoldCommitment<BabyBearExt4> =
            serde_json::from_value(c.clone()).expect("conversion");
        circuit_vks_fixed_commits.push(cmt);
    }
    res.circuit_vks_fixed_commits = circuit_vks_fixed_commits;

    res
}
*/
