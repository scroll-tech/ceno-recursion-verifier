
use crate::tower_verifier::binding::{IOPProverMessage, Point, TowerVerifierInput, F};
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
use openvm_stark_backend::config::{StarkGenericConfig, Val};
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
use crate::zkvm_verifier::binding::ZKVMProofInput;

type SC = BabyBearPoseidon2Config;
type EF = <SC as StarkGenericConfig>::Challenge;
type Challenger = <SC as StarkGenericConfig>::Challenger;

use ff_ext::BabyBearExt4;
use crate::tower_verifier::binding::E;

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
                print_structure(val, indent + 1);
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

#[derive(Default, Debug)]
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

    // let filename = "zkvm_proof.json";
    // let section = "opcode_proofs";
    // let opcode_idx: usize = 0;
    // let opcode_str = "ADD";

    // let mut file = File::open(filename).unwrap();
    // let mut contents = String::new();
    // file.read_to_string(&mut contents);
    // let data: Value = serde_json::from_str(&contents).unwrap();

    // // Check if the root is an object (it is in this case)
    // if let Some(obj) = data.as_object() {
    //     let mut raw_pi_vec: Vec<Vec<F>> = vec![];

    //     if let Some(raw_pi) = obj.get("raw_pi").and_then(Value::as_array) {
    //         for pi in raw_pi {
    //             let mut sub_pi_vec: Vec<F> = vec![];
    //             let fs = Value::as_array(pi).expect("Correct structure");
    //             for f in fs {
    //                 let f_v: F =
    //                     serde_json::from_value(f.clone()).expect("correct deserlization");
    //                 sub_pi_vec.push(f_v);
    //             }
    //             raw_pi_vec.push(sub_pi_vec);
    //         }
    //         res.raw_pi = raw_pi_vec;
    //     }

    //     // deal with opcode + table proof
    //     let opcode_proofs =
    //         Value::as_object(obj.get(section).expect("section")).expect("section");
    //     let table_proofs =
    //         Value::as_object(obj.get("table_proofs").expect("section")).expect("section");

    //     // Gather opcode proof and table proof commitments
    //     let opcode_keys = vec![
    //         "ADD", "ADDI", "ANDI", "BEQ", "BLTU", "BNE", "JALR", "LW", "ORI", "SB", "SRAI",
    //         "SRLI", "SUB", "SW",
    //     ];
    //     let table_keys = vec![
    //         "OPS_And",
    //         "OPS_Ltu",
    //         "OPS_Or",
    //         "OPS_Pow",
    //         "OPS_Xor",
    //         "PROGRAM",
    //         "RAM_Memory_PubIOTable",
    //         "RAM_Memory_StaticMemTable",
    //         "RAM_Register_RegTable",
    //         "RANGE_U14",
    //         "RANGE_U16",
    //         "RANGE_U5",
    //         "RANGE_U8",
    //     ];

    //     let mut opcode_commits: Vec<BasefoldCommitment<BabyBearExt4>> = vec![];
    //     for key in opcode_keys {
    //         let op_proof = Value::as_array(opcode_proofs.get(key).expect("opcode"))
    //             .expect("opcode_section");
    //         let commit = op_proof[1].get("wits_commit").expect("commitment");
    //         let basefold_cmt: BasefoldCommitment<BabyBearExt4> =
    //             serde_json::from_value(commit.clone()).expect("deserialization");
    //         opcode_commits.push(basefold_cmt);
    //     }
    //     res.opcode_proof_commits = opcode_commits;

    //     let mut table_commits: Vec<BasefoldCommitment<BabyBearExt4>> = vec![];
    //     for key in table_keys {
    //         let tb_proof =
    //             Value::as_array(table_proofs.get(key).expect("table")).expect("table_section");
    //         let commit = tb_proof[1].get("wits_commit").expect("commitment");
    //         let basefold_cmt: BasefoldCommitment<BabyBearExt4> =
    //             serde_json::from_value(commit.clone()).expect("deserialization");
    //         table_commits.push(basefold_cmt);
    //     }
    //     res.table_proof_commits = table_commits;

    //     // Parse out ADD proof for testing
    //     let opcode_proof =
    //         Value::as_array(opcode_proofs.get(opcode_str).expect("opcode_section"))
    //             .expect("opcode_section");

    //     // prod_out_evals
    //     let mut prod_out_evals: Vec<Vec<E>> = vec![];

    //     let mut record_r_out_evals: Vec<E> = vec![];
    //     let record_r_out_evals_v =
    //         Value::as_array(opcode_proof[1].get("record_r_out_evals").expect("section"))
    //             .expect("section");
    //     for e in record_r_out_evals_v {
    //         let e_v: E = serde_json::from_value(e.clone()).expect("conversion");
    //         record_r_out_evals.push(e_v);
    //     }
    //     prod_out_evals.push(record_r_out_evals);

    //     let mut record_w_out_evals: Vec<E> = vec![];
    //     let record_w_out_evals_v =
    //         Value::as_array(opcode_proof[1].get("record_w_out_evals").expect("section"))
    //             .expect("section");
    //     for e in record_w_out_evals_v {
    //         let e_v: E = serde_json::from_value(e.clone()).expect("conversion");
    //         record_w_out_evals.push(e_v);
    //     }
    //     prod_out_evals.push(record_w_out_evals);
    //     res.prod_out_evals = prod_out_evals;

    //     // logup_out_evals
    //     let mut logup_out_evals: Vec<Vec<E>> = vec![];
    //     let mut inner: Vec<E> = vec![];

    //     for label in [
    //         "lk_p1_out_eval",
    //         "lk_p2_out_eval",
    //         "lk_q1_out_eval",
    //         "lk_q2_out_eval",
    //     ] {
    //         let e_v: E =
    //             serde_json::from_value(opcode_proof[1].get(label).expect("section").clone())
    //                 .expect("conversion");
    //         inner.push(e_v);
    //     }
    //     logup_out_evals.push(inner);
    //     res.logup_out_evals = logup_out_evals;

    //     // parse out tower proof fields
    //     let tower_proof =
    //         Value::as_object(opcode_proof[1].get("tower_proof").expect("tower_proof"))
    //             .expect("tower_proof");

    //     let mut proofs: Vec<Vec<IOPProverMessage>> = vec![];
    //     let proofs_section =
    //         Value::as_array(tower_proof.get("proofs").expect("proofs")).expect("proof");
    //     for proof in proofs_section {
    //         let mut proof_messages: Vec<IOPProverMessage> = vec![];
    //         let messages = Value::as_array(proof).expect("messages");
    //         for m in messages {
    //             let mut evaluations_vec: Vec<E> = vec![];
    //             let evaluations = Value::as_array(
    //                 Value::as_object(m)
    //                     .expect("IOPProverMessage")
    //                     .get("evaluations")
    //                     .expect("evaluations"),
    //             )
    //             .expect("evaluations");
    //             for v in evaluations {
    //                 let e_v: E = serde_json::from_value(v.clone()).expect("e");
    //                 evaluations_vec.push(e_v);
    //             }
    //             proof_messages.push(IOPProverMessage {
    //                 evaluations: evaluations_vec,
    //             });
    //             // println!("=> m: {:?}", m);
    //             // println!("=> m parsed evaluations: {:?}", evaluations_vec);
    //         }
    //         proofs.push(proof_messages);
    //     }
    //     res.num_proofs = proofs.len();
    //     res.proofs = proofs;

    //     let mut prod_specs_eval: Vec<Vec<Vec<E>>> = vec![];
    //     let prod_specs_eval_section =
    //         Value::as_array(tower_proof.get("prod_specs_eval").expect("eval")).expect("evals");
    //     for inner in prod_specs_eval_section {
    //         let mut inner_v: Vec<Vec<E>> = vec![];
    //         let v = Value::as_array(inner).expect("inner vec");
    //         for inner_inner in v {
    //             let mut inner_evals_v: Vec<E> = vec![];
    //             let inner_evals = Value::as_array(inner_inner).expect("inner evals vec");
    //             for e in inner_evals {
    //                 let e_v: E = serde_json::from_value(e.clone()).expect("e");
    //                 inner_evals_v.push(e_v);
    //             }
    //             inner_v.push(inner_evals_v);
    //         }
    //         prod_specs_eval.push(inner_v);
    //     }
    //     res.num_prod_specs = prod_specs_eval.len();
    //     res.prod_specs_eval = prod_specs_eval;

    //     let mut logup_specs_eval: Vec<Vec<Vec<E>>> = vec![];
    //     let logup_specs_eval_section =
    //         Value::as_array(tower_proof.get("logup_specs_eval").expect("eval")).expect("evals");
    //     for inner in logup_specs_eval_section {
    //         let mut inner_v: Vec<Vec<E>> = vec![];
    //         let v = Value::as_array(inner).expect("inner vec");
    //         for inner_inner in v {
    //             let mut inner_evals_v: Vec<E> = vec![];
    //             let inner_evals = Value::as_array(inner_inner).expect("inner evals vec");
    //             for e in inner_evals {
    //                 let e_v: E = serde_json::from_value(e.clone()).expect("e");
    //                 inner_evals_v.push(e_v);
    //             }
    //             inner_v.push(inner_evals_v);
    //         }
    //         logup_specs_eval.push(inner_v);
    //     }
    //     res.num_logup_specs = logup_specs_eval.len();
    //     res.logup_specs_eval = logup_specs_eval;

    //     res.num_variables = vec![17, 17, 19];
    //     res.num_fanin = 2;
    //     res.max_num_variables = 19;
    // }

    // // parse out fixed commits
    // let mut vk_file = File::open("circuit_vks_fixed_commits.json").unwrap();
    // let mut vk_contents = String::new();
    // vk_file.read_to_string(&mut vk_contents);
    // let data: Value = serde_json::from_str(&vk_contents).unwrap();

    // let mut circuit_vks_fixed_commits: Vec<BasefoldCommitment<BabyBearExt4>> = vec![];
    // for c in Value::as_array(&data).expect("conversion") {
    //     let cmt: BasefoldCommitment<BabyBearExt4> =
    //         serde_json::from_value(c.clone()).expect("conversion");
    //     circuit_vks_fixed_commits.push(cmt);
    // }
    // res.circuit_vks_fixed_commits = circuit_vks_fixed_commits;

    res
}
