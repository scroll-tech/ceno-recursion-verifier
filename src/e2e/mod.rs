use crate::tower_verifier::binding::IOPProverMessage;
use crate::zkvm_verifier::binding::ZKVMProofInput;
use crate::zkvm_verifier::binding::{
    TowerProofInput, ZKVMOpcodeProofInput, ZKVMTableProofInput, E, F,
};
use crate::zkvm_verifier::verifier::verify_zkvm_proof;
use ff_ext::BabyBearExt4;
use itertools::Itertools;
use mpcs::BasefoldCommitment;
use mpcs::{Basefold, BasefoldRSParams};
use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
use openvm_native_circuit::{Native, NativeConfig};
use openvm_native_compiler::ir::DIGEST_SIZE;
use openvm_native_compiler::{asm::AsmBuilder, conversion::CompilerOptions};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_backend::config::StarkGenericConfig;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Config, p3_baby_bear::BabyBear,
};
use p3_matrix::dense::DenseMatrix;
use std::collections::HashMap;
use std::fs::File;
use crate::basefold::binding::{BasefoldProofInput, BatchOpening, CommitPhaseProofStep, DenseMatrixInput, Hash, QueryOpeningProof, TrivialProofInput, CircuitIndexMeta};
const BASECODE_MSG_SIZE_LOG: usize = 7;

type SC = BabyBearPoseidon2Config;
type EF = <SC as StarkGenericConfig>::Challenge;

use ceno_zkvm::{
    scheme::{verifier::ZKVMVerifier, ZKVMProof},
    structs::ZKVMVerifyingKey,
};

#[derive(Debug)]
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
        let mut record_r_out_evals: Vec<E> = vec![];
        let mut record_w_out_evals: Vec<E> = vec![];
        for v in &opcode_proof.record_r_out_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            record_r_out_evals.push(v_e);
        }
        for v in &opcode_proof.record_w_out_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            record_w_out_evals.push(v_e);
        }

        // logup sum at layer 1
        let lk_p1_out_eval: E =
            serde_json::from_value(serde_json::to_value(opcode_proof.lk_p1_out_eval).unwrap())
                .unwrap();
        let lk_p2_out_eval: E =
            serde_json::from_value(serde_json::to_value(opcode_proof.lk_p2_out_eval).unwrap())
                .unwrap();
        let lk_q1_out_eval: E =
            serde_json::from_value(serde_json::to_value(opcode_proof.lk_q1_out_eval).unwrap())
                .unwrap();
        let lk_q2_out_eval: E =
            serde_json::from_value(serde_json::to_value(opcode_proof.lk_q2_out_eval).unwrap())
                .unwrap();

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
        let mut main_sel_sumcheck_proofs: Vec<IOPProverMessage> = vec![];
        for m in &opcode_proof.main_sel_sumcheck_proofs {
            let mut evaluations_vec: Vec<E> = vec![];
            for v in &m.evaluations {
                let v_e: E =
                    serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
                evaluations_vec.push(v_e);
            }
            main_sel_sumcheck_proofs.push(IOPProverMessage {
                evaluations: evaluations_vec,
            });
        }
        let mut r_records_in_evals: Vec<E> = vec![];
        for v in &opcode_proof.r_records_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            r_records_in_evals.push(v_e);
        }
        let mut w_records_in_evals: Vec<E> = vec![];
        for v in &opcode_proof.w_records_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            w_records_in_evals.push(v_e);
        }
        let mut lk_records_in_evals: Vec<E> = vec![];
        for v in &opcode_proof.lk_records_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            lk_records_in_evals.push(v_e);
        }
        let mut wits_in_evals: Vec<E> = vec![];
        for v in &opcode_proof.wits_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v.clone()).unwrap()).unwrap();
            wits_in_evals.push(v_e);
        }

        opcode_proofs_vec.push(ZKVMOpcodeProofInput {
            idx: opcode_id.clone(),
            num_instances: opcode_num_instances_lookup.get(opcode_id).unwrap().clone(),
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
            wits_in_evals,
        });
    }

    let mut table_proofs_vec: Vec<ZKVMTableProofInput> = vec![];
    for (table_id, table_proof) in &zkvm_proof.table_proofs {
        let mut r_out_evals: Vec<E> = vec![];
        let mut w_out_evals: Vec<E> = vec![];
        let mut lk_out_evals: Vec<E> = vec![];

        for v in &table_proof.r_out_evals {
            r_out_evals.push(serde_json::from_value(serde_json::to_value(v[0]).unwrap()).unwrap());
            r_out_evals.push(serde_json::from_value(serde_json::to_value(v[1]).unwrap()).unwrap());
        }
        for v in &table_proof.w_out_evals {
            w_out_evals.push(serde_json::from_value(serde_json::to_value(v[0]).unwrap()).unwrap());
            w_out_evals.push(serde_json::from_value(serde_json::to_value(v[1]).unwrap()).unwrap());
        }
        let compressed_rw_out_len: usize = r_out_evals.len() / 2;
        for v in &table_proof.lk_out_evals {
            lk_out_evals.push(serde_json::from_value(serde_json::to_value(v[0]).unwrap()).unwrap());
            lk_out_evals.push(serde_json::from_value(serde_json::to_value(v[1]).unwrap()).unwrap());
            lk_out_evals.push(serde_json::from_value(serde_json::to_value(v[2]).unwrap()).unwrap());
            lk_out_evals.push(serde_json::from_value(serde_json::to_value(v[3]).unwrap()).unwrap());
        }
        let compressed_lk_out_len: usize = lk_out_evals.len() / 4;

        let mut has_same_r_sumcheck_proofs: usize = 0;
        let mut same_r_sumcheck_proofs: Vec<IOPProverMessage> = vec![];
        if table_proof.same_r_sumcheck_proofs.is_some() {
            for m in table_proof.same_r_sumcheck_proofs.as_ref().unwrap() {
                let mut evaluation_vec: Vec<E> = vec![];
                for v in &m.evaluations {
                    let v_e: E = serde_json::from_value(serde_json::to_value(v).unwrap()).unwrap();
                    evaluation_vec.push(v_e);
                }
                same_r_sumcheck_proofs.push(IOPProverMessage {
                    evaluations: evaluation_vec,
                });
            }
        } else {
            has_same_r_sumcheck_proofs = 0;
        }

        let mut rw_in_evals: Vec<E> = vec![];
        for v in &table_proof.rw_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v).unwrap()).unwrap();
            rw_in_evals.push(v_e);
        }
        let mut lk_in_evals: Vec<E> = vec![];
        for v in &table_proof.lk_in_evals {
            let v_e: E = serde_json::from_value(serde_json::to_value(v).unwrap()).unwrap();
            lk_in_evals.push(v_e);
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

    let witin_commit: BasefoldCommitment<BabyBearExt4> =
        serde_json::from_value(serde_json::to_value(zkvm_proof.witin_commit).unwrap()).unwrap();
    let fixed_commit = verifier.vk.fixed_commit.clone();


    let commits = zkvm_proof.fixed_witin_opening_proof.commits.iter().map(|c| {
        serde_json::from_value(serde_json::to_value(c).unwrap()).unwrap()
    }).collect::<Vec<Hash>>();

    let final_message = zkvm_proof.fixed_witin_opening_proof.final_message.iter().map(|m| {
        m.iter().map(|e| {
            let v_e: E =
                serde_json::from_value(serde_json::to_value(e.clone()).unwrap()).unwrap();
            v_e            
        }).collect::<Vec<E>>()
    }).collect::<Vec<Vec<E>>>();

     let query_opening_proofs: Vec<QueryOpeningProof> = zkvm_proof.fixed_witin_opening_proof.query_opening_proof.iter().map(|q| {
        let witin_base_proof = BatchOpening {
            opened_values: q.witin_base_proof.opened_values.iter().map(|row| {
                row.iter().map(|f| {
                    let f_v: F =
                        serde_json::from_value(serde_json::to_value(f.clone()).unwrap()).unwrap();
                    f_v
                })
                .collect::<Vec<F>>()
            }).collect::<Vec<Vec<F>>>(),
            opening_proof: q.witin_base_proof.opening_proof.iter().map(|p| {
                let mut p_f: [F; DIGEST_SIZE] = [F::default(); DIGEST_SIZE];
                for (idx, f) in p.iter().enumerate() {
                    let f_v: F = serde_json::from_value(serde_json::to_value(f.clone()).unwrap()).unwrap();
                    p_f[idx] = f_v;
                }
                p_f
            }).collect::<Vec<[F; DIGEST_SIZE]>>()
        };

        let fixed_base_proof = if q.fixed_base_proof.is_some() {
            Some(BatchOpening {
                opened_values: q.fixed_base_proof.as_ref().unwrap().opened_values.iter().map(|row| {
                    row.iter().map(|f| {
                        let f_v: F =
                            serde_json::from_value(serde_json::to_value(f.clone()).unwrap()).unwrap();
                        f_v
                    })
                    .collect::<Vec<F>>()
                }).collect::<Vec<Vec<F>>>(),
                opening_proof: q.fixed_base_proof.as_ref().unwrap().opening_proof.iter().map(|p| {
                    let mut p_f: [F; DIGEST_SIZE] = [F::default(); DIGEST_SIZE];
                    for (idx, f) in p.iter().enumerate() {
                        let f_v: F = serde_json::from_value(serde_json::to_value(f.clone()).unwrap()).unwrap();
                        p_f[idx] = f_v;
                    }
                    p_f
                }).collect::<Vec<[F; DIGEST_SIZE]>>()
            })
        } else {
            None
        };

        let commit_phase_openings = q.commit_phase_openings.iter().map(|cpo| {
            let f_e: E = serde_json::from_value(serde_json::to_value(cpo.sibling_value.clone()).unwrap()).unwrap();

            let opening_proof = cpo.opening_proof.iter().map(|p| {
                let mut p_f: [F; DIGEST_SIZE] = [F::default(); DIGEST_SIZE];
                for (idx, f) in p.iter().enumerate() {
                    let f_v: F = serde_json::from_value(serde_json::to_value(f.clone()).unwrap()).unwrap();
                    p_f[idx] = f_v;
                }
                p_f
            })
            .collect::<Vec<[F; DIGEST_SIZE]>>();
            
            CommitPhaseProofStep {
                sibling_value: f_e,
                opening_proof,
            }
        })
        .collect::<Vec<CommitPhaseProofStep>>();

        QueryOpeningProof { 
            witin_base_proof, 
            fixed_base_proof, 
            commit_phase_openings, 
        }
    })
    .collect::<Vec<QueryOpeningProof>>();

    let sumcheck_proof_is_some = zkvm_proof.fixed_witin_opening_proof.sumcheck_proof.is_some();
    let sumcheck_proof: Vec<IOPProverMessage> = if sumcheck_proof_is_some {
        zkvm_proof.fixed_witin_opening_proof.sumcheck_proof.unwrap().iter().map(|p| {
            let evaluations = p.evaluations.iter().map(|e| {
                let v_e: E = serde_json::from_value(serde_json::to_value(e.clone()).unwrap()).unwrap();
                v_e
            }).collect::<Vec<E>>();
            IOPProverMessage { evaluations }
        }).collect::<Vec<IOPProverMessage>>()
    } else {
        vec![]
    };

    let trivial_proof_is_some = zkvm_proof.fixed_witin_opening_proof.trivial_proof.is_some();
    let trivial_proof = if trivial_proof_is_some {
        let matrices = zkvm_proof.fixed_witin_opening_proof.trivial_proof.unwrap().iter().map(|row| {
            row.iter().map(|mtx| {
                let values: Vec<Vec<F>> = mtx.values.chunks(mtx.width).map(|chunk| {
                    let mut v: Vec<F> = Vec::with_capacity(chunk.len());

                    chunk.iter().for_each(|f| {
                        let v_f: F = serde_json::from_value(serde_json::to_value(f.clone()).unwrap()).unwrap();
                        v.push(v_f);
                    });

                    v
                }).collect::<Vec<Vec<F>>>();

                DenseMatrixInput { values }
            })
            .collect::<Vec<DenseMatrixInput>>()
        })
        .collect::<Vec<Vec<DenseMatrixInput>>>();

        TrivialProofInput {
            rows: matrices.len(),
            matrices,
        }
    } else {
        TrivialProofInput::default()
    };

    // preprocess data into respective group, in particularly, trivials vs non-trivials
    let mut circuit_metas = vec![];
    let mut trivial_metas_count: usize = 0;
    let mut metas_count: usize = 0;

    for (idx, &(circuit_index, num_var)) in zkvm_proof.num_instances.iter().enumerate() {
        let (expected_witins_num_poly, expected_fixed_num_poly) =
            &verifier.vk.circuit_num_polys[circuit_index];
        let mut circuit_meta = CircuitIndexMeta {
            order_idx: idx,
            is_trivial: false,
            witin_num_vars: num_var,
            witin_num_polys: *expected_witins_num_poly,
            fixed_num_vars: 0,
            fixed_num_polys: 0,
        };

        // NOTE: for evals, we concat witin with fixed to make process easier
        if num_var <= BASECODE_MSG_SIZE_LOG {
            circuit_meta.is_trivial = true;
            if *expected_fixed_num_poly > 0 {
                circuit_meta.fixed_num_vars = num_var;
                circuit_meta.fixed_num_polys = *expected_fixed_num_poly;
            }
            circuit_metas.push(circuit_meta);
            trivial_metas_count += 1;
        } else {
            if *expected_fixed_num_poly > 0 {
                circuit_meta.fixed_num_vars = num_var;
                circuit_meta.fixed_num_polys = *expected_fixed_num_poly;
            }
            circuit_metas.push(circuit_meta);
            metas_count += 1;
        }
    }

    let fixed_witin_opening_proof = BasefoldProofInput {
        commits,
        final_message,
        query_opening_proofs,
        sumcheck_proof_is_some,
        sumcheck_proof,
        trivial_proof_is_some,
        trivial_proof,
        circuit_metas,
        metas_count,
        trivial_metas_count,
    };

    (
        ZKVMProofInput {
            raw_pi,
            pi_evals,
            opcode_proofs: opcode_proofs_vec,
            table_proofs: table_proofs_vec,
            witin_commit,
            fixed_commit,
            num_instances: zkvm_proof.num_instances.clone(),
            fixed_witin_opening_proof,
        },
        proving_sequence,
    )
}

#[test]
pub fn test_zkvm_proof_verifier_from_bincode_exports() {
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
    let program: Program<
        p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
    > = builder.compile_isa_with_options(CompilerOptions::default().with_cycle_tracker());

    let mut system_config = SystemConfig::default()
        .with_public_values(4)
        .with_max_segment_len((1 << 25) - 100);
    system_config.profiling = true;
    let config = NativeConfig::new(system_config, Native);

    let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
    
    // Alternative execution
    // executor.execute(program, witness_stream).unwrap();

    let res = executor.execute_and_then(
        program,
        witness_stream,
        |_, seg| {
            Ok(seg)
        },
        |err| err,
    ).unwrap();

    for (i, seg) in res.iter().enumerate() {
        // _debug
        // println!("=> segment {:?} metrics: {:?}", i, seg.metrics);
    }
}
