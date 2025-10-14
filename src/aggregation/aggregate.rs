use openvm_stark_backend::config::StarkGenericConfig;
use openvm_stark_backend::proof::Proof;
use openvm_stark_sdk::config::baby_bear_poseidon2::{BabyBearPoseidon2Engine, BabyBearPermutationConfig};
use openvm_stark_sdk::engine::StarkFriEngine;
use p3_baby_bear::Poseidon2BabyBear;
use crate::zkvm_verifier::binding::{E, F};
use openvm_circuit::arch::{SingleSegmentVmExecutor, VirtualMachine};
use openvm_sdk::{
    config::{AggConfig, AppConfig, SdkVmConfig}, Sdk, StdIn,
    keygen::AggStarkProvingKey,
    prover::StarkProver,
    prover::vm::SingleSegmentVmProver,
};
use openvm_continuations::verifier::{
    internal::types::{InternalVmVerifierInput, VmStarkProof},
    leaf::types::LeafVmVerifierInput,
    root::types::RootVmVerifierInput,
};
use std::fs::File;
use std::io::Write;
use openvm_native_recursion::hints::Hintable;
const NUM_CHILDREN: usize = 2;  // _debug: param
const NUM_CHILDREN_INTERNAL: usize = 2;
use std::time::Instant;

pub fn compress_to_root_proof(
    stark_prover: StarkProver<SdkVmConfig, BabyBearPoseidon2Engine>,
    witness_stream: Vec<Vec<F>>,
) {
    let aggregation_start_timestamp = Instant::now();
    // Generate the continuation proof
    let segmented_continuation_proof = stark_prover.app_prover.generate_app_proof(witness_stream.into());
    println!("Aggregation - Generated segemented (count: {:?}) continuation proof at: {:?}", segmented_continuation_proof.per_segment.len(), aggregation_start_timestamp.elapsed());

    // _debug: export
    let json = serde_json::to_string_pretty(&segmented_continuation_proof).unwrap();
    let mut file = File::create("segmented_continuation_proof.json").expect("Create export proof file");
    file.write_all(json.as_bytes()).expect("Export proof");

    let public_values = segmented_continuation_proof.user_public_values.public_values.clone();
    let leaf_inputs = LeafVmVerifierInput::chunk_continuation_vm_proof(&segmented_continuation_proof, NUM_CHILDREN);

    // Generate leaf proofs
    let leaf_prover = stark_prover.agg_prover.leaf_prover;
    let mut leaf_proofs = leaf_inputs.into_iter().enumerate().map(|(leaf_node_idx, input)| {
            SingleSegmentVmProver::prove(&leaf_prover, input.write_to_stream())
        })
        .collect::<Vec<_>>();
    println!("Aggregation - Generated {:?} leaf proofs at: {:?}", leaf_proofs.len(), aggregation_start_timestamp.elapsed());

    // _debug: export
    leaf_proofs.iter().enumerate().for_each(|(idx, p)| {
        let json = serde_json::to_string_pretty(p).unwrap();
        let mut file = File::create(format!("leaf_proof_{:?}.json", idx)).expect("Create export proof file");
        file.write_all(json.as_bytes()).expect("Export proof");
    });

    // Aggregate tree to root proof
    let internal_prover = stark_prover.agg_prover.internal_prover;
    let mut internal_node_idx = -1;
    let mut internal_node_height = 0;
    let mut proofs = leaf_proofs;

    // We will always generate at least one internal proof, even if there is only one leaf
    // proof, in order to shrink the proof size
    while proofs.len() > 1 || internal_node_height == 0 {
        let internal_inputs = InternalVmVerifierInput::chunk_leaf_or_internal_proofs(
            internal_prover
                .committed_exe
                .get_program_commit()
                .into(),
            &proofs,
            stark_prover.agg_prover.num_children_internal,
        );
        proofs = internal_inputs
            .into_iter()
            .map(|input| {
                internal_node_idx += 1;
                let internal_proof = SingleSegmentVmProver::prove(&internal_prover, input.write());
                println!("Aggregation - Completed internal node (idx: {:?}) at height {:?}: {:?}", internal_node_idx, internal_node_height, aggregation_start_timestamp.elapsed());

                // _debug: export
                let json = serde_json::to_string_pretty(&internal_proof).unwrap();
                let mut file = File::create(format!("internal_proof_{:?}_height_{:?}.json", internal_node_idx, internal_node_height)).expect("Create export proof file");
                file.write_all(json.as_bytes()).expect("Export proof");

                internal_proof
            })
            .collect();
        internal_node_height += 1;
    }
    println!("Aggregation - Final height: {:?}", internal_node_height);
    
    let root_stark_proof = VmStarkProof {
        proof: proofs.pop().unwrap(),
        user_public_values: public_values,
    };

    // _debug: export
    let json = serde_json::to_string_pretty(&root_stark_proof).unwrap();
    let mut file = File::create("root_proof_with_public_values.json").expect("Create export proof file");
    file.write_all(json.as_bytes()).expect("Export proof");

    println!("Aggregation - Completed root proof: {:?}", aggregation_start_timestamp.elapsed());

    // stark_prover.agg_prover.wrap_e2e_stark_proof(root_stark_proof)
    // stark_prover.agg_prover.generate_root_proof_impl(root_verifier_input)
}
    