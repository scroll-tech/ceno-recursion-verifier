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
use openvm_native_recursion::hints::Hintable;
const NUM_CHILDREN: usize = 2;
const PERM_WIDTH: usize = 16;
const BATCH_SIZE: usize = 2;
const CHANNEL_CAPACITY: usize = 16;
type SC = BabyBearPermutationConfig<Poseidon2BabyBear<PERM_WIDTH>>;
use std::{
    borrow::Borrow,
    collections::BTreeMap,
    env,
    error::Error,
    num::NonZeroUsize,
    path::Path,
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc::{channel, sync_channel},
        Arc, Mutex, OnceLock, Condvar,
    },
    thread,
};

/// A turn-based synchronization primitive.
pub struct TurnBasedSync {
    pub current_turn: Mutex<usize>,
    pub cv: Condvar,
}

impl TurnBasedSync {
    /// Creates a new [TurnBasedSync].
    pub fn new() -> Self {
        TurnBasedSync { current_turn: Mutex::new(0), cv: Condvar::new() }
    }

    /// Waits for the current turn to be equal to the given turn.
    pub fn wait_for_turn(&self, my_turn: usize) {
        let mut turn = self.current_turn.lock().unwrap();
        while *turn != my_turn {
            turn = self.cv.wait(turn).unwrap();
        }
    }

    /// Advances the current turn.
    pub fn advance_turn(&self) {
        let mut turn = self.current_turn.lock().unwrap();
        *turn += 1;
        self.cv.notify_all();
    }
}

enum RecursionInputData<SC: StarkGenericConfig> {
    Leaf(LeafVmVerifierInput<SC>),
    Internal(InternalVmVerifierInput<SC>),
}

pub fn compress_to_root_proof(
    stark_prover: StarkProver<SdkVmConfig, BabyBearPoseidon2Engine>,
    witness_stream: Vec<Vec<F>>,
) {
    let segmented_continuation_proof = stark_prover.app_prover.generate_app_proof(witness_stream.into());
    let public_values = segmented_continuation_proof.user_public_values.public_values.clone();
    let leaf_inputs = LeafVmVerifierInput::chunk_continuation_vm_proof(&segmented_continuation_proof, NUM_CHILDREN);

    // Generate leaf proofs
    let leaf_prover = stark_prover.agg_prover.leaf_prover;

    let mut leaf_proofs = leaf_inputs.into_iter().enumerate().map(|(leaf_node_idx, input)| {
            SingleSegmentVmProver::prove(&leaf_prover, input.write_to_stream())
        })
        .collect::<Vec<_>>();

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
                // info_span!("single_internal_agg", idx = internal_node_idx,).in_scope(|| {})
                SingleSegmentVmProver::prove(&internal_prover, input.write())
            })
            .collect();
        internal_node_height += 1;
    }

    let root_stark_proof = VmStarkProof {
        proof: proofs.pop().unwrap(),
        user_public_values: public_values,
    };

    // stark_prover.agg_prover.wrap_e2e_stark_proof(root_stark_proof)
    // stark_prover.agg_prover.generate_root_proof_impl(root_verifier_input)
}
    