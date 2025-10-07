use openvm_stark_sdk::config::baby_bear_poseidon2::BabyBearPoseidon2Engine;
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

pub fn compress_to_root_proof(
    stark_prover: StarkProver<SdkVmConfig, BabyBearPoseidon2Engine>,
    stdin: StdIn,
) {
    let segmented_continuation_proof = stark_prover.app_prover.generate_app_proof(stdin);
    let public_values = segmented_continuation_proof.user_public_values.public_values.clone();

    // Generate leaf proofs
    let leaf_proofs = stark_prover.agg_prover.generate_leaf_proofs(&segmented_continuation_proof);
    let leaf_prover = stark_prover.agg_prover.leaf_prover;

    let leaf_inputs = LeafVmVerifierInput::chunk_continuation_vm_proof(&segmented_continuation_proof, NUM_CHILDREN);
    let mut leaf_proofs = leaf_inputs.into_iter().enumerate().map(|(leaf_node_idx, input)| {
            // info_span!("single leaf proof generation", idx = leaf_node_idx)
            //     .in_scope(|| ))
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

    // stark_prover.agg_prover.wrap_e2e_stark_proof(e2e_stark_proof)
    // stark_prover.agg_prover.generate_root_proof_impl(root_verifier_input)
}
    
// /// Reduce shards proofs to a single shard proof using the recursion prover.
// #[instrument(name = "compress", level = "info", skip_all)]
// pub fn compress(
//     &self,
//     vk: &SP1VerifyingKey,
//     proof: SP1CoreProof,
//     deferred_proofs: Vec<SP1ReduceProof<InnerSC>>,
//     opts: SP1ProverOpts,
// ) -> Result<SP1ReduceProof<InnerSC>, SP1RecursionProverError> {
//     #[allow(clippy::type_complexity)]
//     enum TracesOrInput {
//         ProgramRecordTraces(
//             Box<(
//                 Arc<RecursionProgram<BabyBear>>,
//                 ExecutionRecord<BabyBear>,
//                 Vec<(String, RowMajorMatrix<BabyBear>)>,
//             )>,
//         ),
//         CircuitWitness(Box<SP1CircuitWitness>),
//     }

//     // The batch size for reducing two layers of recursion.
//     let batch_size = REDUCE_BATCH_SIZE;
//     // The batch size for reducing the first layer of recursion.
//     let first_layer_batch_size = 1;

//     let shard_proofs = &proof.proof.0;

//     // Generate the first layer inputs.
//     let first_layer_inputs =
//         self.get_first_layer_inputs(vk, shard_proofs, &deferred_proofs, first_layer_batch_size);

//     // Calculate the expected height of the tree.
//     let mut expected_height = if first_layer_inputs.len() == 1 { 0 } else { 1 };
//     let num_first_layer_inputs = first_layer_inputs.len();
//     let mut num_layer_inputs = num_first_layer_inputs;
//     while num_layer_inputs > batch_size {
//         num_layer_inputs = num_layer_inputs.div_ceil(2);
//         expected_height += 1;
//     }

//     // Generate the proofs.
//     let span = tracing::Span::current().clone();
//     let (vk, proof) = thread::scope(|s| {
//         let _span = span.enter();

//         // Spawn a worker that sends the first layer inputs to a bounded channel.
//         let input_sync = Arc::new(TurnBasedSync::new());
//         let (input_tx, input_rx) = sync_channel::<(usize, usize, SP1CircuitWitness, bool)>(
//             opts.recursion_opts.checkpoints_channel_capacity,
//         );
//         let input_tx = Arc::new(Mutex::new(input_tx));
//         {
//             let input_tx = Arc::clone(&input_tx);
//             let input_sync = Arc::clone(&input_sync);
//             s.spawn(move || {
//                 for (index, input) in first_layer_inputs.into_iter().enumerate() {
//                     input_sync.wait_for_turn(index);
//                     input_tx.lock().unwrap().send((index, 0, input, false)).unwrap();
//                     input_sync.advance_turn();
//                 }
//             });
//         }

//         // Spawn workers who generate the records and traces.
//         let record_and_trace_sync = Arc::new(TurnBasedSync::new());
//         let (record_and_trace_tx, record_and_trace_rx) =
//             sync_channel::<(usize, usize, TracesOrInput)>(
//                 opts.recursion_opts.records_and_traces_channel_capacity,
//             );
//         let record_and_trace_tx = Arc::new(Mutex::new(record_and_trace_tx));
//         let record_and_trace_rx = Arc::new(Mutex::new(record_and_trace_rx));
//         let input_rx = Arc::new(Mutex::new(input_rx));
//         for _ in 0..opts.recursion_opts.trace_gen_workers {
//             let record_and_trace_sync = Arc::clone(&record_and_trace_sync);
//             let record_and_trace_tx = Arc::clone(&record_and_trace_tx);
//             let input_rx = Arc::clone(&input_rx);
//             let span = tracing::debug_span!("generate records and traces");
//             s.spawn(move || {
//                 let _span = span.enter();
//                 loop {
//                     let received = { input_rx.lock().unwrap().recv() };
//                     if let Ok((index, height, input, false)) = received {
//                         // Get the program and witness stream.
//                         let (program, witness_stream) = tracing::debug_span!(
//                             "get program and witness stream"
//                         )
//                         .in_scope(|| match input {
//                             SP1CircuitWitness::Core(input) => {
//                                 let mut witness_stream = Vec::new();
//                                 Witnessable::<InnerConfig>::write(&input, &mut witness_stream);
//                                 (self.recursion_program(&input), witness_stream)
//                             }
//                             SP1CircuitWitness::Deferred(input) => {
//                                 let mut witness_stream = Vec::new();
//                                 Witnessable::<InnerConfig>::write(&input, &mut witness_stream);
//                                 (self.deferred_program(&input), witness_stream)
//                             }
//                             SP1CircuitWitness::Compress(input) => {
//                                 let mut witness_stream = Vec::new();

//                                 let input_with_merkle = self.make_merkle_proofs(input);

//                                 Witnessable::<InnerConfig>::write(
//                                     &input_with_merkle,
//                                     &mut witness_stream,
//                                 );

//                                 (self.compress_program(&input_with_merkle), witness_stream)
//                             }
//                         });

//                         // Execute the runtime.
//                         let record = tracing::debug_span!("execute runtime").in_scope(|| {
//                             let mut runtime =
//                                 RecursionRuntime::<Val<InnerSC>, Challenge<InnerSC>, _>::new(
//                                     program.clone(),
//                                     self.compress_prover.config().perm.clone(),
//                                 );
//                             runtime.witness_stream = witness_stream.into();
//                             runtime
//                                 .run()
//                                 .map_err(|e| {
//                                     SP1RecursionProverError::RuntimeError(e.to_string())
//                                 })
//                                 .unwrap();
//                             runtime.record
//                         });

//                         // Generate the dependencies.
//                         let mut records = vec![record];
//                         tracing::debug_span!("generate dependencies").in_scope(|| {
//                             self.compress_prover.machine().generate_dependencies(
//                                 &mut records,
//                                 &opts.recursion_opts,
//                                 None,
//                             )
//                         });

//                         // Generate the traces.
//                         let record = records.into_iter().next().unwrap();
//                         let traces = tracing::debug_span!("generate traces")
//                             .in_scope(|| self.compress_prover.generate_traces(&record));

//                         // Wait for our turn to update the state.
//                         record_and_trace_sync.wait_for_turn(index);

//                         // Send the record and traces to the worker.
//                         record_and_trace_tx
//                             .lock()
//                             .unwrap()
//                             .send((
//                                 index,
//                                 height,
//                                 TracesOrInput::ProgramRecordTraces(Box::new((
//                                     program, record, traces,
//                                 ))),
//                             ))
//                             .unwrap();

//                         // Advance the turn.
//                         record_and_trace_sync.advance_turn();
//                     } else if let Ok((index, height, input, true)) = received {
//                         record_and_trace_sync.wait_for_turn(index);

//                         // Send the record and traces to the worker.
//                         record_and_trace_tx
//                             .lock()
//                             .unwrap()
//                             .send((
//                                 index,
//                                 height,
//                                 TracesOrInput::CircuitWitness(Box::new(input)),
//                             ))
//                             .unwrap();

//                         // Advance the turn.
//                         record_and_trace_sync.advance_turn();
//                     } else {
//                         break;
//                     }
//                 }
//             });
//         }

//         // Spawn workers who generate the compress proofs.
//         let proofs_sync = Arc::new(TurnBasedSync::new());
//         let (proofs_tx, proofs_rx) =
//             sync_channel::<(usize, usize, StarkVerifyingKey<InnerSC>, ShardProof<InnerSC>)>(
//                 num_first_layer_inputs * 2,
//             );
//         let proofs_tx = Arc::new(Mutex::new(proofs_tx));
//         let proofs_rx = Arc::new(Mutex::new(proofs_rx));
//         let mut prover_handles = Vec::new();
//         for _ in 0..opts.recursion_opts.shard_batch_size {
//             let prover_sync = Arc::clone(&proofs_sync);
//             let record_and_trace_rx = Arc::clone(&record_and_trace_rx);
//             let proofs_tx = Arc::clone(&proofs_tx);
//             let span = tracing::debug_span!("prove");
//             let handle = s.spawn(move || {
//                 let _span = span.enter();
//                 loop {
//                     let received = { record_and_trace_rx.lock().unwrap().recv() };
//                     if let Ok((index, height, TracesOrInput::ProgramRecordTraces(boxed_prt))) =
//                         received
//                     {
//                         let (program, record, traces) = *boxed_prt;
//                         tracing::debug_span!("batch").in_scope(|| {
//                             // Get the keys.
//                             let (pk, vk) = tracing::debug_span!("Setup compress program")
//                                 .in_scope(|| self.compress_prover.setup(&program));

//                             // Observe the proving key.
//                             let mut challenger = self.compress_prover.config().challenger();
//                             tracing::debug_span!("observe proving key").in_scope(|| {
//                                 pk.observe_into(&mut challenger);
//                             });

//                             #[cfg(feature = "debug")]
//                             self.compress_prover.debug_constraints(
//                                 &self.compress_prover.pk_to_host(&pk),
//                                 vec![record.clone()],
//                                 &mut challenger.clone(),
//                             );

//                             // Commit to the record and traces.
//                             let data = tracing::debug_span!("commit")
//                                 .in_scope(|| self.compress_prover.commit(&record, traces));

//                             // Generate the proof.
//                             let proof = tracing::debug_span!("open").in_scope(|| {
//                                 self.compress_prover.open(&pk, data, &mut challenger).unwrap()
//                             });

//                             // Verify the proof.
//                             #[cfg(feature = "debug")]
//                             self.compress_prover
//                                 .machine()
//                                 .verify(
//                                     &vk,
//                                     &sp1_stark::MachineProof {
//                                         shard_proofs: vec![proof.clone()],
//                                     },
//                                     &mut self.compress_prover.config().challenger(),
//                                 )
//                                 .unwrap();

//                             // Wait for our turn to update the state.
//                             prover_sync.wait_for_turn(index);

//                             // Send the proof.
//                             proofs_tx.lock().unwrap().send((index, height, vk, proof)).unwrap();

//                             // Advance the turn.
//                             prover_sync.advance_turn();
//                         });
//                     } else if let Ok((
//                         index,
//                         height,
//                         TracesOrInput::CircuitWitness(witness_box),
//                     )) = received
//                     {
//                         let witness = *witness_box;
//                         if let SP1CircuitWitness::Compress(inner_witness) = witness {
//                             let SP1CompressWitnessValues { vks_and_proofs, is_complete: _ } =
//                                 inner_witness;
//                             assert!(vks_and_proofs.len() == 1);
//                             let (vk, proof) = vks_and_proofs.last().unwrap();
//                             // Wait for our turn to update the state.
//                             prover_sync.wait_for_turn(index);

//                             // Send the proof.
//                             proofs_tx
//                                 .lock()
//                                 .unwrap()
//                                 .send((index, height, vk.clone(), proof.clone()))
//                                 .unwrap();

//                             // Advance the turn.
//                             prover_sync.advance_turn();
//                         }
//                     } else {
//                         break;
//                     }
//                 }
//             });
//             prover_handles.push(handle);
//         }

//         // Spawn a worker that generates inputs for the next layer.
//         let handle = {
//             let input_tx = Arc::clone(&input_tx);
//             let proofs_rx = Arc::clone(&proofs_rx);
//             let span = tracing::debug_span!("generate next layer inputs");
//             s.spawn(move || {
//                 let _span = span.enter();
//                 let mut count = num_first_layer_inputs;
//                 let mut batch: Vec<(
//                     usize,
//                     usize,
//                     StarkVerifyingKey<InnerSC>,
//                     ShardProof<InnerSC>,
//                 )> = Vec::new();
//                 loop {
//                     if expected_height == 0 {
//                         break;
//                     }
//                     let received = { proofs_rx.lock().unwrap().recv() };
//                     if let Ok((index, height, vk, proof)) = received {
//                         batch.push((index, height, vk, proof));

//                         // If we haven't reached the batch size, continue.
//                         if batch.len() < batch_size {
//                             continue;
//                         }

//                         // Compute whether we're at the last input of a layer.
//                         let mut is_last = false;
//                         if let Some(first) = batch.first() {
//                             is_last = first.1 != height;
//                         }

//                         // If we're at the last input of a layer, we need to only include the
//                         // first input, otherwise we include all inputs.
//                         let inputs =
//                             if is_last { vec![batch[0].clone()] } else { batch.clone() };

//                         let next_input_height = inputs[0].1 + 1;

//                         let is_complete = next_input_height == expected_height;

//                         let vks_and_proofs = inputs
//                             .into_iter()
//                             .map(|(_, _, vk, proof)| (vk, proof))
//                             .collect::<Vec<_>>();
//                         let input = SP1CircuitWitness::Compress(SP1CompressWitnessValues {
//                             vks_and_proofs,
//                             is_complete,
//                         });

//                         input_sync.wait_for_turn(count);
//                         input_tx
//                             .lock()
//                             .unwrap()
//                             .send((count, next_input_height, input, is_last))
//                             .unwrap();
//                         input_sync.advance_turn();
//                         count += 1;

//                         // If we're at the root of the tree, stop generating inputs.
//                         if is_complete {
//                             break;
//                         }

//                         // If we were at the last input of a layer, we keep everything but the
//                         // first input. Otherwise, we empty the batch.
//                         if is_last {
//                             batch = vec![batch[1].clone()];
//                         } else {
//                             batch = Vec::new();
//                         }
//                     } else {
//                         break;
//                     }
//                 }
//             })
//         };

//         // Wait for all the provers to finish.
//         drop(input_tx);
//         drop(record_and_trace_tx);
//         drop(proofs_tx);

//         for handle in prover_handles {
//             handle.join().unwrap();
//         }
//         handle.join().unwrap();
//         tracing::debug!("joined handles");

//         let (_, _, vk, proof) = proofs_rx.lock().unwrap().recv().unwrap();
//         (vk, proof)
//     });

//     Ok(SP1ReduceProof { vk, proof })
// }
