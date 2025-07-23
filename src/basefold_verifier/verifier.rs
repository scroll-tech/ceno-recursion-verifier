use crate::{
    basefold_verifier::query_phase::{batch_verifier_query_phase, QueryPhaseVerifierInputVariable},
    transcript::{transcript_check_pow_witness, transcript_observe_label},
};

use super::{basefold::*, extension_mmcs::*, mmcs::*, rs::*, structs::*, utils::*};
use ff_ext::{BabyBearExt4, ExtensionField, PoseidonField};
use openvm_native_compiler::{asm::AsmConfig, ir::FromConstant, prelude::*};
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::{
    challenger::{
        duplex::DuplexChallengerVariable, CanObserveDigest, CanObserveVariable,
        CanSampleBitsVariable, CanSampleVariable, FeltChallenger,
    },
    hints::{Hintable, VecAutoHintable},
    vars::HintSlice,
};
use openvm_stark_backend::config::Val;
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::FieldAlgebra;
use std::fmt::Debug;

pub type F = BabyBear;
pub type E = BabyBearExt4;
pub type InnerConfig = AsmConfig<F, E>;

pub(crate) fn batch_verifier<C: Config>(
    builder: &mut Builder<C>,
    max_num_var: Var<C::N>,
    rounds: Array<C, RoundVariable<C>>,
    proof: BasefoldProofVariable<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    // The permutation of the dimensions in decreasing order, whose correctness will be checked in the circuit
    perms: Array<C, Array<C, Var<C::N>>>,
) {
    builder.assert_nonzero(&proof.final_message.len());
    let expected_final_message_size: Var<C::N> = builder.eval(Usize::<C::N>::from(1usize)); // TODO: support early stop?
    iter_zip!(builder, proof.final_message).for_each(|ptr_vec, builder| {
        let final_message_len = builder.iter_ptr_get(&proof.final_message, ptr_vec[0]).len();
        builder.assert_eq::<Var<C::N>>(final_message_len, expected_final_message_size);
    });

    builder.assert_nonzero(&proof.sumcheck_proof.len());
    // TODO: get this number from some config instead of hardcoding
    let expected_num_queries: Var<C::N> = builder.eval(Usize::<C::N>::from(100usize));
    builder.assert_eq::<Var<C::N>>(proof.query_opening_proof.len(), expected_num_queries);

    // Compute the total number of polynomials across all rounds
    let total_num_polys: Var<C::N> = builder.eval(Usize::<C::N>::from(0));
    iter_zip!(builder, rounds).for_each(|ptr_vec, builder| {
        let openings = builder.iter_ptr_get(&rounds, ptr_vec[0]).openings;
        iter_zip!(builder, openings).for_each(|ptr_vec_openings, builder| {
            let evals_num = builder
                .iter_ptr_get(&openings, ptr_vec_openings[0])
                .point_and_evals
                .evals
                .len();
            builder.assign(&total_num_polys, total_num_polys + evals_num);
        });
    });

    transcript_observe_label(builder, challenger, b"batch coeffs");
    let batch_coeff = challenger.sample_ext(builder);
    let running_coeff =
        <Ext<C::F, C::EF> as FromConstant<C>>::constant(C::EF::from_canonical_usize(1), builder);
    let batch_coeffs: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(total_num_polys);

    iter_zip!(builder, batch_coeffs).for_each(|ptr_vec_batch_coeffs, builder| {
        builder.iter_ptr_set(&batch_coeffs, ptr_vec_batch_coeffs[0], running_coeff);
        builder.assign(&running_coeff, running_coeff * batch_coeff);
    });

    // The max num var is provided by the prover and not guaranteed to be correct.
    // Check that it is greater than or equal to every num var, and that it is
    // equal to at least one of the num vars by multiplying all the differences
    // together and check if the product is zero.
    let diff_product: Var<C::N> = builder.eval(Usize::from(1));
    let max_num_var_plus_one: Var<C::N> = builder.eval(max_num_var + Usize::from(1));
    iter_zip!(builder, rounds).for_each(|ptr_vec, builder| {
        let round = builder.iter_ptr_get(&rounds, ptr_vec[0]);
        // Need to compute the max num var for each round separately. This time
        // don't need to provide by hint because we have
        // commit.log2_max_codeword_size = max_num_var + rate_log
        // We need to ensure that rate_log < commit.log2_max_codeword_size
        // TODO: rate_log is temporarily hardcoded to 1
        builder.assert_less_than_slow_small_rhs(
            Usize::from(1),
            round.commit.log2_max_codeword_size.clone(),
        );
        let max_num_var_round: Var<C::N> =
            builder.eval(round.commit.log2_max_codeword_size - Usize::from(1));
        // Although max_num_var_round_plus_one is the same as log2_max_codeword_size
        // in the current code, it may not be so when the log rate is updated. So
        // let's keep the code more general for now.
        let max_num_var_round_plus_one: Var<C::N> =
            builder.eval(max_num_var_round + Usize::from(1));
        let diff_product_round: Var<C::N> = builder.eval(Usize::from(1));
        iter_zip!(builder, round.openings).for_each(|ptr_vec_opening, builder| {
            let opening = builder.iter_ptr_get(&round.openings, ptr_vec_opening[0]);
            builder.assert_less_than_slow_bit_decomp(opening.num_var, max_num_var_round_plus_one);
            builder.assign(
                &diff_product_round,
                diff_product_round * (max_num_var_round - opening.num_var),
            );
        });
        // Check that at least one opening.num_var is equal to max_num_var_round
        builder.assert_eq::<Var<C::N>>(diff_product_round, Usize::from(0));

        // Now work with the outer max num var
        builder.assert_less_than_slow_bit_decomp(max_num_var_round, max_num_var_plus_one);
        builder.assign(
            &diff_product,
            diff_product * (max_num_var - max_num_var_round),
        );
    });
    // Check that at least one max_num_var_round is equal to max_num_var
    builder.assert_eq::<Var<C::N>>(diff_product, Usize::from(0));

    // TODO: num rounds should be max num var - base message size log, but
    // base message size log is 0 for now
    let num_rounds = max_num_var;

    let fold_challenges: Array<C, Ext<_, _>> = builder.dyn_array(max_num_var);
    builder.range(0, num_rounds).for_each(|index_vec, builder| {
        let sumcheck_message = builder.get(&proof.sumcheck_proof, index_vec[0]).evaluations;
        iter_zip!(builder, sumcheck_message).for_each(|ptr_vec_sumcheck_message, builder| {
            let elem = builder.iter_ptr_get(&sumcheck_message, ptr_vec_sumcheck_message[0]);
            let elem_felts = builder.ext2felt(elem);
            challenger.observe_slice(builder, elem_felts);
        });

        transcript_observe_label(builder, challenger, b"commit round");
        let challenge = challenger.sample_ext(builder);
        builder.set(&fold_challenges, index_vec[0], challenge);
        builder
            .if_ne(index_vec[0], num_rounds - Usize::from(1))
            .then(|builder| {
                let commit = builder.get(&proof.commits, index_vec[0]);
                challenger.observe_digest(builder, commit.value.into());
            });
    });

    iter_zip!(builder, proof.final_message).for_each(|ptr_vec_sumcheck_message, builder| {
        // Each final message should contain a single element, since the final
        // message size log is assumed to be zero
        let elems = builder.iter_ptr_get(&proof.final_message, ptr_vec_sumcheck_message[0]);
        let elem = builder.get(&elems, 0);
        let elem_felts = builder.ext2felt(elem);
        challenger.observe_slice(builder, elem_felts);
    });

    transcript_check_pow_witness(builder, challenger, 16, proof.pow_witness); // TODO: avoid hardcoding pow bits
    transcript_observe_label(builder, challenger, b"query indices");
    let queries: Array<C, Var<C::N>> = builder.dyn_array(100); // TODO: avoid hardcoding
    let zero = builder.eval(Usize::from(0));
    builder.range(0, 100).for_each(|index_vec, builder| {
        let number_of_bits = builder.eval_expr(max_num_var + Usize::from(1));
        let query = challenger.sample_bits(builder, number_of_bits);
        // TODO: the index will need to be split back to bits in query phase, so it's
        // probably better to avoid converting bits to integer altogether
        let number_of_bits = builder.eval(max_num_var + Usize::from(1));
        let query = bin_to_dec_le(builder, &query, zero, number_of_bits);
        builder.set(&queries, index_vec[0], query);
    });

    let input = QueryPhaseVerifierInputVariable {
        max_num_var: builder.eval(max_num_var),
        batch_coeffs,
        fold_challenges,
        indices: queries,
        proof,
        rounds,
        perms,
    };
    batch_verifier_query_phase(builder, input);
}

#[cfg(test)]
pub mod tests {
    use std::{cmp::Reverse, collections::BTreeMap, iter::once};

    use ceno_mle::mle::MultilinearExtension;
    use ceno_transcript::{BasicTranscript, Transcript};
    use ff_ext::{BabyBearExt4, FromUniformBytes};
    use itertools::Itertools;
    use mpcs::{
        pcs_batch_commit, pcs_setup, pcs_trim, util::hash::write_digest_to_transcript,
        BasefoldDefault, PolynomialCommitmentScheme,
    };
    use mpcs::{BasefoldRSParams, BasefoldSpec, PCSFriParam};
    use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::AsmBuilder;
    use openvm_native_recursion::challenger::duplex::DuplexChallengerVariable;
    use openvm_native_recursion::hints::Hintable;
    use openvm_stark_backend::p3_challenger::GrindingChallenger;
    use openvm_stark_sdk::config::baby_bear_poseidon2::Challenger;
    use openvm_stark_sdk::p3_baby_bear::BabyBear;
    use p3_field::Field;
    use p3_field::FieldAlgebra;
    use rand::thread_rng;
    use serde::Deserialize;

    type F = BabyBear;
    type E = BabyBearExt4;
    type PCS = BasefoldDefault<E>;

    use super::{batch_verifier, BasefoldProof, BasefoldProofVariable, InnerConfig, RoundVariable};
    use crate::basefold_verifier::basefold::{Round, RoundOpening};
    use crate::basefold_verifier::query_phase::PointAndEvals;
    use crate::{
        basefold_verifier::{
            basefold::BasefoldCommitment,
            query_phase::{BatchOpening, CommitPhaseProofStep, QueryOpeningProof},
            structs::CircuitIndexMeta,
        },
        tower_verifier::binding::{Point, PointAndEval},
    };
    use openvm_native_compiler::{asm::AsmConfig, prelude::*};

    #[derive(Deserialize)]
    pub struct VerifierInput {
        pub max_num_var: usize,
        pub proof: BasefoldProof,
        pub rounds: Vec<Round>,
        pub perms: Vec<Vec<usize>>,
    }

    impl Hintable<InnerConfig> for VerifierInput {
        type HintVariable = VerifierInputVariable<InnerConfig>;

        fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
            let max_num_var = usize::read(builder);
            let proof = BasefoldProof::read(builder);
            let rounds = Vec::<Round>::read(builder);
            let perms = Vec::<Vec<usize>>::read(builder);

            VerifierInputVariable {
                max_num_var,
                proof,
                rounds,
                perms,
            }
        }

        fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
            let mut stream = Vec::new();
            stream.extend(<usize as Hintable<InnerConfig>>::write(&self.max_num_var));
            stream.extend(self.proof.write());
            stream.extend(self.rounds.write());
            stream.extend(self.perms.write());
            stream
        }
    }

    #[derive(DslVariable, Clone)]
    pub struct VerifierInputVariable<C: Config> {
        pub max_num_var: Var<C::N>,
        pub proof: BasefoldProofVariable<C>,
        pub rounds: Array<C, RoundVariable<C>>,
        pub perms: Array<C, Array<C, Var<C::N>>>,
    }

    #[allow(dead_code)]
    pub fn build_batch_verifier(input: VerifierInput) -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        // build test program
        let mut builder = AsmBuilder::<F, E>::default();
        let mut challenger = DuplexChallengerVariable::new(&mut builder);
        let verifier_input = VerifierInput::read(&mut builder);
        batch_verifier(
            &mut builder,
            verifier_input.max_num_var,
            verifier_input.rounds,
            verifier_input.proof,
            &mut challenger,
            verifier_input.perms,
        );
        builder.halt();
        let program = builder.compile_isa();

        let mut witness_stream: Vec<Vec<F>> = Vec::new();
        witness_stream.extend(input.write());
        // witness_stream.push(vec![F::from_canonical_u32(2).inverse()]);

        (program, witness_stream)
    }

    fn construct_test(dimensions: Vec<(usize, usize)>) {
        let mut rng = thread_rng();

        // setup PCS
        let pp = PCS::setup(1 << 20, mpcs::SecurityLevel::Conjecture100bits).unwrap();
        let (pp, vp) = pcs_trim::<E, PCS>(pp, 1 << 20).unwrap();

        // Sort the dimensions decreasingly and compute the permutation array
        let mut dimensions_with_index = dimensions.iter().enumerate().collect::<Vec<_>>();
        dimensions_with_index.sort_by(|(_, (a, _)), (_, (b, _))| b.cmp(a));
        // The perm array should satisfy that: sorted_dimensions[perm[i]] = dimensions[i]
        // However, if we just pick the indices now, we get the inverse permutation:
        // sorted_dimensions[i] = dimensions[perm[i]]
        let perm = dimensions_with_index
            .iter()
            .map(|(i, _)| *i)
            .collect::<Vec<_>>();
        // So we need to invert the permutation
        let mut inverted_perm = vec![0usize; perm.len()];
        for (i, &j) in perm.iter().enumerate() {
            inverted_perm[j] = i;
        }
        let perm = inverted_perm;

        let mut num_total_polys = 0;
        let (matrices, mles): (Vec<_>, Vec<_>) = dimensions
            .into_iter()
            .map(|(num_vars, width)| {
                let m = ceno_witness::RowMajorMatrix::<F>::rand(&mut rng, 1 << num_vars, width);
                let mles = m.to_mles();
                num_total_polys += width;

                (m, mles)
            })
            .unzip();

        // commit to matrices
        let pcs_data = pcs_batch_commit::<E, PCS>(&pp, matrices).unwrap();
        let comm = PCS::get_pure_commitment(&pcs_data);

        let point_and_evals = mles
            .iter()
            .map(|mles| {
                let point = E::random_vec(mles[0].num_vars(), &mut rng);
                let evals = mles.iter().map(|mle| mle.evaluate(&point)).collect_vec();

                (point, evals)
            })
            .collect_vec();

        // batch open
        let mut transcript = BasicTranscript::<E>::new(&[]);
        let rounds = vec![(&pcs_data, point_and_evals.clone())];
        let opening_proof = PCS::batch_open(&pp, rounds, &mut transcript).unwrap();

        // batch verify
        let mut transcript = BasicTranscript::<E>::new(&[]);
        let rounds = vec![(
            comm,
            point_and_evals
                .iter()
                .map(|(point, evals)| (point.len(), (point.clone(), evals.clone())))
                .collect_vec(),
        )];
        PCS::batch_verify(&vp, rounds.clone(), &opening_proof, &mut transcript)
            .expect("Native verification failed");

        let max_num_var = point_and_evals
            .iter()
            .map(|(point, _)| point.len())
            .max()
            .unwrap();

        let perms = vec![perm];

        let verifier_input = VerifierInput {
            max_num_var,
            rounds: rounds
                .iter()
                .map(|round| Round {
                    commit: round.0.clone().into(),
                    openings: round
                        .1
                        .iter()
                        .map(|opening| RoundOpening {
                            num_var: opening.0,
                            point_and_evals: PointAndEvals {
                                point: Point {
                                    fs: opening.1.clone().0,
                                },
                                evals: opening.1.clone().1,
                            },
                        })
                        .collect(),
                })
                .collect(),
            proof: opening_proof.into(),
            perms,
        };

        let (program, witness) = build_batch_verifier(verifier_input);

        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100);
        let config = NativeConfig::new(system_config, Native);

        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
        executor.execute(program.clone(), witness.clone()).unwrap();

        // _debug
        let results = executor.execute_segments(program, witness).unwrap();
        for seg in results {
            println!("=> cycle count: {:?}", seg.metrics.cycle_count);
        }
    }

    #[test]
    fn test_simple_batch() {
        for num_var in 5..20 {
            construct_test(vec![(num_var, 20)]);
        }
    }

    #[test]
    fn test_decreasing_batch() {
        construct_test(vec![
            (14, 20),
            (14, 40),
            (13, 30),
            (12, 30),
            (11, 10),
            (10, 15),
        ]);
    }

    #[test]
    fn test_random_batch() {
        construct_test(vec![(10, 20), (12, 30), (11, 10), (12, 15)]);
    }
}
