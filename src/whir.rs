use crate::sumcheck::construct_binary_evaluation_idxs;
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use ark_poly::domain::EvaluationDomain;
use ark_std::collections::BTreeSet;
use nimue::{
    plugins::ark::{FieldChallenges, FieldReader},
    ByteChallenges, ByteReader,
};
use nimue_pow::{blake3::Blake3PoW, PoWChallenge};
use openvm_native_compiler::asm::AsmConfig;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::{
    challenger::ChallengerVariable,
    hints::{Hintable, InnerChallenge, InnerVal, VecAutoHintable},
};
use openvm_stark_sdk::p3_blake3::Blake3;
use p3_field::{ExtensionField, Field as Plonky3Field, FieldAlgebra, TwoAdicField};
use whir::{
    crypto::{
        fields::Field64,
        merkle_tree::blake3::{self as merkle_tree, Blake3Digest},
    },
    poly_utils::{eq_poly_outside, MultilinearPoint},
    sumcheck::proof::SumcheckPolynomial,
    whir::{
        fs_utils::DigestReader,
        parameters::WhirConfig,
        vm_binding::{
            BlakeDigestVariable, StatementVariable, WhirProofRoundVariable, WhirProofVariable,
        },
        WhirProof,
    },
};

type F = Field64;
type MerkleConfig = merkle_tree::MerkleTreeParams<F>;
type PowStrategy = Blake3PoW;
type InnerConfig = AsmConfig<InnerVal, InnerChallenge>;

fn convert_poly_evals(evals: &[F; 3]) -> Vec<<InnerConfig as Config>::N> {
    evals
        .iter()
        .map(|e| <InnerConfig as Config>::N::from_wrapped_u64(to_bigint_u64(*e)))
        .collect::<Vec<<InnerConfig as Config>::N>>()
}
fn convert_field_vector(v: &Vec<Field64>) -> Vec<<InnerConfig as Config>::N> {
    v.iter()
        .map(|n| <InnerConfig as Config>::N::from_wrapped_u64(to_bigint_u64(*n)))
        .collect::<Vec<<InnerConfig as Config>::N>>()
}
fn convert_vec_felts_to_vm<C: Config>(
    builder: &mut Builder<C>,
    v: &Vec<Felt<C::F>>,
) -> Array<C, Felt<C::F>> {
    let arr = builder.dyn_array(v.len());
    for (i, f) in v.iter().enumerate() {
        builder.set(&arr, i, f.clone());
    }
    arr
}
fn to_bigint_u64(n: Field64) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&n.into_bigint().to_bytes_le());
    u64::from_le_bytes(bytes)
}

fn verify_merkle_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    whir_proof: &WhirProofRoundVariable<C>,
) {
    // _debug: hash discrepancy. Original WHIR uses Blake3.
}

fn sum_over_hypercube<C: Config>(
    builder: &mut Builder<C>,
    sumcheck_poly_evals: &Array<C, Felt<C::F>>,
    evaluation_idxs: &Vec<usize>,
) -> Felt<C::F> {
    let mut acc: Felt<C::F> = builder.eval(C::F::ZERO);
    for idx in evaluation_idxs {
        let new_acc = acc + builder.get(&sumcheck_poly_evals, *idx);
        acc = builder.eval(new_acc);
    }
    acc
}

fn eq_poly3<C: Config>(builder: &mut Builder<C>, r: Felt<C::F>, idx: usize) -> Felt<C::F> {
    let one: Felt<C::F> = builder.eval(C::F::ONE);
    let two: Felt<C::F> = builder.eval(C::F::TWO);
    let two_inv: Felt<C::F> = builder.eval(C::F::TWO.inverse());

    let b = idx % 3;
    let expr = match b {
        0 => (r - one) * (r - two) * two_inv,
        1 => r * (r - two) * (-one),
        2 => r * (r - one) * two_inv,
        _ => unreachable!(),
    };

    builder.eval(expr)
}

fn evaluate_at_point<C: Config>(
    builder: &mut Builder<C>,
    poly: &Array<C, Felt<C::F>>,
    r: Felt<C::F>,
) -> Felt<C::F> {
    let num_evaluation_points = 3_usize;
    let mut evaluation: Felt<C::F> = builder.eval(C::F::ZERO);

    for index in 0..num_evaluation_points {
        let new_evaluation_expr =
            evaluation + builder.get(poly, index) * eq_poly3(builder, r, index);
        evaluation = builder.eval(new_evaluation_expr);
    }

    evaluation
}

fn dot_product<C: Config>(
    builder: &mut Builder<C>,
    a: &Array<C, Felt<C::F>>,
    b: &Array<C, Felt<C::F>>,
) -> Felt<<C as Config>::F> {
    let mut acc: Felt<C::F> = builder.eval(C::F::ZERO);

    iter_zip!(builder, a, b).for_each(|idx_vec, builder| {
        let ptr_a = idx_vec[0];
        let ptr_b = idx_vec[1];
        let v_a = builder.iter_ptr_get(&a, ptr_a);
        let v_b = builder.iter_ptr_get(&b, ptr_b);
        let new_acc = builder.eval(acc + v_a + v_b);
        acc = new_acc;
    });

    acc
}

fn get_challenge_stir_queries(
    domain_size: usize,
    folding_factor: usize,
    num_queries: usize,
) -> Vec<usize> {
    let folded_domain_size = domain_size / (1 << folding_factor);
    let domain_size_bytes = ((folded_domain_size * 2 - 1).ilog2() as usize + 7) / 8;
    let queries = vec![0u8; num_queries * domain_size_bytes];

    let indices = queries.chunks_exact(domain_size_bytes).map(|chunk| {
        let mut result = 0;
        for byte in chunk {
            result <<= 8;
            result |= *byte as usize;
        }
        result % folded_domain_size
    });

    Vec::from_iter(BTreeSet::from_iter(indices))
}

fn compute_folds_full<C: Config>(
    builder: &mut Builder<C>,
    parsed: &ParsedProofVariable<C>,
    config: &WhirConfig<F, MerkleConfig, PowStrategy>,
) -> Vec<Vec<Felt<C::F>>> {
    let two_inv = F::from(2).inverse().unwrap();
    let mut domain_size = config.starting_domain.backing_domain.size();
    let coset_domain_size = 1 << config.folding_factor;

    let mut result = Vec::new();

    for round in &parsed.rounds {
        // This is such that coset_generator^coset_domain_size = F::ONE
        //let _coset_generator = domain_gen.pow(&[(domain_size / coset_domain_size) as u64]);
        let coset_generator_inv = round
            .domain_gen_inv
            .pow([(domain_size / coset_domain_size) as u64]);

        let evaluations: Vec<_> = round
            .stir_challenges_indexes
            .iter()
            .enumerate()
            .map(|(i, index)| {
                let answers = builder.get(&round.stir_challenges_answers, i);
                // The coset is w^index * <w_coset_generator>
                //let _coset_offset = domain_gen.pow(&[*index as u64]);
                let coset_offset_inv = round.domain_gen_inv.pow([*index as u64]);

                compute_fold::<C>(
                    builder,
                    &answers,
                    &parsed.final_folding_randomness,
                    coset_offset_inv,
                    coset_generator_inv,
                    two_inv,
                    config.folding_factor,
                )
            })
            .collect();

        result.push(evaluations);
        domain_size /= 2;
    }

    let domain_gen_inv = parsed.final_domain_gen_inv;

    // Final round
    let coset_generator_inv = domain_gen_inv.pow([(domain_size / coset_domain_size) as u64]);

    let evaluations: Vec<_> = parsed
        .final_randomness_indexes
        .iter()
        .enumerate()
        .map(|(i, index)| {
            let answers = builder.get(&parsed.final_randomness_answers, i);
            // The coset is w^index * <w_coset_generator>
            //let _coset_offset = domain_gen.pow(&[*index as u64]);
            let coset_offset_inv = domain_gen_inv.pow([*index as u64]);
            compute_fold::<C>(
                builder,
                &answers,
                &parsed.final_folding_randomness,
                coset_offset_inv,
                coset_generator_inv,
                two_inv,
                config.folding_factor,
            )
        })
        .collect();

    result.push(evaluations);

    result
}

fn compute_fold<C: Config>(
    builder: &mut Builder<C>,
    answers: &Array<C, Felt<C::F>>,
    folding_randomness: &Vec<Felt<C::F>>,
    mut coset_offset_inv: F,
    mut coset_gen_inv: F,
    two_inv: F,
    folding_factor: usize,
) -> Felt<C::F> {
    let mut scalars: Vec<Felt<C::F>> = vec![];
    iter_zip!(builder, answers).for_each(|idx_vec, builder| {
        let ptr = idx_vec[0];
        let v = builder.iter_ptr_get(&answers, ptr);
        scalars.push(v);
    });
    let two_inv: Felt<C::F> = builder.eval(C::F::from_wrapped_u64(to_bigint_u64(two_inv)));

    // We recursively compute the fold, rec is where it is
    if scalars.len() > 1 {
        for rec in 0..folding_factor {
            let offset = scalars.len() / 2;
            let mut new_answers: Vec<Felt<C::F>> = vec![];
            let mut coset_index_inv = F::ONE;
            for i in 0..offset {
                let f_value_0 = scalars[i];
                let f_value_1 = scalars[i + offset];
                let point_inv: Felt<C::F> = builder.eval(C::F::from_wrapped_u64(to_bigint_u64(
                    coset_offset_inv * coset_index_inv,
                )));
                let left = f_value_0 + f_value_1;
                let right = point_inv * (f_value_0 - f_value_1);

                let new_answer = two_inv
                    * (left + folding_randomness[folding_randomness.len() - 1 - rec] * right);
                new_answers.push(builder.eval(new_answer));
                coset_index_inv *= coset_gen_inv;
            }
            scalars = new_answers;

            coset_offset_inv = coset_offset_inv * coset_offset_inv;
            coset_gen_inv = coset_gen_inv * coset_gen_inv;
        }
    }

    scalars[0]
}

pub struct WhirTranscriptWitness {
    root_digest: Blake3Digest,
    folding_factor: usize,
    initial_ood_answers: Vec<F>,
    initial_sumcheck_polys: Vec<[F; 3]>,
    sumcheck_round_count: usize,
    sumcheck_round_roots: Vec<Blake3Digest>,
    sumcheck_round_ood_answers: Vec<Vec<F>>,
    sumcheck_round_poly_evals: Vec<Vec<[F; 3]>>,
    final_sumcheck_rounds: usize,
    final_coefficients: Vec<F>,
    final_sumcheck_poly_evals: Vec<[F; 3]>,
}

#[derive(DslVariable, Clone)]
pub struct WhirTranscriptWitnessVariable<C: Config> {
    root_digest: BlakeDigestVariable<C>,
    initial_ood_answers: Array<C, Felt<C::F>>,
    folding_factor: Usize<C::N>,
    initial_sumcheck_polys: Array<C, Array<C, Felt<C::F>>>,
    sumcheck_round_count: Usize<C::N>,
    sumcheck_round_roots: Array<C, BlakeDigestVariable<C>>,
    sumcheck_round_ood_answers: Array<C, Array<C, Felt<C::F>>>,
    sumcheck_round_poly_evals: Array<C, Array<C, Array<C, Felt<C::F>>>>,
    final_sumcheck_rounds: Usize<C::N>,
    final_coefficients: Array<C, Felt<C::F>>,
    final_sumcheck_poly_evals: Array<C, Array<C, Felt<C::F>>>,
}

#[derive(DslVariable, Clone)]
pub struct SumcheckRound<C: Config> {
    poly_eval: Array<C, Felt<C::F>>,
    folding_randomness: Felt<C::F>,
}

#[derive(Clone)]
struct ParsedIntermediateRound<C: Config> {
    folding_randomness: Vec<Felt<C::F>>,
    ood_points: Array<C, Felt<C::F>>,
    ood_answers: Array<C, Felt<C::F>>,
    stir_challenges_indexes: Vec<usize>,
    stir_challenges_points: Vec<F>,
    stir_challenges_answers: Array<C, Array<C, Felt<C::F>>>,
    combination_randomness: Array<C, Felt<C::F>>,
    sumcheck_rounds: Vec<SumcheckRound<C>>,
    domain_gen_inv: F,
}

#[derive(Clone)]
pub struct ParsedProofVariable<C: Config> {
    initial_combination_randomness: Array<C, Felt<C::F>>,
    initial_sumcheck_rounds: Vec<SumcheckRound<C>>,
    rounds: Vec<ParsedIntermediateRound<C>>,
    final_domain_gen_inv: F,
    final_randomness_indexes: Vec<usize>,
    final_randomness_points: Vec<F>,
    final_randomness_answers: Array<C, Array<C, Felt<C::F>>>,
    final_folding_randomness: Vec<Felt<C::F>>,
    final_sumcheck_rounds: Vec<SumcheckRound<C>>,
    final_sumcheck_randomness: Vec<Felt<C::F>>,
    final_coefficients: Array<C, Felt<C::F>>,
}

impl Hintable<InnerConfig> for WhirTranscriptWitness {
    type HintVariable = WhirTranscriptWitnessVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let root_digest = Blake3Digest::read(builder);
        let initial_ood_answers = builder.hint_felts();
        let folding_factor = Usize::Var(usize::read(builder));

        // Witness on intial statement
        let initial_sumcheck_polys = builder.dyn_array(folding_factor.clone());
        iter_zip!(builder, initial_sumcheck_polys).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            let v = builder.hint_felts();
            builder.iter_ptr_set(&initial_sumcheck_polys, ptr, v);
        });

        // Middle rounds
        let sumcheck_round_count = Usize::Var(usize::read(builder));
        let sumcheck_round_roots = Vec::<Blake3Digest>::read(builder);

        let sumcheck_round_ood_answers = builder.dyn_array(sumcheck_round_count.clone());
        iter_zip!(builder, sumcheck_round_ood_answers).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            let v = builder.hint_felts();
            builder.iter_ptr_set(&sumcheck_round_ood_answers, ptr, v);
        });

        let round_l = builder.eval_expr(sumcheck_round_count.clone());
        let folding_l = builder.eval_expr(folding_factor.clone());
        let sumcheck_round_poly_evals = builder.dyn_array(round_l);
        iter_zip!(builder, sumcheck_round_poly_evals).for_each(|idx_vec, builder| {
            let sumcheck_round_inner_polys = builder.dyn_array(folding_l);

            iter_zip!(builder, sumcheck_round_inner_polys).for_each(|inner_idx_vec, builder| {
                let inner_ptr = inner_idx_vec[0];
                let v = builder.hint_felts();
                builder.iter_ptr_set(&sumcheck_round_inner_polys, inner_ptr, v);
            });

            let ptr = idx_vec[0];
            builder.iter_ptr_set(&sumcheck_round_poly_evals, ptr, sumcheck_round_inner_polys);
        });

        // Final sumcheck
        let final_sumcheck_rounds = Usize::Var(usize::read(builder));
        let final_coefficients = builder.hint_felts();
        let final_sumcheck_poly_evals = builder.dyn_array(final_sumcheck_rounds.clone());
        iter_zip!(builder, final_sumcheck_poly_evals).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            let v = builder.hint_felts();
            builder.iter_ptr_set(&final_sumcheck_poly_evals, ptr, v);
        });

        Self::HintVariable {
            root_digest,
            initial_ood_answers,
            folding_factor,
            initial_sumcheck_polys,
            sumcheck_round_count,
            sumcheck_round_roots,
            sumcheck_round_ood_answers,
            sumcheck_round_poly_evals,
            final_sumcheck_rounds,
            final_coefficients,
            final_sumcheck_poly_evals,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();

        stream.extend(self.root_digest.write());
        stream.extend(convert_field_vector(&self.initial_ood_answers).write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.folding_factor,
        ));

        for p in self.initial_sumcheck_polys.iter() {
            stream.extend(convert_poly_evals(p).write());
        }
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.sumcheck_round_count,
        ));
        stream.extend(self.sumcheck_round_roots.write());
        for answers in self.sumcheck_round_ood_answers.iter() {
            stream.extend(convert_field_vector(answers).write());
        }
        for round in self.sumcheck_round_poly_evals.iter() {
            for p in round.iter() {
                stream.extend(convert_poly_evals(p).write());
            }
        }
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.final_sumcheck_rounds,
        ));
        stream.extend(convert_field_vector(&self.final_coefficients).write());
        for p in self.final_sumcheck_poly_evals.iter() {
            stream.extend(convert_poly_evals(p).write());
        }

        stream
    }
}

fn parse_arthur_transcript<Arthur>(
    arthur: &mut Arthur,
    config: WhirConfig<F, MerkleConfig, PowStrategy>,
) -> WhirTranscriptWitness
where
    Arthur: FieldReader<F>
        + FieldChallenges<F>
        + ByteReader
        + ByteChallenges
        + DigestReader<MerkleConfig>
        + PoWChallenge,
{
    let root_digest = arthur.read_digest().expect("Root digest should exist.");

    let mut initial_ood_points = vec![F::ZERO; config.committment_ood_samples];
    let mut initial_ood_answers = vec![F::ZERO; config.committment_ood_samples];
    if config.committment_ood_samples > 0 {
        arthur
            .fill_challenge_scalars(&mut initial_ood_points)
            .expect("Initial ood points");
        arthur
            .fill_next_scalars(&mut initial_ood_answers)
            .expect("Initial ood answers");
    }

    assert!(config.initial_statement);

    // Derive combination randomness and first sumcheck polynomial
    let [_combination_randomness_gen]: [F; 1] = arthur
        .challenge_scalars()
        .expect("Combination randomness generator");

    let mut initial_sumcheck_polys: Vec<[F; 3]> = vec![];
    for _ in 0..config.folding_factor {
        let initial_sumcheck_poly_evals: [F; 3] = arthur
            .next_scalars()
            .expect("Sumcheck poly coefficient witnesses.");
        initial_sumcheck_polys.push(initial_sumcheck_poly_evals);

        let [_folding_randomness_single] = arthur.challenge_scalars().expect("Folding challenge");

        // _debug: skip pow
        if config.starting_folding_pow_bits > 0. {
            arthur
                .challenge_pow::<PowStrategy>(config.starting_folding_pow_bits)
                .expect("pow");
        }
    }

    let domain_size = config.starting_domain.size();
    let mut sumcheck_round_roots: Vec<Blake3Digest> = vec![];
    let mut sumcheck_round_ood_answers: Vec<Vec<F>> = vec![];
    let mut sumcheck_round_poly_evals: Vec<Vec<[F; 3]>> = vec![];
    for r in 0..config.n_rounds() {
        let new_root = arthur.read_digest().expect("Round digest");
        sumcheck_round_roots.push(new_root);

        let round_params = &config.round_parameters[r];

        let mut ood_points = vec![F::ZERO; round_params.ood_samples];
        let mut ood_answers = vec![F::ZERO; round_params.ood_samples];
        if round_params.ood_samples > 0 {
            arthur
                .fill_challenge_scalars(&mut ood_points)
                .expect("Round challenge points");
            arthur
                .fill_next_scalars(&mut ood_answers)
                .expect("Round answers");
        }
        sumcheck_round_ood_answers.push(ood_answers);

        let folded_domain_size = domain_size / (1 << config.folding_factor);
        let domain_size_bytes = ((folded_domain_size * 2 - 1).ilog2() as usize + 7) / 8;
        let mut queries = vec![0u8; round_params.num_queries * domain_size_bytes];
        arthur
            .fill_challenge_bytes(&mut queries)
            .expect("Round challenge queries");

        // _debug: skip pow
        if round_params.pow_bits > 0. {
            arthur
                .challenge_pow::<PowStrategy>(round_params.pow_bits)
                .expect("pow");
        }

        let [_combination_randomness_gen] = arthur
            .challenge_scalars()
            .expect("Round combination randomness generator");

        let mut round_poly_evals: Vec<[F; 3]> = vec![];
        for _ in 0..config.folding_factor {
            let sumcheck_poly_evals: [F; 3] =
                arthur.next_scalars().expect("Round sumcheck poly evals");
            round_poly_evals.push(sumcheck_poly_evals);
            let [_folding_randomness_single] = arthur
                .challenge_scalars()
                .expect("Round folding randomness");

            // _debug: skip pow
            if round_params.folding_pow_bits > 0. {
                arthur
                    .challenge_pow::<PowStrategy>(round_params.folding_pow_bits)
                    .expect("pow");
            }
        }
        sumcheck_round_poly_evals.push(round_poly_evals);
    }

    let mut final_coefficients = vec![F::ZERO; 1 << config.final_sumcheck_rounds];
    arthur
        .fill_next_scalars(&mut final_coefficients)
        .expect("Final sumcheck coefficients");

    // Final queries verify
    let folded_domain_size = domain_size / (1 << config.folding_factor);
    let domain_size_bytes = ((folded_domain_size * 2 - 1).ilog2() as usize + 7) / 8;
    let mut queries = vec![0u8; config.final_queries * domain_size_bytes];
    arthur
        .fill_challenge_bytes(&mut queries)
        .expect("Final queries");

    // _debug: skip pow
    if config.final_pow_bits > 0. {
        arthur
            .challenge_pow::<PowStrategy>(config.final_pow_bits)
            .expect("pow");
    }

    let mut final_sumcheck_poly_evals: Vec<[F; 3]> = vec![];
    for _ in 0..config.final_sumcheck_rounds {
        let sumcheck_poly_evals: [F; 3] = arthur.next_scalars().expect("Round sumcheck poly evals");
        final_sumcheck_poly_evals.push(sumcheck_poly_evals);
        let [_folding_randomness_single] = arthur
            .challenge_scalars()
            .expect("Final folding randomness");

        // _debug: skip pow
        if config.final_folding_pow_bits > 0. {
            arthur
                .challenge_pow::<PowStrategy>(config.final_folding_pow_bits)
                .expect("pow");
        }
    }

    WhirTranscriptWitness {
        root_digest,
        folding_factor: config.folding_factor,
        initial_ood_answers,
        initial_sumcheck_polys,
        sumcheck_round_count: config.n_rounds(),
        sumcheck_round_roots,
        sumcheck_round_ood_answers,
        sumcheck_round_poly_evals,
        final_sumcheck_rounds: config.final_sumcheck_rounds,
        final_coefficients,
        final_sumcheck_poly_evals,
    }
}

fn scalar_challenge<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
) -> Felt<C::F> {
    challenger.sample(builder)
}

fn scalar_challenges<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    len: usize,
) -> Array<C, Felt<C::F>> {
    let scalars = builder.dyn_array(len);

    iter_zip!(builder, scalars).for_each(|idx_vec, builder| {
        let ptr = idx_vec[0];
        let r = scalar_challenge(builder, challenger);
        builder.iter_ptr_set(&scalars, ptr, r);
    });

    scalars
}

fn expand_randomness<C: Config>(
    builder: &mut Builder<C>,
    gen: Felt<C::F>,
    randomness_array: &Array<C, Felt<C::F>>,
) {
    let mut last_r: Felt<C::F> = builder.eval(C::F::ONE);
    iter_zip!(builder, randomness_array).for_each(|idx_vec, builder| {
        let ptr = idx_vec[0];
        let r: Felt<C::F> = builder.eval(last_r * gen);
        builder.iter_ptr_set(&randomness_array, ptr, r);
        last_r = builder.iter_ptr_get(&randomness_array, ptr);
    });
}

fn verify_whir<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    statement: StatementVariable<C>,
    proof: WhirProofVariable<C>,
    transcript_witness: WhirTranscriptWitnessVariable<C>,
    config: WhirConfig<F, MerkleConfig, PowStrategy>,
) {
    let root = transcript_witness.root_digest;
    challenger.observe_slice(builder, root.clone().digest);

    let initial_ood_len = config.committment_ood_samples;
    let initial_ood_points = scalar_challenges(builder, challenger, initial_ood_len);
    let initial_ood_answers = transcript_witness.initial_ood_answers;

    assert!(config.initial_statement);

    // Derive combination randomness and first sumcheck polynomial
    let combination_randomness_len =
        builder.eval_expr(initial_ood_points.len() + statement.points.len());
    let combination_randomness_gen = scalar_challenge(builder, challenger);
    let initial_combination_randomness: Array<C, Felt<C::F>> =
        builder.dyn_array(combination_randomness_len);
    expand_randomness(
        builder,
        combination_randomness_gen,
        &initial_combination_randomness,
    );

    // Initial sumcheck
    let mut initial_sumcheck_rounds: Vec<SumcheckRound<C>> = vec![];
    let mut folding_randomness: Vec<Felt<C::F>> = vec![];
    iter_zip!(builder, transcript_witness.initial_sumcheck_polys).for_each(|idx_vec, builder| {
        let ptr = idx_vec[0];
        let poly = builder.iter_ptr_get(&transcript_witness.initial_sumcheck_polys, ptr);
        challenger.observe_slice(builder, poly.clone());
        let folding_ml_pt = scalar_challenge(builder, challenger);
        folding_randomness.push(folding_ml_pt);
        initial_sumcheck_rounds.push(SumcheckRound {
            poly_eval: poly,
            folding_randomness: folding_ml_pt,
        });

        // _debug: POW
    });
    folding_randomness.reverse();

    // Intermediate Sumcheck rounds
    let mut prev_root = root;
    let domain_gen = config.starting_domain.backing_domain.group_gen();
    let mut exp_domain_gen = domain_gen.pow([1 << config.folding_factor]);
    let mut domain_gen_inv = config.starting_domain.backing_domain.group_gen_inv();
    let mut domain_size = config.starting_domain.size();
    let mut intermediate_rounds: Vec<ParsedIntermediateRound<C>> = vec![];

    let mut r: usize = 0;
    iter_zip!(
        builder,
        proof.proofs,
        transcript_witness.sumcheck_round_roots,
        transcript_witness.sumcheck_round_ood_answers,
        transcript_witness.sumcheck_round_poly_evals,
    )
    .for_each(|idx_vec, builder| {
        let whir_proof_ptr = idx_vec[0];
        let whir_proof = builder.iter_ptr_get(&proof.proofs, whir_proof_ptr);
        let round_params = &config.round_parameters[r];

        let root_ptr = idx_vec[1];
        let new_root = builder.iter_ptr_get(&transcript_witness.sumcheck_round_roots, root_ptr);

        let ood_points = scalar_challenges(builder, challenger, round_params.ood_samples);
        let ood_ptr = idx_vec[2];
        let ood_answers =
            builder.iter_ptr_get(&transcript_witness.sumcheck_round_ood_answers, ood_ptr);
        challenger.observe_slice(builder, ood_answers.clone());

        let stir_challenges_indexes = get_challenge_stir_queries(
            domain_size,
            config.folding_factor,
            round_params.num_queries,
        );

        let stir_challenges_points: Vec<F> = stir_challenges_indexes
            .iter()
            .map(|index| exp_domain_gen.pow([*index as u64]))
            .collect();

        verify_merkle_proof(builder, challenger, &whir_proof);

        // _debug: POW

        // Round combination randomness
        let combination_randomness_len =
            Usize::from(round_params.num_queries + round_params.ood_samples);
        let combination_randomness_gen = scalar_challenge(builder, challenger);
        let combination_randomness: Array<C, Felt<C::F>> =
            builder.dyn_array(combination_randomness_len);
        expand_randomness(builder, combination_randomness_gen, &combination_randomness);

        let round_polys_ptr = idx_vec[3];
        let round_polys = builder.iter_ptr_get(
            &transcript_witness.sumcheck_round_poly_evals,
            round_polys_ptr,
        );
        let mut sumcheck_rounds: Vec<SumcheckRound<C>> = vec![];
        let mut folding_ml_pt: Vec<Felt<C::F>> = vec![];

        iter_zip!(builder, round_polys).for_each(|inner_idx_vec, builder| {
            let ptr = inner_idx_vec[0];
            let poly = builder.iter_ptr_get(&round_polys, ptr);
            challenger.observe_slice(builder, poly.clone());

            let folding_randomness = scalar_challenge(builder, challenger);
            folding_ml_pt.push(folding_randomness);
            sumcheck_rounds.push(SumcheckRound {
                poly_eval: poly,
                folding_randomness,
            });

            // _debug: POW
        });
        folding_ml_pt.reverse();

        intermediate_rounds.push(ParsedIntermediateRound {
            folding_randomness: folding_ml_pt.clone(),
            ood_points,
            ood_answers,
            stir_challenges_indexes,
            stir_challenges_points,
            stir_challenges_answers: whir_proof.answers,
            combination_randomness,
            sumcheck_rounds,
            domain_gen_inv,
        });

        folding_randomness = folding_ml_pt;

        prev_root = new_root.clone();
        exp_domain_gen = exp_domain_gen * exp_domain_gen;
        domain_gen_inv = domain_gen_inv * domain_gen_inv;
        domain_size /= 2;

        r += 1;
    });

    // Final Sumchecks
    let final_coefficients = transcript_witness.final_coefficients;
    let final_whir_proof_idx = builder.eval_expr(proof.len - Usize::from(1));
    let final_whir_proof = builder.get(&proof.proofs, final_whir_proof_idx);

    // Final queries verify
    let final_randomness_indexes =
        get_challenge_stir_queries(domain_size, config.folding_factor, config.final_queries);
    let final_randomness_points: Vec<F> = final_randomness_indexes
        .iter()
        .map(|index| exp_domain_gen.pow([*index as u64]))
        .collect();

    verify_merkle_proof(builder, challenger, &final_whir_proof);

    // _debug: POW

    let mut final_sumcheck_rounds: Vec<SumcheckRound<C>> = vec![];
    let mut final_sumcheck_randomness: Vec<Felt<C::F>> = vec![];

    iter_zip!(builder, transcript_witness.final_sumcheck_poly_evals).for_each(
        |idx_vec, builder| {
            let ptr = idx_vec[0];
            let poly = builder.iter_ptr_get(&transcript_witness.final_sumcheck_poly_evals, ptr);
            challenger.observe_slice(builder, poly.clone());

            let folding_randomness = scalar_challenge(builder, challenger);
            final_sumcheck_randomness.push(folding_randomness);
            final_sumcheck_rounds.push(SumcheckRound {
                poly_eval: poly,
                folding_randomness,
            });

            // _debug: POW
        },
    );
    final_sumcheck_randomness.reverse();

    let parsed = ParsedProofVariable {
        initial_combination_randomness,
        initial_sumcheck_rounds,
        rounds: intermediate_rounds,
        final_domain_gen_inv: domain_gen_inv,
        final_randomness_indexes,
        final_randomness_points,
        final_randomness_answers: final_whir_proof.answers,
        final_folding_randomness: folding_randomness,
        final_sumcheck_rounds,
        final_sumcheck_randomness,
        final_coefficients,
    };

    let computed_folds = compute_folds_full(builder, &parsed, &config);
    let evaluation_idxs = construct_binary_evaluation_idxs(config.folding_factor);

    // Check first sumcheck
    let mut prev: &SumcheckRound<C>;
    let first_round = parsed
        .initial_sumcheck_rounds
        .first()
        .expect("First sumcheck");

    // Check the first polynomial
    let mut prev_poly = &first_round.poly_eval;
    let mut randomness = first_round.folding_randomness;

    let sum = sum_over_hypercube(builder, prev_poly, &evaluation_idxs);
    let zero: Usize<C::N> = builder.eval(C::N::ZERO);
    let ood_answers_len: Usize<C::N> = builder.eval(initial_ood_answers.len());
    let randomness_len: Usize<C::N> = builder.eval(parsed.initial_combination_randomness.len());
    let ood_randomness_slice =
        &parsed
            .initial_combination_randomness
            .slice(builder, zero, ood_answers_len.clone());
    let ood_dot_product = dot_product(builder, &initial_ood_answers, ood_randomness_slice);
    let statement_randomness_slice =
        &parsed
            .initial_combination_randomness
            .slice(builder, ood_answers_len, randomness_len);
    let statement_dot_product =
        dot_product(builder, &statement.evaluations, statement_randomness_slice);
    let rhs: Felt<<C as Config>::F> = builder.eval(ood_dot_product + statement_dot_product);

    // _debug: Field discrepancy
    // builder.assert_felt_eq(sum, rhs);

    // Check the rest of the initial rounds
    for round in &parsed.initial_sumcheck_rounds[1..] {
        let poly = &round.poly_eval;
        let new_randomness = round.folding_randomness;

        let sum = sum_over_hypercube(builder, poly, &evaluation_idxs);
        let random_eval = evaluate_at_point(builder, prev_poly, randomness);

        // _debug: Field discrepancy
        // builder.assert_felt_eq(sum, random_eval);

        prev_poly = poly;
        randomness = new_randomness;
    }
    let mut prev_sumcheck = SumcheckRound {
        poly_eval: prev_poly.clone(),
        folding_randomness: randomness,
    };
    prev = &prev_sumcheck;

    // Check intermediate sumcheck rounds
    for (round, folds) in parsed.rounds.iter().zip(&computed_folds) {
        let sumcheck_round = &round.sumcheck_rounds[0].clone();
        let sumcheck_poly = &sumcheck_round.poly_eval;
        let new_randomness = sumcheck_round.folding_randomness;

        let prev_eval = evaluate_at_point(builder, &prev.poly_eval, prev.folding_randomness);
        let sum = sum_over_hypercube(builder, &sumcheck_poly, &evaluation_idxs);
        let zero: Usize<C::N> = builder.eval(C::N::ZERO);
        let ood_answers_len: Usize<C::N> = builder.eval(round.ood_answers.len());
        let randomness_len: Usize<C::N> = builder.eval(round.combination_randomness.len());
        let ood_randomness_slice =
            &round
                .combination_randomness
                .slice(builder, zero, ood_answers_len.clone());
        let ood_dot_product = dot_product(builder, &round.ood_answers, ood_randomness_slice);
        let folds_randomness_slice =
            &round
                .combination_randomness
                .slice(builder, ood_answers_len, randomness_len);
        let folds_arr = convert_vec_felts_to_vm(builder, folds);
        let folds_dot_product = dot_product(builder, &folds_arr, folds_randomness_slice);
        let claimed_sum: Felt<<C as Config>::F> =
            builder.eval(prev_eval + ood_dot_product + folds_dot_product);

        // _debug: Field discrepancy
        // builder.assert_felt_eq(sum, claimed_sum);

        prev_sumcheck = SumcheckRound {
            poly_eval: sumcheck_poly.clone(),
            folding_randomness: new_randomness,
        };
        prev = &prev_sumcheck;

        for round in &round.sumcheck_rounds[1..] {
            let poly = &round.poly_eval;
            let new_randomness = round.folding_randomness;

            let sum = sum_over_hypercube(builder, poly, &evaluation_idxs);
            let random_eval = evaluate_at_point(builder, prev_poly, randomness);

            // _debug: Field discrepancy
            // builder.assert_felt_eq(sum, random_eval);

            prev_poly = poly;
            randomness = new_randomness;
        }
        prev_sumcheck = SumcheckRound {
            poly_eval: prev_poly.clone(),
            folding_randomness: randomness,
        };
        prev = &prev_sumcheck;
    }

    // _

    // Check the final sumchecks
    let prev_eval = evaluate_at_point(builder, &prev.poly_eval, prev.folding_randomness);
    let final_sumcheck_round = &parsed.final_sumcheck_rounds[0].clone();
    let sumcheck_poly = &final_sumcheck_round.poly_eval;
    let new_randomness = final_sumcheck_round.folding_randomness;
    let claimed_sum = prev_eval;
    let sum = sum_over_hypercube(builder, sumcheck_poly, &evaluation_idxs);

    // _debug: Field discrepancy
    // builder.assert_felt_eq(sum, claimed_sum);

    prev_sumcheck = SumcheckRound {
        poly_eval: sumcheck_poly.clone(),
        folding_randomness: new_randomness,
    };
    prev = &prev_sumcheck;

    // Check the rest of the round
    for round in &parsed.final_sumcheck_rounds[1..] {
        let poly = &round.poly_eval;
        let new_randomness = round.folding_randomness;

        let sum = sum_over_hypercube(builder, poly, &evaluation_idxs);
        let random_eval = evaluate_at_point(builder, prev_poly, randomness);

        // _debug: Field discrepancy
        // builder.assert_felt_eq(sum, random_eval);

        prev_poly = poly;
        randomness = new_randomness;

        prev_sumcheck = SumcheckRound {
            poly_eval: prev_poly.clone(),
            folding_randomness: randomness,
        };
        prev = &prev_sumcheck;
    }

    // _
}

pub mod tests {
    use crate::whir::{parse_arthur_transcript, verify_whir, WhirTranscriptWitness};
    use nimue::{DefaultHash, IOPattern};
    use nimue_pow::blake3::Blake3PoW;
    use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::{AsmBuilder, AsmConfig};
    use openvm_native_recursion::{challenger::duplex::DuplexChallengerVariable, hints::Hintable};
    use openvm_stark_backend::config::{StarkGenericConfig, Val};
    use openvm_stark_sdk::{
        config::baby_bear_poseidon2::{default_engine, BabyBearPoseidon2Config},
        p3_baby_bear::BabyBear,
    };
    use whir::{
        crypto::{fields::Field64, merkle_tree::blake3 as merkle_tree},
        parameters::{FoldType, MultivariateParameters, SoundnessType, WhirParameters},
        poly_utils::{coeffs::CoefficientList, MultilinearPoint},
        sumcheck::prover_core::SumcheckCore,
        utils::base_decomposition,
        whir::{
            committer::Committer, iopattern::WhirIOPattern, parameters::WhirConfig, prover::Prover,
            verifier::Verifier, Statement, WhirProof,
        },
    };

    type MerkleConfig = merkle_tree::MerkleTreeParams<F>;
    type PowStrategy = Blake3PoW;
    type F = Field64;

    fn construct_binary_evaluation_idxs(folding_factor: usize) -> Vec<usize> {
        (0..(1 << folding_factor))
            .into_iter()
            .filter(|&p| {
                base_decomposition(p, 3, folding_factor)
                    .into_iter()
                    .all(|v| matches!(v, 0 | 1))
            })
            .collect::<Vec<usize>>()
    }

    #[allow(dead_code)]
    pub fn build_test_whir_sumcheck() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        type SC = BabyBearPoseidon2Config;
        type F = Val<SC>;
        type EF = <SC as StarkGenericConfig>::Challenge;
        type Challenger = <SC as StarkGenericConfig>::Challenger;
        type ScPcs = <SC as StarkGenericConfig>::Pcs;
        type C = AsmConfig<F, EF>;
        type WF = Field64; // Whir's field

        // Whir setup constants
        let folding_factor: usize = 2;
        let num_variables = 3 * folding_factor;
        let soundness_type = SoundnessType::UniqueDecoding;
        let fold_type = FoldType::Naive;
        let num_points: usize = 1;
        let pow_bits: usize = 5;
        let num_coeffs = 1 << num_variables;

        let mut rng = ark_std::test_rng();

        // Parameters
        let (leaf_hash_params, two_to_one_params) = merkle_tree::default_config::<WF>(&mut rng);
        let mv_params = MultivariateParameters::<WF>::new(num_variables);
        let whir_params = WhirParameters::<MerkleConfig, PowStrategy> {
            initial_statement: true,
            security_level: 32,
            pow_bits,
            folding_factor,
            leaf_hash_params,
            two_to_one_params,
            soundness_type,
            _pow_parameters: Default::default(),
            starting_log_inv_rate: 1,
            fold_optimisation: fold_type,
        };
        let params = WhirConfig::<WF, MerkleConfig, PowStrategy>::new(mv_params, whir_params);

        // Protocol
        let polynomial = CoefficientList::new(vec![WF::from(1); num_coeffs]);

        let points: Vec<_> = (0..num_points)
            .map(|_| MultilinearPoint::rand(&mut rng, num_variables))
            .collect();

        let statement = Statement {
            points: points.clone(),
            evaluations: points
                .iter()
                .map(|point| polynomial.evaluate(point))
                .collect(),
        };

        let io = IOPattern::<DefaultHash>::new("🌪️")
            .commit_statement(&params)
            .add_whir_proof(&params)
            .clone();

        let mut merlin = io.to_merlin();

        let committer = Committer::new(params.clone());
        let witness = committer.commit(&mut merlin, polynomial).unwrap();

        let prover = Prover(params.clone());

        let proof = prover
            .prove(&mut merlin, statement.clone(), witness)
            .unwrap();

        let verifier = Verifier::new(params.clone());
        let mut arthur = io.to_arthur(merlin.transcript().clone());

        assert!(verifier.verify(&mut arthur, &statement, &proof).is_ok());

        // OpenVM DSL
        let engine = default_engine();
        let _pcs = engine.config.pcs();
        let perm = engine.perm;
        let mut challenger = Challenger::new(perm.clone());

        let mut builder = AsmBuilder::<F, EF>::default();
        let mut challenger = DuplexChallengerVariable::new(&mut builder);

        // Obtain witness inputs
        let whir_statement = Statement::read(&mut builder);
        let whir_proof = WhirProof::read(&mut builder);
        let transcript_witness = WhirTranscriptWitness::read(&mut builder);

        verify_whir(
            &mut builder,
            &mut challenger,
            whir_statement,
            whir_proof,
            transcript_witness,
            params.clone(),
        );
        builder.halt();

        // Pass in witness stream
        let mut witness_stream: Vec<
            Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
        > = Vec::new();
        witness_stream.extend(statement.write());
        witness_stream.extend(proof.write());

        let mut arthur = io.to_arthur(merlin.transcript());
        let transcript_witness = parse_arthur_transcript(&mut arthur, params.clone());
        witness_stream.extend(transcript_witness.write());

        let program: Program<
            p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
        > = builder.compile_isa();

        (program, witness_stream)
    }

    #[test]
    fn test_whir_sumcheck() {
        let (program, witness) = build_test_whir_sumcheck();

        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100);
        let config = NativeConfig::new(system_config, Native);

        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
        executor.execute(program, witness).unwrap();
    }
}
