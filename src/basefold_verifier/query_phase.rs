// Note: check all XXX comments!

use ark_std::log2;
use ff_ext::{BabyBearExt4, ExtensionField, PoseidonField};
use mpcs::basefold::QueryOpeningProof as InnerQueryOpeningProof;
use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::{
    hints::{Hintable, VecAutoHintable},
    vars::HintSlice,
};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_commit::ExtensionMmcs;
use p3_field::{Field, FieldAlgebra};
use serde::Deserialize;
use std::fmt::Debug;

use super::{basefold::*, extension_mmcs::*, mmcs::*, rs::*, structs::*, utils::*};
use crate::{
    arithmetics::{build_eq_x_r_vec_sequential_with_offset, eq_eval_with_index},
    tower_verifier::{binding::*, program::interpolate_uni_poly},
};

pub type F = BabyBear;
pub type E = BabyBearExt4;
pub type InnerConfig = AsmConfig<F, E>;

use p3_fri::BatchOpening as InnerBatchOpening;
use p3_fri::CommitPhaseProofStep as InnerCommitPhaseProofStep;

/// We have to define a struct similar to p3_fri::BatchOpening as
/// the trait `Hintable` is defined in another crate inside OpenVM
#[derive(Deserialize)]
pub struct BatchOpening {
    pub opened_values: Vec<Vec<F>>,
    pub opening_proof: MmcsProof,
}

impl
    From<
        InnerBatchOpening<
            <E as ExtensionField>::BaseField,
            <<E as ExtensionField>::BaseField as PoseidonField>::MMCS,
        >,
    > for BatchOpening
{
    fn from(
        inner: InnerBatchOpening<
            <E as ExtensionField>::BaseField,
            <<E as ExtensionField>::BaseField as PoseidonField>::MMCS,
        >,
    ) -> Self {
        Self {
            opened_values: inner.opened_values,
            opening_proof: inner.opening_proof.into(),
        }
    }
}

#[derive(DslVariable, Clone)]
pub struct BatchOpeningVariable<C: Config> {
    pub opened_values: Array<C, Array<C, Felt<C::F>>>,
    pub opening_proof: HintSlice<C>,
}

impl Hintable<InnerConfig> for BatchOpening {
    type HintVariable = BatchOpeningVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let opened_values = Vec::<Vec<F>>::read(builder);
        let opening_proof = read_hint_slice(builder);

        BatchOpeningVariable {
            opened_values,
            opening_proof,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.opened_values.write());
        stream.extend(vec![
            vec![F::from_canonical_usize(self.opening_proof.len())],
            self.opening_proof
                .iter()
                .flatten()
                .copied()
                .collect::<Vec<_>>(),
        ]);
        stream
    }
}

impl VecAutoHintable for BatchOpening {}

/// TODO: use `openvm_native_recursion::fri::types::FriCommitPhaseProofStepVariable` instead
#[derive(Deserialize)]
pub struct CommitPhaseProofStep {
    pub sibling_value: E,
    pub opening_proof: MmcsProof,
}

pub type ExtMmcs<E> = ExtensionMmcs<
    <E as ExtensionField>::BaseField,
    E,
    <<E as ExtensionField>::BaseField as PoseidonField>::MMCS,
>;
impl From<InnerCommitPhaseProofStep<E, ExtMmcs<E>>> for CommitPhaseProofStep {
    fn from(inner: InnerCommitPhaseProofStep<E, ExtMmcs<E>>) -> Self {
        Self {
            sibling_value: inner.sibling_value,
            opening_proof: inner.opening_proof.into(),
        }
    }
}

#[derive(DslVariable, Clone)]
pub struct CommitPhaseProofStepVariable<C: Config> {
    pub sibling_value: Ext<C::F, C::EF>,
    pub opening_proof: HintSlice<C>,
}

impl VecAutoHintable for CommitPhaseProofStep {}

impl Hintable<InnerConfig> for CommitPhaseProofStep {
    type HintVariable = CommitPhaseProofStepVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let sibling_value = E::read(builder);
        let opening_proof = read_hint_slice(builder);

        CommitPhaseProofStepVariable {
            sibling_value,
            opening_proof,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.sibling_value.write());
        stream.extend(vec![
            vec![F::from_canonical_usize(self.opening_proof.len())],
            self.opening_proof
                .iter()
                .flatten()
                .copied()
                .collect::<Vec<_>>(),
        ]);
        stream
    }
}

#[derive(Deserialize)]
pub struct QueryOpeningProof {
    pub input_proofs: Vec<BatchOpening>,
    pub commit_phase_openings: Vec<CommitPhaseProofStep>,
}

impl From<InnerQueryOpeningProof<E>> for QueryOpeningProof {
    fn from(proof: InnerQueryOpeningProof<E>) -> Self {
        Self {
            input_proofs: proof
                .input_proofs
                .into_iter()
                .map(|proof| proof.into())
                .collect(),
            commit_phase_openings: proof
                .commit_phase_openings
                .into_iter()
                .map(|proof| proof.into())
                .collect(),
        }
    }
}

#[derive(DslVariable, Clone)]
pub struct QueryOpeningProofVariable<C: Config> {
    pub input_proofs: Array<C, BatchOpeningVariable<C>>,
    pub commit_phase_openings: Array<C, CommitPhaseProofStepVariable<C>>,
}

pub(crate) type QueryOpeningProofs = Vec<QueryOpeningProof>;
pub(crate) type QueryOpeningProofsVariable<C> = Array<C, QueryOpeningProofVariable<C>>;

impl VecAutoHintable for QueryOpeningProof {}

impl Hintable<InnerConfig> for QueryOpeningProof {
    type HintVariable = QueryOpeningProofVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let input_proofs = Vec::<BatchOpening>::read(builder);
        let commit_phase_openings = Vec::<CommitPhaseProofStep>::read(builder);
        QueryOpeningProofVariable {
            input_proofs,
            commit_phase_openings,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.input_proofs.write());
        stream.extend(self.commit_phase_openings.write());
        stream
    }
}

#[derive(Deserialize)]
// NOTE: Different from PointAndEval in tower_verifier!
pub struct PointAndEvals {
    pub point: Point,
    pub evals: Vec<E>,
}
impl Hintable<InnerConfig> for PointAndEvals {
    type HintVariable = PointAndEvalsVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let point = Point::read(builder);
        let evals = Vec::<E>::read(builder);
        PointAndEvalsVariable { point, evals }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.point.write());
        stream.extend(self.evals.write());
        stream
    }
}
impl VecAutoHintable for PointAndEvals {}

#[derive(DslVariable, Clone)]
pub struct PointAndEvalsVariable<C: Config> {
    pub point: PointVariable<C>,
    pub evals: Array<C, Ext<C::F, C::EF>>,
}

#[derive(Deserialize)]
pub struct QueryPhaseVerifierInput {
    // pub t_inv_halves: Vec<Vec<<E as ExtensionField>::BaseField>>,
    pub max_num_var: usize,
    pub batch_coeffs: Vec<E>,
    pub fold_challenges: Vec<E>,
    pub indices: Vec<usize>,
    pub proof: BasefoldProof,
    pub rounds: Vec<Round>,
}

impl Hintable<InnerConfig> for QueryPhaseVerifierInput {
    type HintVariable = QueryPhaseVerifierInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        // let t_inv_halves = Vec::<Vec<F>>::read(builder);
        let max_num_var = Usize::Var(usize::read(builder));
        let batch_coeffs = Vec::<E>::read(builder);
        let fold_challenges = Vec::<E>::read(builder);
        let indices = Vec::<usize>::read(builder);
        let proof = BasefoldProof::read(builder);
        let rounds = Vec::<Round>::read(builder);

        QueryPhaseVerifierInputVariable {
            // t_inv_halves,
            max_num_var,
            batch_coeffs,
            fold_challenges,
            indices,
            proof,
            rounds,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        // stream.extend(self.t_inv_halves.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.max_num_var));
        stream.extend(self.batch_coeffs.write());
        stream.extend(self.fold_challenges.write());
        stream.extend(self.indices.write());
        stream.extend(self.proof.write());
        stream.extend(self.rounds.write());
        stream
    }
}

#[derive(DslVariable, Clone)]
pub struct QueryPhaseVerifierInputVariable<C: Config> {
    // pub t_inv_halves: Array<C, Array<C, Felt<C::F>>>,
    pub max_num_var: Usize<C::N>,
    pub batch_coeffs: Array<C, Ext<C::F, C::EF>>,
    pub fold_challenges: Array<C, Ext<C::F, C::EF>>,
    pub indices: Array<C, Var<C::N>>,
    pub proof: BasefoldProofVariable<C>,
    pub rounds: Array<C, RoundVariable<C>>,
}

#[derive(DslVariable, Clone)]
pub struct PackedCodeword<C: Config> {
    pub low: Ext<C::F, C::EF>,
    pub high: Ext<C::F, C::EF>,
}

pub(crate) fn batch_verifier_query_phase<C: Config + Debug>(
    builder: &mut Builder<C>,
    input: QueryPhaseVerifierInputVariable<C>,
) {
    // Nondeterministically supply inv_2
    let inv_2 = builder.hint_felt();
    builder.assert_eq::<Felt<C::F>>(
        inv_2 * C::F::from_canonical_usize(2),
        C::F::from_canonical_usize(1),
    );
    let two_adic_generators_inverses: Array<C, Felt<C::F>> = builder.dyn_array(28);
    for (index, val) in [
        0x1usize, 0x78000000, 0x67055c21, 0x5ee99486, 0xbb4c4e4, 0x2d4cc4da, 0x669d6090,
        0x17b56c64, 0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226, 0x4c734715, 0x11c33e2a,
        0x62c3d2b1, 0x77cad399, 0x54c131f4, 0x4cabd6a6, 0x5cf5713f, 0x3e9430e8, 0xba067a3,
        0x18adc27d, 0x21fd55bc, 0x4b859b3d, 0x3bd57996, 0x4483d85a, 0x3a26eef8, 0x1a427a41,
    ]
    .iter()
    .enumerate()
    {
        let generator = builder.constant(C::F::from_canonical_usize(*val).inverse());
        builder.set_value(&two_adic_generators_inverses, index, generator);
    }

    // encode_small
    let final_message = &input.proof.final_message;
    let final_rmm_values_len = builder.get(final_message, 0).len();
    let final_rmm_values = builder.dyn_array(final_rmm_values_len.clone());

    builder
        .range(0, final_rmm_values_len.clone())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let row_len = final_message.len();
            let sum = builder.constant(C::EF::ZERO);
            builder.range(0, row_len).for_each(|j_vec, builder| {
                let j = j_vec[0];
                let row = builder.get(final_message, j);
                let row_j = builder.get(&row, i);
                builder.assign(&sum, sum + row_j);
            });
            builder.set_value(&final_rmm_values, i, sum);
        });

    let final_rmm = RowMajorMatrixVariable {
        values: final_rmm_values,
        width: builder.eval(Usize::from(1)),
    };
    let final_codeword = encode_small(builder, final_rmm);

    let log2_max_codeword_size: Var<C::N> =
        builder.eval(input.max_num_var.clone() + get_rate_log::<C>());

    iter_zip!(builder, input.indices, input.proof.query_opening_proof).for_each(
        |ptr_vec, builder| {
            // TODO: change type of input.indices to be `Array<C, Array<C, Var<C::N>>>`
            let idx = builder.iter_ptr_get(&input.indices, ptr_vec[0]);
            let idx = builder.unsafe_cast_var_to_felt(idx);
            let idx_bits = builder.num2bits_f(idx, C::N::bits() as u32);
            // assert idx_bits[log2_max_codeword_size..] == 0
            builder
                .range(log2_max_codeword_size, idx_bits.len())
                .for_each(|i_vec, builder| {
                    let bit = builder.get(&idx_bits, i_vec[0]);
                    builder.assert_eq::<Var<_>>(bit, Usize::from(0));
                });
            let idx_bits = idx_bits.slice(builder, 1, log2_max_codeword_size.clone());

            let reduced_codeword_by_height: Array<C, PackedCodeword<C>> =
                builder.dyn_array(log2_max_codeword_size.clone());

            let query = builder.iter_ptr_get(&input.proof.query_opening_proof, ptr_vec[1]);
            let batch_coeffs_offset: Var<C::N> = builder.constant(C::N::ZERO);

            iter_zip!(builder, query.input_proofs, input.rounds).for_each(|ptr_vec, builder| {
                let batch_opening = builder.iter_ptr_get(&query.input_proofs, ptr_vec[0]);
                let round = builder.iter_ptr_get(&input.rounds, ptr_vec[1]);
                let opened_values = batch_opening.opened_values;
                let perm_opened_values = builder.dyn_array(opened_values.len());
                let dimensions = builder.dyn_array(opened_values.len());
                let opening_proof = batch_opening.opening_proof;

                // reorder (opened values, dimension) according to the permutation
                builder
                    .range(0, opened_values.len())
                    .for_each(|j_vec, builder| {
                        let j = j_vec[0];
                        let mat_j = builder.get(&opened_values, j);
                        let num_var_j = builder.get(&round.openings, j).num_var;
                        let height_j =
                            builder.eval(num_var_j + get_rate_log::<C>() - Usize::from(1));

                        // TODO: use permutation to get the index
                        // let permuted_index = builder.get(&perm, j);
                        let permuted_j = j;

                        builder.set_value(&perm_opened_values, permuted_j, mat_j);
                        builder.set_value(&dimensions, permuted_j, height_j);
                    });

                // i >>= (log2_max_codeword_size - commit.log2_max_codeword_size);
                let bits_shift: Var<C::N> = builder
                    .eval(log2_max_codeword_size.clone() - round.commit.log2_max_codeword_size);
                let reduced_idx_bits = idx_bits.slice(builder, bits_shift, idx_bits.len());

                // verify input mmcs
                let mmcs_verifier_input = MmcsVerifierInputVariable {
                    commit: round.commit.commit.clone(),
                    dimensions: dimensions,
                    index_bits: reduced_idx_bits,
                    opened_values: perm_opened_values,
                    proof: opening_proof,
                };

                mmcs_verify_batch(builder, mmcs_verifier_input);

                // TODO: optimize this procedure
                iter_zip!(builder, opened_values, round.openings).for_each(|ptr_vec, builder| {
                    let opened_value = builder.iter_ptr_get(&opened_values, ptr_vec[0]);
                    let opening = builder.iter_ptr_get(&round.openings, ptr_vec[1]);
                    let log2_height: Var<C::N> =
                        builder.eval(opening.num_var + get_rate_log::<C>() - Usize::from(1));
                    let width = opening.point_and_evals.evals.len();

                    let batch_coeffs_next_offset: Var<C::N> =
                        builder.eval(batch_coeffs_offset + width.clone());
                    let coeffs = input.batch_coeffs.slice(
                        builder,
                        batch_coeffs_offset.clone(),
                        batch_coeffs_next_offset.clone(),
                    );
                    let low_values = opened_value.slice(builder, 0, width.clone());
                    let high_values =
                        opened_value.slice(builder, width.clone(), opened_value.len());
                    let low: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
                    let high: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

                    iter_zip!(builder, coeffs, low_values, high_values).for_each(
                        |ptr_vec, builder| {
                            let coeff = builder.iter_ptr_get(&coeffs, ptr_vec[0]);
                            let low_value = builder.iter_ptr_get(&low_values, ptr_vec[1]);
                            let high_value = builder.iter_ptr_get(&high_values, ptr_vec[2]);

                            builder.assign(&low, low + coeff * low_value);
                            builder.assign(&high, high + coeff * high_value);
                        },
                    );
                    let codeword = PackedCodeword { low, high };
                    builder.set_value(&reduced_codeword_by_height, log2_height, codeword);
                    builder.assign(&batch_coeffs_offset, batch_coeffs_next_offset);
                });
            });

            let opening_ext = query.commit_phase_openings;

            // fold 1st codeword
            let cur_num_var: Var<C::N> = builder.eval(input.max_num_var.clone());
            let log2_height: Var<C::N> =
                builder.eval(cur_num_var + get_rate_log::<C>() - Usize::from(1));

            let r = builder.get(&input.fold_challenges, 0);
            let codeword = builder.get(&reduced_codeword_by_height, log2_height);
            let coeff = verifier_folding_coeffs_level(
                builder,
                &two_adic_generators_inverses,
                log2_height,
                &idx_bits,
                inv_2,
            );
            let folded = codeword_fold_with_challenge::<C>(
                builder,
                codeword.low,
                codeword.high,
                r,
                coeff,
                inv_2,
            );

            // check commit phases
            let commits = &input.proof.commits;
            builder.assert_eq::<Var<C::N>>(
                commits.len() + Usize::from(1),
                input.fold_challenges.len(),
            );
            builder.assert_eq::<Var<C::N>>(commits.len(), opening_ext.len());
            builder.range(0, commits.len()).for_each(|i_vec, builder| {
                let i = i_vec[0];
                let commit = builder.get(&commits, i);
                let commit_phase_step = builder.get(&opening_ext, i);
                let i_plus_one = builder.eval_expr(i + Usize::from(1));

                let sibling_value = commit_phase_step.sibling_value;
                let proof = commit_phase_step.opening_proof;

                builder.assign(&cur_num_var, cur_num_var - Usize::from(1));
                builder.assign(&log2_height, log2_height - Usize::from(1));

                let folded_idx = builder.get(&idx_bits, i);
                // TODO: absorb smaller codeword
                let new_involved_codeword: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

                // leafs
                let leafs = builder.dyn_array(2);
                let sibling_idx = builder.eval_expr(RVar::from(1) - folded_idx);
                builder.assign(&folded, folded + new_involved_codeword);
                builder.set_value(&leafs, folded_idx, folded);
                builder.set_value(&leafs, sibling_idx, sibling_value);

                // idx >>= 1
                let idx_pair = idx_bits.slice(builder, i_plus_one, idx_bits.len());

                // mmcs_ext.verify_batch
                let dimensions = builder.dyn_array(1);
                let opened_values = builder.dyn_array(1);
                builder.set_value(&opened_values, 0, leafs.clone());
                builder.set_value(&dimensions, 0, log2_height.clone());
                let ext_mmcs_verifier_input = ExtMmcsVerifierInputVariable {
                    commit: commit.clone(),
                    dimensions,
                    index_bits: idx_pair.clone(),
                    opened_values,
                    proof,
                };
                ext_mmcs_verify_batch::<C>(builder, ext_mmcs_verifier_input);

                let r = builder.get(&input.fold_challenges, i_plus_one);
                let coeff = verifier_folding_coeffs_level(
                    builder,
                    &two_adic_generators_inverses,
                    log2_height,
                    &idx_pair,
                    inv_2,
                );
                let left = builder.get(&leafs, 0);
                let right = builder.get(&leafs, 1);
                let new_folded =
                    codeword_fold_with_challenge(builder, left, right, r, coeff, inv_2);
                builder.assign(&folded, new_folded);
            });

            // assert that final_value[i] = folded
            let final_idx: Var<C::N> = builder.constant(C::N::ZERO);
            builder
                .range(commits.len(), idx_bits.len())
                .for_each(|i_vec, builder| {
                    let i = i_vec[0];
                    let bit = builder.get(&idx_bits, i);
                    builder.assign(
                        &final_idx,
                        final_idx * SymbolicVar::from(C::N::from_canonical_u16(2)) + bit,
                    );
                });
            let final_value = builder.get(&final_codeword.values, final_idx);
            builder.assert_eq::<Ext<C::F, C::EF>>(final_value, folded);
        },
    );

    // 1. check initial claim match with first round sumcheck value
    let batch_coeffs_offset: Var<C::N> = builder.constant(C::N::ZERO);
    let expected_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    iter_zip!(builder, input.rounds).for_each(|ptr_vec, builder| {
        let round = builder.iter_ptr_get(&input.rounds, ptr_vec[0]);
        iter_zip!(builder, round.openings).for_each(|ptr_vec, builder| {
            let opening = builder.iter_ptr_get(&round.openings, ptr_vec[0]);
            // TODO: filter out openings with num_var >= get_basecode_msg_size_log::<C>()
            let var_diff: Var<C::N> = builder.eval(input.max_num_var.get_var() - opening.num_var);
            let scalar_var = pow_2(builder, var_diff);
            let scalar = builder.unsafe_cast_var_to_felt(scalar_var);
            iter_zip!(builder, opening.point_and_evals.evals).for_each(|ptr_vec, builder| {
                let eval = builder.iter_ptr_get(&opening.point_and_evals.evals, ptr_vec[0]);
                let coeff = builder.get(&input.batch_coeffs, batch_coeffs_offset);
                let val: Ext<C::F, C::EF> = builder.eval(eval * coeff * scalar);
                builder.assign(&expected_sum, expected_sum + val);
                builder.assign(&batch_coeffs_offset, batch_coeffs_offset + Usize::from(1));
            });
        });
    });
    let sum: Ext<C::F, C::EF> = {
        let sumcheck_evals = builder.get(&input.proof.sumcheck_proof, 0).evaluations;
        let eval0 = builder.get(&sumcheck_evals, 0);
        let eval1 = builder.get(&sumcheck_evals, 1);
        builder.eval(eval0 + eval1)
    };
    builder.assert_eq::<Ext<C::F, C::EF>>(expected_sum, sum);

    /*
    // 2. check every round of sumcheck match with prev claims
    let fold_len_minus_one: Var<C::N> = builder.eval(input.fold_challenges.len() - Usize::from(1));
    builder
        .range(0, fold_len_minus_one)
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let evals = builder.get(&input.sumcheck_messages, i).evaluations;
            let challenge = builder.get(&input.fold_challenges, i);
            let left = interpolate_uni_poly(builder, &evals, challenge);
            let i_plus_one = builder.eval_expr(i + Usize::from(1));
            let next_evals = builder
                .get(&input.sumcheck_messages, i_plus_one)
                .evaluations;
            let eval0 = builder.get(&next_evals, 0);
            let eval1 = builder.get(&next_evals, 1);
            let right: Ext<C::F, C::EF> = builder.eval(eval0 + eval1);
            builder.assert_eq::<Ext<C::F, C::EF>>(left, right);
        });

    // 3. check final evaluation are correct
    let final_evals = builder
        .get(&input.sumcheck_messages, fold_len_minus_one.clone())
        .evaluations;
    let final_challenge = builder.get(&input.fold_challenges, fold_len_minus_one.clone());
    let left = interpolate_uni_poly(builder, &final_evals, final_challenge);
    let right: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    builder
        .range(0, input.final_message.len())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let final_message = builder.get(&input.final_message, i);
            let point = builder.get(&input.point_evals, i).point;
            // coeff is the eq polynomial evaluated at the first challenge.len() variables
            let num_vars_evaluated: Var<C::N> =
                builder.eval(point.fs.len() - get_basecode_msg_size_log::<C>());
            let ylo = builder.eval(input.fold_challenges.len() - num_vars_evaluated);
            let coeff = eq_eval_with_index(
                builder,
                &point.fs,
                &input.fold_challenges,
                Usize::from(0),
                Usize::Var(ylo),
                Usize::Var(num_vars_evaluated),
            );
            // We assume that the final message is of size 1, so the eq poly is just
            // vec![one].
            // let eq = build_eq_x_r_vec_sequential_with_offset::<C>(
            //     builder,
            //     &point.fs,
            //     Usize::Var(num_vars_evaluated),
            // );
            // eq_coeff = eq * coeff
            // let eq_coeff = builder.dyn_array(eq.len());
            // builder.range(0, eq.len()).for_each(|j_vec, builder| {
            //     let j = j_vec[0];
            //     let next_eq = builder.get(&eq, j);
            //     let next_eq_coeff: Ext<C::F, C::EF> = builder.eval(next_eq * coeff);
            //     builder.set_value(&eq_coeff, j, next_eq_coeff);
            // });
            // let dot_prod = dot_product(builder, &final_message, &eq_coeff);

            // Again assuming final message is a single element
            let final_message = builder.get(&final_message, 0);
            // Again, eq polynomial is just one
            let dot_prod: Ext<C::F, C::EF> = builder.eval(final_message * coeff);
            builder.assign(&right, right + dot_prod);
        });
    builder.assert_eq::<Ext<C::F, C::EF>>(left, right);
         */
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
    use openvm_native_recursion::hints::Hintable;
    use openvm_stark_backend::p3_challenger::GrindingChallenger;
    use openvm_stark_sdk::p3_baby_bear::BabyBear;
    use p3_field::Field;
    use p3_field::FieldAlgebra;
    use rand::thread_rng;

    type F = BabyBear;
    type E = BabyBearExt4;
    type PCS = BasefoldDefault<E>;

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

    use super::{batch_verifier_query_phase, QueryPhaseVerifierInput};

    #[allow(dead_code)]
    pub fn build_batch_verifier_query_phase(
        input: QueryPhaseVerifierInput,
    ) -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        // build test program
        let mut builder = AsmBuilder::<F, E>::default();
        let query_phase_input = QueryPhaseVerifierInput::read(&mut builder);
        batch_verifier_query_phase(&mut builder, query_phase_input);
        builder.halt();
        let program = builder.compile_isa();

        // prepare input
        let mut witness_stream: Vec<Vec<F>> = Vec::new();
        witness_stream.extend(input.write());
        witness_stream.push(vec![F::from_canonical_u32(2).inverse()]);
        // witness_stream.push(vec![F::from_canonical_usize(
        //     input
        //         .circuit_meta
        //         .iter()
        //         .unique_by(|x| x.witin_num_vars)
        //         .count(),
        // )]);
        // witness_stream.push(
        //     input
        //         .circuit_meta
        //         .iter()
        //         .enumerate()
        //         .sorted_by_key(|(_, CircuitIndexMeta { witin_num_vars, .. })| {
        //             Reverse(witin_num_vars)
        //         })
        //         .map(|(index, _)| F::from_canonical_usize(index))
        //         .collect_vec(),
        // );
        // for (query, idx) in input.queries.iter().zip(input.indices.iter()) {
        //     witness_stream.push(vec![F::from_canonical_usize(idx / 2)]);
        //     if let Some(fixed_comm) = &input.fixed_comm {
        //         let log2_witin_max_codeword_size = input.max_num_var + 1;
        //         if log2_witin_max_codeword_size > fixed_comm.log2_max_codeword_size {
        //             witness_stream.push(vec![F::ZERO])
        //         } else {
        //             witness_stream.push(vec![F::ONE])
        //         }
        //     }
        //     for i in 0..input.circuit_meta.len() {
        //         witness_stream.push(vec![F::from_canonical_usize(
        //             query.witin_base_proof.opened_values[i].len() / 2,
        //         )]);
        //         if input.circuit_meta[i].fixed_num_vars > 0 {
        //             witness_stream.push(vec![F::from_canonical_usize(
        //                 if let Some(fixed_base_proof) = &query.fixed_base_proof {
        //                     fixed_base_proof.opened_values[i].len() / 2
        //                 } else {
        //                     0
        //                 },
        //             )]);
        //         }
        //     }
        // }

        (program, witness_stream)
    }

    #[test]
    fn test_verify_query_phase_batch() {
        let mut rng = thread_rng();
        let m1 = ceno_witness::RowMajorMatrix::<F>::rand(&mut rng, 1 << 10, 10);
        let mles_1 = m1.to_mles();
        let matrices = vec![m1];

        let pp = PCS::setup(1 << 20, mpcs::SecurityLevel::Conjecture100bits).unwrap();
        let (pp, vp) = pcs_trim::<E, PCS>(pp, 1 << 20).unwrap();
        let pcs_data = pcs_batch_commit::<E, PCS>(&pp, matrices).unwrap();
        let comm = PCS::get_pure_commitment(&pcs_data);

        let point = E::random_vec(10, &mut rng);
        let evals = mles_1.iter().map(|mle| mle.evaluate(&point)).collect_vec();

        // let evals = mles_1
        //     .iter()
        //     .map(|mle| points.iter().map(|p| mle.evaluate(&p)).collect_vec())
        //     .collect::<Vec<_>>();
        let mut transcript = BasicTranscript::<E>::new(&[]);
        let rounds = vec![(&pcs_data, vec![(point.clone(), evals.clone())])];
        let opening_proof = PCS::batch_open(&pp, rounds, &mut transcript).unwrap();

        let mut transcript = BasicTranscript::<E>::new(&[]);
        let rounds = vec![(comm, vec![(point.len(), (point, evals.clone()))])];
        PCS::batch_verify(&vp, rounds.clone(), &opening_proof, &mut transcript)
            .expect("Native verification failed");

        let mut transcript = BasicTranscript::<E>::new(&[]);
        let batch_coeffs = transcript.sample_and_append_challenge_pows(10, b"batch coeffs");

        let max_num_var = 10;
        let num_rounds = max_num_var; // The final message is of length 1

        // prepare folding challenges via sumcheck round msg + FRI commitment
        let mut fold_challenges: Vec<E> = Vec::with_capacity(10);
        let commits = &opening_proof.commits;

        let sumcheck_messages = opening_proof.sumcheck_proof.as_ref().unwrap();
        for i in 0..num_rounds {
            transcript.append_field_element_exts(sumcheck_messages[i].evaluations.as_slice());
            fold_challenges.push(
                transcript
                    .sample_and_append_challenge(b"commit round")
                    .elements,
            );
            if i < num_rounds - 1 {
                write_digest_to_transcript(&commits[i], &mut transcript);
            }
        }
        transcript.append_field_element_exts_iter(opening_proof.final_message.iter().flatten());

        // check pow
        let pow_bits = vp.get_pow_bits_by_level(mpcs::PowStrategy::FriPow);
        if pow_bits > 0 {
            assert!(transcript.check_witness(pow_bits, opening_proof.pow_witness));
        }

        let queries: Vec<_> = transcript.sample_bits_and_append_vec(
            b"query indices",
            <BasefoldRSParams as BasefoldSpec<E>>::get_number_queries(),
            max_num_var + <BasefoldRSParams as BasefoldSpec<E>>::get_rate_log(),
        );

        let query_input = QueryPhaseVerifierInput {
            // t_inv_halves: vp.encoding_params.t_inv_halves,
            max_num_var: 10,
            fold_challenges,
            batch_coeffs,
            indices: queries,
            proof: opening_proof.into(),
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
        };
        let (program, witness) = build_batch_verifier_query_phase(query_input);

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
}
