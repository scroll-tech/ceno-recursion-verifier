// Note: check all XXX comments!

use ff_ext::{ExtensionField, PoseidonField};
use mpcs::QueryPhaseVerifierInput as InnerQueryPhaseVerifierInput;
use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::{
    hints::{Hintable, VecAutoHintable},
    vars::HintSlice,
};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_field::FieldAlgebra;
use serde::Deserialize;

use super::{basefold::*, extension_mmcs::*, mmcs::*, rs::*, structs::*, utils::*};
use crate::{
    arithmetics::{
        build_eq_x_r_vec_sequential, build_eq_x_r_vec_sequential_with_offset, eq_eval_with_index,
    },
    tower_verifier::{binding::*, program::interpolate_uni_poly},
};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, DIMENSIONS>;
pub type InnerConfig = AsmConfig<F, E>;

use p3_fri::BatchOpening as InnerBatchOpening;
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

impl Hintable<InnerConfig> for BatchOpening {
    type HintVariable = BatchOpeningVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let opened_values = Vec::<Vec<F>>::read(builder);
        let length = Usize::from(builder.hint_var());
        let id = Usize::from(builder.hint_load());
        let opening_proof = HintSlice { length, id };

        BatchOpeningVariable {
            opened_values,
            opening_proof,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.opened_values.write());
        stream.extend(
            self.opening_proof
                .iter()
                .map(|p| p.to_vec())
                .collect::<Vec<_>>()
                .write(),
        );
        stream
    }
}

#[derive(DslVariable, Clone)]
pub struct BatchOpeningVariable<C: Config> {
    pub opened_values: Array<C, Array<C, Felt<C::F>>>,
    pub opening_proof: HintSlice<C>,
}

use p3_fri::CommitPhaseProofStep as InnerCommitPhaseProofStep;
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

impl Hintable<InnerConfig> for CommitPhaseProofStep {
    type HintVariable = CommitPhaseProofStepVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let sibling_value = E::read(builder);
        let length = Usize::from(builder.hint_var());
        let id = Usize::from(builder.hint_load());
        let opening_proof = HintSlice { length, id };

        CommitPhaseProofStepVariable {
            sibling_value,
            opening_proof,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.sibling_value.write());
        stream.extend(
            self.opening_proof
                .iter()
                .map(|p| p.to_vec())
                .collect::<Vec<_>>()
                .write(),
        );
        stream
    }
}
impl VecAutoHintable for CommitPhaseProofStep {}

#[derive(DslVariable, Clone)]
pub struct CommitPhaseProofStepVariable<C: Config> {
    pub sibling_value: Ext<C::F, C::EF>,
    pub opening_proof: HintSlice<C>,
}

#[derive(Deserialize)]
pub struct QueryOpeningProof {
    pub witin_base_proof: BatchOpening,
    pub fixed_base_proof: Option<BatchOpening>,
    pub commit_phase_openings: Vec<CommitPhaseProofStep>,
}
type QueryOpeningProofs = Vec<QueryOpeningProof>;

use mpcs::QueryOpeningProof as InnerQueryOpeningProof;
impl From<InnerQueryOpeningProof<E>> for QueryOpeningProof {
    fn from(proof: InnerQueryOpeningProof<E>) -> Self {
        QueryOpeningProof {
            witin_base_proof: proof.witin_base_proof.into(),
            fixed_base_proof: proof.fixed_base_proof.map(|p| p.into()),
            commit_phase_openings: proof
                .commit_phase_openings
                .into_iter()
                .map(|p| p.into())
                .collect(),
        }
    }
}

impl Hintable<InnerConfig> for QueryOpeningProof {
    type HintVariable = QueryOpeningProofVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let witin_base_proof = BatchOpening::read(builder);
        let fixed_is_some = Usize::Var(usize::read(builder));
        let fixed_base_proof = BatchOpening::read(builder);
        let commit_phase_openings = Vec::<CommitPhaseProofStep>::read(builder);
        QueryOpeningProofVariable {
            witin_base_proof,
            fixed_is_some,
            fixed_base_proof,
            commit_phase_openings,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.witin_base_proof.write());
        if let Some(fixed_base_proof) = &self.fixed_base_proof {
            stream.extend(<usize as Hintable<InnerConfig>>::write(&1));
            stream.extend(fixed_base_proof.write());
        } else {
            stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
            let tmp_proof = BatchOpening {
                opened_values: Vec::new(),
                opening_proof: Vec::new(),
            };
            stream.extend(tmp_proof.write());
        }
        stream.extend(self.commit_phase_openings.write());
        stream
    }
}
impl VecAutoHintable for QueryOpeningProof {}

#[derive(DslVariable, Clone)]
pub struct QueryOpeningProofVariable<C: Config> {
    pub witin_base_proof: BatchOpeningVariable<C>,
    pub fixed_is_some: Usize<C::N>, // 0 <==> false
    pub fixed_base_proof: BatchOpeningVariable<C>,
    pub commit_phase_openings: Array<C, CommitPhaseProofStepVariable<C>>,
}
type QueryOpeningProofsVariable<C> = Array<C, QueryOpeningProofVariable<C>>;

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
    pub max_num_var: usize,
    pub indices: Vec<usize>,
    pub final_message: Vec<Vec<E>>,
    pub batch_coeffs: Vec<E>,
    pub queries: QueryOpeningProofs,
    pub fixed_comm: Option<BasefoldCommitment>,
    pub witin_comm: BasefoldCommitment,
    pub circuit_meta: Vec<CircuitIndexMeta>,
    pub commits: Vec<HashDigest>,
    pub fold_challenges: Vec<E>,
    pub sumcheck_messages: Vec<IOPProverMessage>,
    pub point_evals: Vec<(Point, Vec<E>)>,
}

impl From<InnerQueryPhaseVerifierInput<E>> for QueryPhaseVerifierInput {
    fn from(input: InnerQueryPhaseVerifierInput<E>) -> Self {
        QueryPhaseVerifierInput {
            max_num_var: input.max_num_var,
            indices: input.indices,
            final_message: input.final_message,
            batch_coeffs: input.batch_coeffs,
            queries: input.queries.into_iter().map(|q| q.into()).collect(),
            fixed_comm: input.fixed_comm.map(|comm| comm.into()),
            witin_comm: input.witin_comm.into(),
            circuit_meta: input.circuit_meta.into(),
            commits: input.commits.into(),
            fold_challenges: input.fold_challenges,
            sumcheck_messages: input.sumcheck_messages.into(),
            point_evals: input.point_evals.into(),
        }
    }
}

impl Hintable<InnerConfig> for QueryPhaseVerifierInput {
    type HintVariable = QueryPhaseVerifierInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let max_num_var = Usize::Var(usize::read(builder));
        let indices = Vec::<usize>::read(builder);
        let final_message = Vec::<Vec<E>>::read(builder);
        let batch_coeffs = Vec::<E>::read(builder);
        let queries = QueryOpeningProofs::read(builder);
        let fixed_is_some = Usize::Var(usize::read(builder));
        let fixed_comm = BasefoldCommitment::read(builder);
        let witin_comm = BasefoldCommitment::read(builder);
        let circuit_meta = Vec::<CircuitIndexMeta>::read(builder);
        let commits = Vec::<HashDigest>::read(builder);
        let fold_challenges = Vec::<E>::read(builder);
        let sumcheck_messages = Vec::<IOPProverMessage>::read(builder);
        let point_evals = Vec::<PointAndEvals>::read(builder);

        QueryPhaseVerifierInputVariable {
            max_num_var,
            indices,
            final_message,
            batch_coeffs,
            queries,
            fixed_is_some,
            fixed_comm,
            witin_comm,
            circuit_meta,
            commits,
            fold_challenges,
            sumcheck_messages,
            point_evals,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.max_num_var));
        stream.extend(self.indices.write());
        stream.extend(self.final_message.write());
        stream.extend(self.batch_coeffs.write());
        stream.extend(self.queries.write());
        if let Some(fixed_comm) = &self.fixed_comm {
            stream.extend(<usize as Hintable<InnerConfig>>::write(&1));
            stream.extend(fixed_comm.write());
        } else {
            stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
            let tmp_comm = BasefoldCommitment {
                commit: Default::default(),
                log2_max_codeword_size: 0,
                // trivial_commits: Vec::new(),
            };
            stream.extend(tmp_comm.write());
        }
        stream.extend(self.witin_comm.write());
        stream.extend(self.circuit_meta.write());
        stream.extend(self.commits.write());
        stream.extend(self.fold_challenges.write());
        stream.extend(self.sumcheck_messages.write());
        stream.extend(
            self.point_evals
                .iter()
                .map(|(p, e)| PointAndEvals {
                    point: p.clone(),
                    evals: e.clone(),
                })
                .collect::<Vec<_>>()
                .write(),
        );
        stream
    }
}

#[derive(DslVariable, Clone)]
pub struct QueryPhaseVerifierInputVariable<C: Config> {
    pub max_num_var: Usize<C::N>,
    pub indices: Array<C, Var<C::N>>,
    pub final_message: Array<C, Array<C, Ext<C::F, C::EF>>>,
    pub batch_coeffs: Array<C, Ext<C::F, C::EF>>,
    pub queries: QueryOpeningProofsVariable<C>,
    pub fixed_is_some: Usize<C::N>, // 0 <==> false
    pub fixed_comm: BasefoldCommitmentVariable<C>,
    pub witin_comm: BasefoldCommitmentVariable<C>,
    pub circuit_meta: Array<C, CircuitIndexMetaVariable<C>>,
    pub commits: Array<C, HashDigestVariable<C>>,
    pub fold_challenges: Array<C, Ext<C::F, C::EF>>,
    pub sumcheck_messages: Array<C, IOPProverMessageVariable<C>>,
    pub point_evals: Array<C, PointAndEvalsVariable<C>>,
}

pub(crate) fn batch_verifier_query_phase<C: Config>(
    builder: &mut Builder<C>,
    input: QueryPhaseVerifierInputVariable<C>,
) {
    // Nondeterministically supply inv_2
    let inv_2 = builder.hint_felt();
    builder.assert_eq::<Felt<C::F>>(
        inv_2 * C::F::from_canonical_usize(2),
        C::F::from_canonical_usize(1),
    );
    let two_adic_generators: Array<C, Felt<C::F>> = builder.dyn_array(28);
    for (index, val) in [
        0x1usize, 0x78000000, 0x67055c21, 0x5ee99486, 0xbb4c4e4, 0x2d4cc4da, 0x669d6090,
        0x17b56c64, 0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226, 0x4c734715, 0x11c33e2a,
        0x62c3d2b1, 0x77cad399, 0x54c131f4, 0x4cabd6a6, 0x5cf5713f, 0x3e9430e8, 0xba067a3,
        0x18adc27d, 0x21fd55bc, 0x4b859b3d, 0x3bd57996, 0x4483d85a, 0x3a26eef8, 0x1a427a41,
    ]
    .iter()
    .enumerate()
    {
        let generator = builder.constant(C::F::from_canonical_usize(*val));
        builder.set_value(&two_adic_generators, index, generator);
    }

    // encode_small
    let final_rmm_values_len = builder.get(&input.final_message, 0).len();
    let final_rmm_values = builder.dyn_array(final_rmm_values_len.clone());
    builder
        .range(0, final_rmm_values_len.clone())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let row = builder.get(&input.final_message, i);
            let sum = builder.constant(C::EF::ZERO);
            builder.range(0, row.len()).for_each(|j_vec, builder| {
                let j = j_vec[0];
                let row_j = builder.get(&row, j);
                builder.assign(&sum, sum + row_j);
            });
            builder.set_value(&final_rmm_values, i, sum);
        });
    let final_rmm = RowMajorMatrixVariable {
        values: final_rmm_values,
        width: builder.eval(Usize::from(1)),
    };
    let final_codeword = encode_small(builder, final_rmm);
    // can't use witin_comm.log2_max_codeword_size since it's untrusted
    let log2_witin_max_codeword_size: Var<C::N> =
        builder.eval(input.max_num_var.clone() + get_rate_log::<C>());

    // Nondeterministically supply the index folding_sorted_order
    // Check that:
    // 1. It has the same length as input.circuit_meta (checked by requesting folding_len hints)
    // 2. It does not contain the same index twice (checked via a correspondence array)
    // 3. Indexed witin_num_vars are sorted in decreasing order
    // Infer witin_num_vars through index
    let folding_len = input.circuit_meta.len();
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let folding_sort_surjective: Array<C, Ext<C::F, C::EF>> =
        builder.dyn_array(folding_len.clone());
    builder
        .range(0, folding_len.clone())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            builder.set(&folding_sort_surjective, i, zero.clone());
        });

    // an vector with same length as circuit_meta, which is sorted by num_var in descending order and keep its index
    // for reverse lookup when retrieving next base codeword to involve into batching
    // Sort input.dimensions by height, returns
    // 1. height_order: after sorting by decreasing height, the original index of each entry
    // 2. num_unique_height: number of different heights
    // 3. count_per_unique_height: for each unique height, number of dimensions of that height
    let (folding_sorted_order_index, _num_unique_num_vars, count_per_unique_num_var) =
        sort_with_count(
            builder,
            &input.circuit_meta,
            |m: CircuitIndexMetaVariable<C>| m.witin_num_vars,
        );

    builder
        .range(0, input.indices.len())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let idx = builder.get(&input.indices, i);
            let query = builder.get(&input.queries, i);
            let witin_opened_values = query.witin_base_proof.opened_values;
            let witin_opening_proof = query.witin_base_proof.opening_proof;
            let fixed_is_some = query.fixed_is_some;
            let fixed_commit = query.fixed_base_proof;
            let opening_ext = query.commit_phase_openings;

            // verify base oracle query proof
            // refer to prover documentation for the reason of right shift by 1
            // Nondeterministically supply the bits of idx in BIG ENDIAN
            // These are not only used by the right shift here but also later on idx_shift
            let idx_len = builder.hint_var();
            let idx_bits: Array<C, Var<C::N>> = builder.dyn_array(idx_len);
            builder.range(0, idx_len).for_each(|j_vec, builder| {
                let j = j_vec[0];
                let next_bit = builder.hint_var();
                // Assert that it is a bit
                builder.assert_eq::<Var<C::N>>(next_bit * next_bit, next_bit);
                builder.set_value(&idx_bits, j, next_bit);
            });
            // Right shift
            let idx_len_minus_one: Var<C::N> = builder.eval(idx_len - Usize::from(1));
            builder.assign(&idx_len, idx_len_minus_one);
            let new_idx = bin_to_dec(builder, &idx_bits, idx_len);
            let last_bit = builder.get(&idx_bits, idx_len);
            builder.assert_eq::<Var<C::N>>(Usize::from(2) * new_idx + last_bit, idx);
            builder.assign(&idx, new_idx);

            let (witin_dimensions, fixed_dimensions) =
                get_base_codeword_dimensions(builder, input.circuit_meta.clone());
            // verify witness
            let mmcs_verifier_input = MmcsVerifierInputVariable {
                commit: input.witin_comm.commit.clone(),
                dimensions: witin_dimensions,
                index_bits: idx_bits.clone(), // TODO: double check, should be new idx bits here ?
                opened_values: witin_opened_values.clone(),
                proof: witin_opening_proof,
            };
            mmcs_verify_batch(builder, mmcs_verifier_input);

            // verify fixed
            let fixed_commit_leafs = builder.dyn_array(0);
            builder
                .if_eq(fixed_is_some.clone(), Usize::from(1))
                .then(|builder| {
                    let fixed_opened_values = fixed_commit.opened_values.clone();
                    let fixed_opening_proof = fixed_commit.opening_proof.clone();
                    // new_idx used by mmcs proof
                    let new_idx: Var<C::N> = builder.eval(idx);
                    // Nondeterministically supply a hint:
                    //   0: input.fixed_comm.log2_max_codeword_size < log2_witin_max_codeword_size
                    //   1: >=
                    let branch_le = builder.hint_var();
                    builder.if_eq(branch_le, Usize::from(0)).then(|builder| {
                        // input.fixed_comm.log2_max_codeword_size < log2_witin_max_codeword_size
                        builder.assert_less_than_slow_small_rhs(
                            input.fixed_comm.log2_max_codeword_size.clone(),
                            log2_witin_max_codeword_size,
                        );
                        // idx >> idx_shift
                        let idx_shift_remain: Var<C::N> = builder.eval(
                            idx_len
                                - (log2_witin_max_codeword_size
                                    - input.fixed_comm.log2_max_codeword_size.clone()),
                        );
                        let tmp_idx = bin_to_dec(builder, &idx_bits, idx_shift_remain);
                        builder.assign(&new_idx, tmp_idx);
                    });
                    builder.if_ne(branch_le, Usize::from(0)).then(|builder| {
                        // input.fixed_comm.log2_max_codeword_size >= log2_witin_max_codeword_size
                        let input_codeword_size_plus_one: Var<C::N> = builder
                            .eval(input.fixed_comm.log2_max_codeword_size.clone() + Usize::from(1));
                        builder.assert_less_than_slow_small_rhs(
                            log2_witin_max_codeword_size,
                            input_codeword_size_plus_one,
                        );
                        // idx << -idx_shift
                        let idx_shift = builder.eval(
                            input.fixed_comm.log2_max_codeword_size.clone()
                                - log2_witin_max_codeword_size,
                        );
                        let idx_factor = pow_2(builder, idx_shift);
                        builder.assign(&new_idx, new_idx * idx_factor);
                    });
                    // verify witness
                    let mmcs_verifier_input = MmcsVerifierInputVariable {
                        commit: input.fixed_comm.commit.clone(),
                        dimensions: fixed_dimensions.clone(),
                        index_bits: idx_bits.clone(), // TODO: should be new idx_bits
                        opened_values: fixed_opened_values.clone(),
                        proof: fixed_opening_proof,
                    };
                    mmcs_verify_batch(builder, mmcs_verifier_input);
                    builder.assign(&fixed_commit_leafs, fixed_opened_values);
                });

            // base_codeword_lo_hi
            let base_codeword_lo = builder.dyn_array(folding_len.clone());
            let base_codeword_hi = builder.dyn_array(folding_len.clone());
            builder
                .range(0, folding_len.clone())
                .for_each(|j_vec, builder| {
                    let j = j_vec[0];
                    let circuit_meta = builder.get(&input.circuit_meta, j);
                    let witin_num_polys = circuit_meta.witin_num_polys;
                    let fixed_num_vars = circuit_meta.fixed_num_vars;
                    let fixed_num_polys = circuit_meta.fixed_num_polys;
                    let witin_leafs = builder.get(&witin_opened_values, j);
                    // lo_wit, hi_wit
                    let leafs_len_div_2 = builder.hint_var();
                    let two: Var<C::N> = builder.eval(Usize::from(2));
                    builder.assert_eq::<Var<C::N>>(leafs_len_div_2 * two, witin_leafs.len()); // Can we assume that leafs.len() is even?
                                                                                              // Actual dot_product only computes the first num_polys terms (can we assume leafs_len_div_2 == num_polys?)
                    let lo_wit = dot_product(builder, &input.batch_coeffs, &witin_leafs);
                    let hi_wit = dot_product_with_index(
                        builder,
                        &input.batch_coeffs,
                        &witin_leafs,
                        Usize::from(0),
                        Usize::Var(leafs_len_div_2),
                        witin_num_polys.clone(),
                    );
                    // lo_fixed, hi_fixed
                    let lo_fixed: Ext<C::F, C::EF> =
                        builder.constant(C::EF::from_canonical_usize(0));
                    let hi_fixed: Ext<C::F, C::EF> =
                        builder.constant(C::EF::from_canonical_usize(0));
                    builder
                        .if_ne(fixed_num_vars, Usize::from(0))
                        .then(|builder| {
                            let fixed_leafs = builder.get(&fixed_commit_leafs, j);
                            let leafs_len_div_2 = builder.hint_var();
                            let two: Var<C::N> = builder.eval(Usize::from(2));
                            builder
                                .assert_eq::<Var<C::N>>(leafs_len_div_2 * two, fixed_leafs.len()); // Can we assume that leafs.len() is even?
                                                                                                   // Actual dot_product only computes the first num_polys terms (can we assume leafs_len_div_2 == num_polys?)
                            let tmp_lo_fixed =
                                dot_product(builder, &input.batch_coeffs, &fixed_leafs);
                            let tmp_hi_fixed = dot_product_with_index(
                                builder,
                                &input.batch_coeffs,
                                &fixed_leafs,
                                Usize::from(0),
                                Usize::Var(leafs_len_div_2),
                                fixed_num_polys.clone(),
                            );
                            builder.assign(&lo_fixed, tmp_lo_fixed);
                            builder.assign(&hi_fixed, tmp_hi_fixed);
                        });
                    let lo: Ext<C::F, C::EF> = builder.eval(lo_wit + lo_fixed);
                    let hi: Ext<C::F, C::EF> = builder.eval(hi_wit + hi_fixed);
                    builder.set_value(&base_codeword_lo, j, lo);
                    builder.set_value(&base_codeword_hi, j, hi);
                });

            // fold and query
            let cur_num_var: Var<C::N> = builder.eval(input.max_num_var.clone());
            // let rounds: Var<C::N> = builder.eval(cur_num_var - get_basecode_msg_size_log::<C>() - Usize::from(1));
            let n_d_next_log: Var<C::N> =
                builder.eval(cur_num_var - get_rate_log::<C>() - Usize::from(1));
            // let n_d_next = pow_2(builder, n_d_next_log);

            // first folding challenge
            let r = builder.get(&input.fold_challenges, 0);
            let next_unique_num_vars_count: Var<C::N> = builder.get(&count_per_unique_num_var, 0);
            let folded: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
            builder
                .range(0, next_unique_num_vars_count)
                .for_each(|j_vec, builder| {
                    let j = j_vec[0];
                    let index = builder.get(&folding_sorted_order_index, j);
                    let lo = builder.get(&base_codeword_lo, index.clone());
                    let hi = builder.get(&base_codeword_hi, index.clone());
                    let level: Var<C::N> =
                        builder.eval(cur_num_var + get_rate_log::<C>() - Usize::from(1));
                    let coeff = verifier_folding_coeffs_level(
                        builder,
                        &two_adic_generators,
                        level,
                        &idx_bits,
                        inv_2,
                    );
                    let fold = codeword_fold_with_challenge::<C>(builder, lo, hi, r, coeff, inv_2);
                    builder.assign(&folded, folded + fold);
                });
            let next_unique_num_vars_index: Var<C::N> = builder.eval(Usize::from(1));
            let cumul_num_vars_count: Var<C::N> = builder.eval(next_unique_num_vars_count);
            let n_d_i_log: Var<C::N> = builder.eval(n_d_next_log);
            // let n_d_i: Var<C::N> = builder.eval(n_d_next);
            // zip_eq
            builder.assert_eq::<Var<C::N>>(
                input.commits.len() + Usize::from(1),
                input.fold_challenges.len(),
            );
            builder.assert_eq::<Var<C::N>>(input.commits.len(), opening_ext.len());
            builder
                .range(0, input.commits.len())
                .for_each(|j_vec, builder| {
                    let j = j_vec[0];
                    let pi_comm = builder.get(&input.commits, j);
                    let j_plus_one = builder.eval_expr(j + RVar::from(1));
                    let r = builder.get(&input.fold_challenges, j_plus_one);
                    let leaf = builder.get(&opening_ext, j).sibling_value;
                    let proof = builder.get(&opening_ext, j).opening_proof;
                    builder.assign(&cur_num_var, cur_num_var - Usize::from(1));

                    // next folding challenges
                    let idx_len_minus_one: Var<C::N> = builder.eval(idx_len - Usize::from(1));
                    let is_interpolate_to_right_index = builder.get(&idx_bits, idx_len_minus_one);
                    let new_involved_codewords: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
                    let next_unique_num_vars_count: Var<C::N> =
                        builder.get(&count_per_unique_num_var, next_unique_num_vars_index);
                    builder
                        .range(0, next_unique_num_vars_count)
                        .for_each(|k_vec, builder| {
                            let k = builder.eval_expr(k_vec[0] + cumul_num_vars_count);
                            let index = builder.get(&folding_sorted_order_index, k);
                            let lo = builder.get(&base_codeword_lo, index.clone());
                            let hi = builder.get(&base_codeword_hi, index.clone());
                            builder
                                .if_eq(is_interpolate_to_right_index, Usize::from(1))
                                .then(|builder| {
                                    builder.assign(
                                        &new_involved_codewords,
                                        new_involved_codewords + hi,
                                    );
                                });
                            builder
                                .if_ne(is_interpolate_to_right_index, Usize::from(1))
                                .then(|builder| {
                                    builder.assign(
                                        &new_involved_codewords,
                                        new_involved_codewords + lo,
                                    );
                                });
                        });
                    builder.assign(
                        &cumul_num_vars_count,
                        cumul_num_vars_count + next_unique_num_vars_count,
                    );
                    builder.assign(
                        &next_unique_num_vars_index,
                        next_unique_num_vars_index + Usize::from(1),
                    );

                    // leafs
                    let leafs = builder.dyn_array(2);
                    let new_leaf = builder.eval(folded + new_involved_codewords);
                    builder
                        .if_eq(is_interpolate_to_right_index, Usize::from(1))
                        .then(|builder| {
                            builder.set_value(&leafs, 0, leaf);
                            builder.set_value(&leafs, 1, new_leaf);
                        });
                    builder
                        .if_ne(is_interpolate_to_right_index, Usize::from(1))
                        .then(|builder| {
                            builder.set_value(&leafs, 0, new_leaf);
                            builder.set_value(&leafs, 1, leaf);
                        });
                    // idx >>= 1
                    let idx_len_minus_one: Var<C::N> = builder.eval(idx_len - Usize::from(1));
                    builder.assign(&idx_len, idx_len_minus_one);
                    let new_idx = bin_to_dec(builder, &idx_bits, idx_len);
                    let last_bit = builder.get(&idx_bits, idx_len);
                    builder.assert_eq::<Var<C::N>>(Usize::from(2) * new_idx + last_bit, idx);
                    builder.assign(&idx, new_idx);
                    // n_d_i >> 1
                    builder.assign(&n_d_i_log, n_d_i_log - Usize::from(1));
                    let n_d_i = pow_2(builder, n_d_i_log);
                    // mmcs_ext.verify_batch
                    let dimensions = builder.dyn_array(1);
                    // let two: Var<_> = builder.eval(Usize::from(2));
                    builder.set_value(&dimensions, 0, n_d_i.clone());
                    let opened_values = builder.uninit_fixed_array(1);
                    builder.set_value(&opened_values, 0, leafs.clone());
                    let ext_mmcs_verifier_input = ExtMmcsVerifierInputVariable {
                        commit: pi_comm.clone(),
                        dimensions,
                        index_bits: idx_bits.clone(), // TODO: new idx bits?
                        opened_values,
                        proof,
                    };
                    ext_mmcs_verify_batch::<C>(builder, ext_mmcs_verifier_input);

                    let coeff = verifier_folding_coeffs_level(
                        builder,
                        &two_adic_generators,
                        n_d_i_log.clone(),
                        &idx_bits,
                        inv_2,
                    );
                    let left = builder.get(&leafs, 0);
                    let right = builder.get(&leafs, 1);
                    let new_folded =
                        codeword_fold_with_challenge(builder, left, right, r.clone(), coeff, inv_2);
                    builder.assign(&folded, new_folded);
                });
            let final_value = builder.get(&final_codeword.values, idx.clone());
            builder.assert_eq::<Ext<C::F, C::EF>>(final_value, folded);
        });

    // 1. check initial claim match with first round sumcheck value
    let points = builder.dyn_array(input.batch_coeffs.len());
    let next_point_index: Var<C::N> = builder.eval(Usize::from(0));
    builder
        .range(0, input.point_evals.len())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            let evals = builder.get(&input.point_evals, i).evals;
            let witin_num_vars = builder.get(&input.circuit_meta, i).witin_num_vars;
            // we need to scale up with scalar for witin_num_vars < max_num_var
            let scale_log = builder.eval(input.max_num_var.clone() - witin_num_vars);
            let scale = pow_2(builder, scale_log);
            // Transform scale into a field element
            let scale = builder.unsafe_cast_var_to_felt(scale);
            builder.range(0, evals.len()).for_each(|j_vec, builder| {
                let j = j_vec[0];
                let eval = builder.get(&evals, j);
                let scaled_eval: Ext<C::F, C::EF> = builder.eval(eval * scale);
                builder.set_value(&points, next_point_index, scaled_eval);
                builder.assign(&next_point_index, next_point_index + Usize::from(1));
            });
        });
    let left = dot_product(builder, &input.batch_coeffs, &points);
    let next_sumcheck_evals = builder.get(&input.sumcheck_messages, 0).evaluations;
    let eval0 = builder.get(&next_sumcheck_evals, 0);
    let eval1 = builder.get(&next_sumcheck_evals, 1);
    let right: Ext<C::F, C::EF> = builder.eval(eval0 + eval1);
    builder.assert_eq::<Ext<C::F, C::EF>>(left, right);

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
            let eq = build_eq_x_r_vec_sequential_with_offset::<C>(
                builder,
                &point.fs,
                Usize::Var(num_vars_evaluated),
            );
            let eq_coeff = builder.dyn_array(eq.len());
            builder.range(0, eq.len()).for_each(|j_vec, builder| {
                let j = j_vec[0];
                let next_eq = builder.get(&eq, j);
                let next_eq_coeff: Ext<C::F, C::EF> = builder.eval(next_eq * coeff);
                builder.set_value(&eq_coeff, j, next_eq_coeff);
            });
            let dot_prod = dot_product(builder, &final_message, &eq_coeff);
            builder.assign(&right, right + dot_prod);
        });
    builder.assert_eq::<Ext<C::F, C::EF>>(left, right);
}

pub mod tests {
    use std::{fs::File, io::Read};

    use mpcs::QueryPhaseVerifierInput as InnerQueryPhaseVerifierInput;
    use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::AsmBuilder;
    use openvm_native_recursion::hints::Hintable;
    use openvm_stark_backend::config::StarkGenericConfig;
    use openvm_stark_sdk::{
        config::baby_bear_poseidon2::BabyBearPoseidon2Config, p3_baby_bear::BabyBear,
    };
    use p3_field::{extension::BinomialExtensionField, FieldAlgebra, FieldExtensionAlgebra};
    type SC = BabyBearPoseidon2Config;

    type F = BabyBear;
    type E = BinomialExtensionField<F, 4>;
    type EF = <SC as StarkGenericConfig>::Challenge;

    use super::{batch_verifier_query_phase, QueryPhaseVerifierInput};

    #[allow(dead_code)]
    pub fn build_batch_verifier_query_phase() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        // OpenVM DSL
        let mut builder = AsmBuilder::<F, EF>::default();

        // Witness inputs
        let query_phase_input = QueryPhaseVerifierInput::read(&mut builder);
        batch_verifier_query_phase(&mut builder, query_phase_input);
        builder.halt();

        // Pass in witness stream
        let f = |n: usize| F::from_canonical_usize(n);
        let mut witness_stream: Vec<
            Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
        > = Vec::new();

        // INPUT
        let mut f = File::open("query_phase_verifier_input.bin".to_string()).unwrap();
        let mut content: Vec<u8> = Vec::new();
        f.read_to_end(&mut content).unwrap();
        let input: InnerQueryPhaseVerifierInput<E> = bincode::deserialize(&content).unwrap();
        let input: QueryPhaseVerifierInput = input.into();
        witness_stream.extend(input.write());

        // PROGRAM
        let program: Program<
            p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
        > = builder.compile_isa();

        (program, witness_stream)
    }

    #[test]
    fn test_verify_query_phase_batch() {
        let (program, witness) = build_batch_verifier_query_phase();

        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100);
        let config = NativeConfig::new(system_config, Native);

        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
        executor.execute(program, witness).unwrap();

        // _debug
        // let results = executor.execute_segments(program, witness).unwrap();
        // for seg in results {
        //     println!("=> cycle count: {:?}", seg.metrics.cycle_count);
        // }
    }
}
