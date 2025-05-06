// Note: check all XXX comments!

use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::FieldAlgebra;

use crate::tower_verifier::binding::*;
use super::{basefold::*, extension_mmcs::*, mmcs::*, rs::*, structs::*, utils::*};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, DIMENSIONS>;
pub type InnerConfig = AsmConfig<F, E>;

pub struct BatchOpening {
    pub opened_values: Vec<Vec<F>>,
    pub opening_proof: MmcsProof,
}

impl Hintable<InnerConfig> for BatchOpening {
  type HintVariable = BatchOpeningVariable<InnerConfig>;

  fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
      let opened_values = Vec::<Vec::<F>>::read(builder);
      let opening_proof = Vec::<Vec::<F>>::read(builder);
      BatchOpeningVariable {
          opened_values,
          opening_proof,
      }
  }

  fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
      let mut stream = Vec::new();
      stream.extend(self.opened_values.write());
      stream.extend(self.opening_proof.iter().map(|p| p.to_vec()).collect::<Vec<_>>().write());
      stream
  }
}

#[derive(DslVariable, Clone)]
pub struct BatchOpeningVariable<C: Config> {
    pub opened_values: Array<C, Array<C, Felt<C::F>>>,
    pub opening_proof: MmcsProofVariable<C>,
}

pub struct CommitPhaseProofStep {
    pub sibling_value: E,
    pub opening_proof: MmcsProof,
}

impl Hintable<InnerConfig> for CommitPhaseProofStep {
    type HintVariable = CommitPhaseProofStepVariable<InnerConfig>;
  
    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let sibling_value = E::read(builder);
        let opening_proof = Vec::<Vec::<F>>::read(builder);
        CommitPhaseProofStepVariable {
            sibling_value,
            opening_proof,
        }
    }
  
    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.sibling_value.write());
        stream.extend(self.opening_proof.iter().map(|p| p.to_vec()).collect::<Vec<_>>().write());
        stream
    }
  }
impl VecAutoHintable for CommitPhaseProofStep {}

#[derive(DslVariable, Clone)]
pub struct CommitPhaseProofStepVariable<C: Config> {
    pub sibling_value: Ext<C::F, C::EF>,
    pub opening_proof: MmcsProofVariable<C>,
}

pub struct QueryOpeningProof {
    pub witin_base_proof: BatchOpening,
    pub fixed_base_proof: Option<BatchOpening>,
    pub commit_phase_openings: Vec<CommitPhaseProofStep>,
}
type QueryOpeningProofs = Vec<QueryOpeningProof>;

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
        PointAndEvalsVariable {
            point,
            evals,
        }
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

pub struct QueryPhaseVerifierInput {
    pub max_num_var: usize,
    pub indices: Vec<usize>,
    pub vp: RSCodeVerifierParameters,
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

impl Hintable<InnerConfig> for QueryPhaseVerifierInput {
    type HintVariable = QueryPhaseVerifierInputVariable<InnerConfig>;
  
    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let max_num_var = Usize::Var(usize::read(builder));
        let indices = Vec::<usize>::read(builder);
        let vp = RSCodeVerifierParameters::read(builder);
        let final_message = Vec::<Vec::<E>>::read(builder);
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
            vp,
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
        stream.extend(self.vp.write());
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
                trivial_commits: Vec::new(),
            };
            stream.extend(tmp_comm.write());
        }
        stream.extend(self.witin_comm.write());
        stream.extend(self.circuit_meta.write());
        stream.extend(self.commits.write());
        stream.extend(self.fold_challenges.write());
        stream.extend(self.sumcheck_messages.write());
        stream.extend(self.point_evals.iter().map(|(p, e)|
            PointAndEvals { point: p.clone(), evals: e.clone() }
        ).collect::<Vec<_>>().write());
        stream
    }
  }

#[derive(DslVariable, Clone)]
pub struct QueryPhaseVerifierInputVariable<C: Config> {
    pub max_num_var: Usize<C::N>,
    pub indices: Array<C, Var<C::N>>,
    pub vp: RSCodeVerifierParametersVariable<C>,
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
    builder.assert_eq::<Felt<C::F>>(inv_2 * C::F::from_canonical_usize(2), C::F::from_canonical_usize(1));

    // encode_small
    let final_rmm_values_len = builder.get(&input.final_message, 0).len();
    let final_rmm_values = builder.dyn_array(final_rmm_values_len.clone());
    builder.range(0, final_rmm_values_len.clone()).for_each(|i_vec, builder| {
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
    let final_codeword = encode_small(
        builder, 
        input.vp.clone(), 
        final_rmm,
    );
    // XXX: we might need to add generics to MMCS to account for different field types
    let mmcs_ext: ExtensionMmcsVariable<C> = Default::default();
    let mmcs: MerkleTreeMmcsVariable<C> = Default::default();
    // can't use witin_comm.log2_max_codeword_size since it's untrusted
    let log2_witin_max_codeword_size: Var<C::N> = builder.eval(input.max_num_var.clone() + get_rate_log::<C>());

    // Nondeterministically supply the index folding_sorted_order
    // Check that:
    // 1. It has the same length as input.circuit_meta (checked by requesting folding_len hints)
    // 2. It does not contain the same index twice (checked via a correspondence array)
    // 3. Indexed witin_num_vars are sorted in decreasing order
    // Infer witin_num_vars through index
    let folding_len = input.circuit_meta.len();
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let folding_sort_surjective: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(folding_len.clone());
    builder.range(0, folding_len.clone()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        builder.set(&folding_sort_surjective, i, zero.clone());
    });

    // an vector with same length as circuit_meta, which is sorted by num_var in descending order and keep its index
    // for reverse lookup when retrieving next base codeword to involve into batching
    // Sort input.dimensions by height, returns
    // 1. height_order: after sorting by decreasing height, the original index of each entry
    // 2. num_unique_height: number of different heights
    // 3. count_per_unique_height: for each unique height, number of dimensions of that height
    let (
        folding_sorted_order_index, 
        _num_unique_num_vars, 
        count_per_unique_num_var
    ) = sort_with_count(
        builder,
        &input.circuit_meta,
        |m: CircuitIndexMetaVariable<C>| m.witin_num_vars,
    );

    builder.range(0, input.indices.len()).for_each(|i_vec, builder| {
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
            index: idx,
            opened_values: witin_opened_values.clone(),
            proof: witin_opening_proof,
        };
        mmcs_verify_batch(builder, mmcs.clone(), mmcs_verifier_input);

        // verify fixed
        let fixed_commit_leafs = builder.dyn_array(0);
        builder.if_eq(fixed_is_some.clone(), Usize::from(1)).then(|builder| {
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
                builder.assert_less_than_slow_small_rhs(input.fixed_comm.log2_max_codeword_size.clone(), log2_witin_max_codeword_size);
                // idx >> idx_shift
                let idx_shift_remain: Var<C::N> = builder.eval(idx_len - (log2_witin_max_codeword_size - input.fixed_comm.log2_max_codeword_size.clone()));
                let tmp_idx = bin_to_dec(builder, &idx_bits, idx_shift_remain);
                builder.assign(&new_idx, tmp_idx);
            });
            builder.if_ne(branch_le, Usize::from(0)).then(|builder| {
                // input.fixed_comm.log2_max_codeword_size >= log2_witin_max_codeword_size
                let input_codeword_size_plus_one: Var<C::N> = builder.eval(input.fixed_comm.log2_max_codeword_size.clone() + Usize::from(1));
                builder.assert_less_than_slow_small_rhs(log2_witin_max_codeword_size, input_codeword_size_plus_one);
                // idx << -idx_shift
                let idx_shift = builder.eval(input.fixed_comm.log2_max_codeword_size.clone() - log2_witin_max_codeword_size);
                let idx_factor = pow_2(builder, idx_shift);
                builder.assign(&new_idx, new_idx * idx_factor);
            });
            // verify witness
            let mmcs_verifier_input = MmcsVerifierInputVariable {
                commit: input.fixed_comm.commit.clone(),
                dimensions: fixed_dimensions.clone(),
                index: new_idx,
                opened_values: fixed_opened_values.clone(),
                proof: fixed_opening_proof,
            };
            mmcs_verify_batch(builder, mmcs.clone(), mmcs_verifier_input);
            builder.assign(&fixed_commit_leafs, fixed_opened_values);
        });

        // base_codeword_lo_hi
        let base_codeword_lo = builder.dyn_array(folding_len.clone());
        let base_codeword_hi = builder.dyn_array(folding_len.clone());
        builder.range(0, folding_len.clone()).for_each(|j_vec, builder| {
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
            let lo_wit = dot_product(builder, 
                &input.batch_coeffs, 
                &witin_leafs, 
                Usize::from(0),
                Usize::from(0),
                witin_num_polys.clone(), 
            );
            let hi_wit = dot_product(builder, 
                &input.batch_coeffs, 
                &witin_leafs, 
                Usize::from(0),
                Usize::Var(leafs_len_div_2), 
                witin_num_polys.clone(), 
            );
            // lo_fixed, hi_fixed
            let lo_fixed: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_usize(0));
            let hi_fixed: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_usize(0));
            builder.if_ne(fixed_num_vars, Usize::from(0)).then(|builder| {
                let fixed_leafs = builder.get(&fixed_commit_leafs, j);
                let leafs_len_div_2 = builder.hint_var();
                let two: Var<C::N> = builder.eval(Usize::from(2));
                builder.assert_eq::<Var<C::N>>(leafs_len_div_2 * two, fixed_leafs.len()); // Can we assume that leafs.len() is even?
                // Actual dot_product only computes the first num_polys terms (can we assume leafs_len_div_2 == num_polys?)
                let tmp_lo_fixed = dot_product(builder, 
                    &input.batch_coeffs, 
                    &fixed_leafs, 
                    Usize::from(0),
                    Usize::from(0),
                    fixed_num_polys.clone(), 
                );
                let tmp_hi_fixed = dot_product(builder, 
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
        let n_d_next_log: Var<C::N> = builder.eval(cur_num_var - get_rate_log::<C>() - Usize::from(1));
        // let n_d_next = pow_2(builder, n_d_next_log);

        // first folding challenge
        let r = builder.get(&input.fold_challenges, 0);
        let next_unique_num_vars_count: Var<C::N> = builder.get(&count_per_unique_num_var, 0);
        let folded: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
        builder.range(0, next_unique_num_vars_count).for_each(|j_vec, builder| {
            let j = j_vec[0];
            let index = builder.get(&folding_sorted_order_index, j);
            let lo = builder.get(&base_codeword_lo, index.clone());
            let hi = builder.get(&base_codeword_hi, index.clone());
            let level: Var<C::N> = builder.eval(cur_num_var + get_rate_log::<C>() - Usize::from(1));
            let coeffs = verifier_folding_coeffs_level(builder, &input.vp, level);
            let coeff = builder.get(&coeffs, idx);
            let fold = codeword_fold_with_challenge::<C>(builder, lo, hi, r, coeff, inv_2);
            builder.assign(&folded, folded + fold);
        });
        let next_unique_num_vars_index: Var<C::N> = builder.eval(Usize::from(1));
        let cumul_num_vars_count: Var<C::N> = builder.eval(next_unique_num_vars_count);
        let n_d_i_log: Var<C::N> = builder.eval(n_d_next_log);
        // let n_d_i: Var<C::N> = builder.eval(n_d_next);
        // zip_eq
        builder.assert_eq::<Var<C::N>>(input.commits.len() + Usize::from(1), input.fold_challenges.len());
        builder.assert_eq::<Var<C::N>>(input.commits.len(), opening_ext.len());
        builder.range(0, input.commits.len()).for_each(|j_vec, builder| {
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
            let next_unique_num_vars_count: Var<C::N> = builder.get(&count_per_unique_num_var, next_unique_num_vars_index);
            builder.range(0, next_unique_num_vars_count).for_each(|k_vec, builder| {
                let k = builder.eval_expr(k_vec[0] + cumul_num_vars_count);
                let index = builder.get(&folding_sorted_order_index, k);
                let lo = builder.get(&base_codeword_lo, index.clone());
                let hi = builder.get(&base_codeword_hi, index.clone());
                builder.if_eq(is_interpolate_to_right_index, Usize::from(1)).then(|builder| {
                    builder.assign(&new_involved_codewords, new_involved_codewords + hi);
                });
                builder.if_ne(is_interpolate_to_right_index, Usize::from(1)).then(|builder| {
                    builder.assign(&new_involved_codewords, new_involved_codewords + lo);
                });
            });
            builder.assign(&cumul_num_vars_count, cumul_num_vars_count + next_unique_num_vars_count);
            builder.assign(&next_unique_num_vars_index, next_unique_num_vars_index + Usize::from(1));

            // leafs
            let leafs = builder.dyn_array(2);
            let new_leaf = builder.eval(folded + new_involved_codewords);
            builder.if_eq(is_interpolate_to_right_index, Usize::from(1)).then(|builder| {
                builder.set_value(&leafs, 0, leaf);
                builder.set_value(&leafs, 1, new_leaf);
            });
            builder.if_ne(is_interpolate_to_right_index, Usize::from(1)).then(|builder| {
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
            let dimensions = builder.uninit_fixed_array(1);
            let two = builder.eval(Usize::from(2));
            builder.set_value(&dimensions, 0, DimensionsVariable {
                width: two,
                height: n_d_i.clone(),
            });
            let opened_values = builder.uninit_fixed_array(1);
            builder.set_value(&opened_values, 0, leafs.clone());
            let ext_mmcs_verifier_input = ExtMmcsVerifierInputVariable {
                commit: pi_comm.clone(),
                dimensions,
                index: idx.clone(),
                opened_values,
                proof,
            };
            ext_mmcs_verify_batch::<C>(builder, mmcs_ext.clone(), ext_mmcs_verifier_input);

            let coeffs = verifier_folding_coeffs_level(builder, &input.vp, n_d_i_log.clone());
            let coeff = builder.get(&coeffs, idx.clone());
            let left = builder.get(&leafs, 0);
            let right = builder.get(&leafs, 1);
            let new_folded = codeword_fold_with_challenge(
                builder, 
                left, 
                right, 
                r.clone(), 
                coeff, 
                inv_2
            );
            builder.assign(&folded, new_folded);
        });
        let final_value = builder.get(&final_codeword.values, idx.clone());
        builder.assert_eq::<Ext::<C::F, C::EF>>(final_value, folded);
    });

    
    /*
    // 1. check initial claim match with first round sumcheck value
    assert_eq!(
        // we need to scale up with scalar for witin_num_vars < max_num_var
        dot_product::<E, _, _>(
            batch_coeffs.iter().copied(),
            point_evals.iter().zip_eq(circuit_meta.iter()).flat_map(
                |((_, evals), CircuitIndexMeta { witin_num_vars, .. })| {
                    evals.iter().copied().map(move |eval| {
                        eval * E::from_u64(1 << (max_num_var - witin_num_vars) as u64)
                    })
                }
            )
        ),
        { sumcheck_messages[0].evaluations[0] + sumcheck_messages[0].evaluations[1] }
    );
    // 2. check every round of sumcheck match with prev claims
    for i in 0..fold_challenges.len() - 1 {
        assert_eq!(
            interpolate_uni_poly(&sumcheck_messages[i].evaluations, fold_challenges[i]),
            { sumcheck_messages[i + 1].evaluations[0] + sumcheck_messages[i + 1].evaluations[1] }
        );
    }
    // 3. check final evaluation are correct
    assert_eq!(
        interpolate_uni_poly(
            &sumcheck_messages[fold_challenges.len() - 1].evaluations,
            fold_challenges[fold_challenges.len() - 1]
        ),
        izip!(final_message, point_evals.iter().map(|(point, _)| point))
            .map(|(final_message, point)| {
                // coeff is the eq polynomial evaluated at the first challenge.len() variables
                let num_vars_evaluated = point.len()
                    - <Spec::EncodingScheme as EncodingScheme<E>>::get_basecode_msg_size_log();
                let coeff = eq_eval(
                    &point[..num_vars_evaluated],
                    &fold_challenges[fold_challenges.len() - num_vars_evaluated..],
                );
                // Compute eq as the partially evaluated eq polynomial
                let eq = build_eq_x_r_vec(&point[num_vars_evaluated..]);
                dot_product(
                    final_message.iter().copied(),
                    eq.into_iter().map(|e| e * coeff),
                )
            })
            .sum()
    );
    */
}
