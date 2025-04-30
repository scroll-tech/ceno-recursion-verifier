// Note: check all XXX comments!

use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::FieldAlgebra;

use crate::tower_verifier::binding::*;
use super::{basefold::*, mmcs::*, rs::*, structs::*};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
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
    pub sibling_value: F,
    pub opening_proof: MmcsProof,
}

impl Hintable<InnerConfig> for CommitPhaseProofStep {
    type HintVariable = CommitPhaseProofStepVariable<InnerConfig>;
  
    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let sibling_value = F::read(builder);
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
    pub sibling_value: Felt<C::F>,
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
    let mmcs_ext: MerkleTreeMmcsVariables<C> = Default::default();
    let mmcs: MerkleTreeMmcsVariables<C> = Default::default();
    // can't use witin_comm.log2_max_codeword_size since it's untrusted
    let log2_witin_max_codeword_size: Var<C::N> = builder.eval(input.max_num_var + get_rate_log::<C>());
    // Nondeterministically supply the index folding_sorted_order
    // Check that:
    // 1. It has the same length as input.circuit_meta (checked by requesting folding_len hints)
    // 2. It does not contain the same index twice (checked via a correspondence array)
    // 3. Indexed witin_num_vars are sorted in decreasing order
    // Infer witin_num_vars through index
    let folding_len = input.circuit_meta.len();
    // let folding_sorted_order_index = builder.dyn_array(folding_len);

    /*
    // an vector with same length as circuit_meta, which is sorted by num_var in descending order and keep its index
    // for reverse lookup when retrieving next base codeword to involve into batching
    let folding_sorted_order = circuit_meta
        .iter()
        .enumerate()
        .sorted_by_key(|(_, CircuitIndexMeta { witin_num_vars, .. })| Reverse(witin_num_vars))
        .map(|(index, CircuitIndexMeta { witin_num_vars, .. })| (witin_num_vars, index))
        .collect_vec();

    indices.iter().zip_eq(queries).for_each(
        |(
            idx,
            QueryOpeningProof {
                witin_base_proof:
                    BatchOpening {
                        opened_values: witin_opened_values,
                        opening_proof: witin_opening_proof,
                    },
                fixed_base_proof: fixed_commit_option,
                commit_phase_openings: opening_ext,
            },
        )| {
            // verify base oracle query proof
            // refer to prover documentation for the reason of right shift by 1
            let mut idx = idx >> 1;

            let (witin_dimentions, fixed_dimentions) =
                get_base_codeword_dimentions::<E, Spec>(circuit_meta);
            // verify witness
            mmcs.verify_batch(
                &witin_comm.commit,
                &witin_dimentions,
                idx,
                witin_opened_values,
                witin_opening_proof,
            )
            .expect("verify witin commit batch failed");

            // verify fixed
            let fixed_commit_leafs = if let Some(fixed_comm) = fixed_comm {
                let BatchOpening {
                    opened_values: fixed_opened_values,
                    opening_proof: fixed_opening_proof,
                } = &fixed_commit_option.as_ref().unwrap();
                

                mmcs.verify_batch(
                    &fixed_comm.commit,
                    &fixed_dimentions,
                    {
                        let idx_shift = log2_witin_max_codeword_size as i32
                            - fixed_comm.log2_max_codeword_size as i32;
                        if idx_shift > 0 {
                            idx >> idx_shift
                        } else {
                            idx << -idx_shift
                        }
                    },
                    fixed_opened_values,
                    fixed_opening_proof,
                )
                .expect("verify fixed commit batch failed");
                fixed_opened_values
            } else {
                &vec![]
            };

            let mut fixed_commit_leafs_iter = fixed_commit_leafs.iter();
            let mut batch_coeffs_iter = batch_coeffs.iter();

            let base_codeword_lo_hi = circuit_meta
                .iter()
                .zip_eq(witin_opened_values)
                .map(
                    |(
                        CircuitIndexMeta {
                            witin_num_polys,
                            fixed_num_vars,
                            fixed_num_polys,
                            ..
                        },
                        witin_leafs,
                    )| {
                        let (lo, hi) = std::iter::once((witin_leafs, *witin_num_polys))
                            .chain((*fixed_num_vars > 0).then(|| {
                                (fixed_commit_leafs_iter.next().unwrap(), *fixed_num_polys)
                            }))
                            .map(|(leafs, num_polys)| {
                                let batch_coeffs = batch_coeffs_iter
                                    .by_ref()
                                    .take(num_polys)
                                    .copied()
                                    .collect_vec();
                                let (lo, hi): (&[E::BaseField], &[E::BaseField]) =
                                    leafs.split_at(leafs.len() / 2);
                                (
                                    dot_product::<E, _, _>(
                                        batch_coeffs.iter().copied(),
                                        lo.iter().copied(),
                                    ),
                                    dot_product::<E, _, _>(
                                        batch_coeffs.iter().copied(),
                                        hi.iter().copied(),
                                    ),
                                )
                            })
                            // fold witin/fixed lo, hi together because they share the same num_vars
                            .reduce(|(lo_wit, hi_wit), (lo_fixed, hi_fixed)| {
                                (lo_wit + lo_fixed, hi_wit + hi_fixed)
                            })
                            .expect("unreachable");
                        (lo, hi)
                    },
                )
                .collect_vec();
            debug_assert_eq!(folding_sorted_order.len(), base_codeword_lo_hi.len());
            debug_assert!(fixed_commit_leafs_iter.next().is_none());
            debug_assert!(batch_coeffs_iter.next().is_none());

            // fold and query
            let mut cur_num_var = max_num_var;
            // -1 because for there are only #max_num_var-1 openings proof
            let rounds = cur_num_var
                - <Spec::EncodingScheme as EncodingScheme<E>>::get_basecode_msg_size_log()
                - 1;
            let n_d_next = 1
                << (cur_num_var + <Spec::EncodingScheme as EncodingScheme<E>>::get_rate_log() - 1);
            debug_assert_eq!(rounds, fold_challenges.len() - 1);
            debug_assert_eq!(rounds, commits.len(),);
            debug_assert_eq!(rounds, opening_ext.len(),);

            // first folding challenge
            let r = fold_challenges.first().unwrap();

            let mut folding_sorted_order_iter = folding_sorted_order.iter();
            // take first batch which num_vars match max_num_var to initial fold value
            let mut folded = folding_sorted_order_iter
                .by_ref()
                .peeking_take_while(|(num_vars, _)| **num_vars == cur_num_var)
                .map(|(_, index)| {
                    let (lo, hi) = &base_codeword_lo_hi[*index];
                    let coeff =
                        <Spec::EncodingScheme as EncodingScheme<E>>::verifier_folding_coeffs_level(
                            vp,
                            cur_num_var
                                + <Spec::EncodingScheme as EncodingScheme<E>>::get_rate_log()
                                - 1,
                        )[idx];
                    codeword_fold_with_challenge(&[*lo, *hi], *r, coeff, inv_2)
                })
                .sum::<E>();

            let mut n_d_i = n_d_next;
            for (
                (pi_comm, r),
                CommitPhaseProofStep {
                    sibling_value: leaf,
                    opening_proof: proof,
                },
            ) in commits
                .iter()
                .zip_eq(fold_challenges.iter().skip(1))
                .zip_eq(opening_ext)
            {
                cur_num_var -= 1;

                let is_interpolate_to_right_index = (idx & 1) == 1;
                let new_involved_codewords = folding_sorted_order_iter
                    .by_ref()
                    .peeking_take_while(|(num_vars, _)| **num_vars == cur_num_var)
                    .map(|(_, index)| {
                        let (lo, hi) = &base_codeword_lo_hi[*index];
                        if is_interpolate_to_right_index {
                            *hi
                        } else {
                            *lo
                        }
                    })
                    .sum::<E>();

                let mut leafs = vec![*leaf; 2];
                leafs[is_interpolate_to_right_index as usize] = folded + new_involved_codewords;
                idx >>= 1;
                mmcs_ext
                    .verify_batch(
                        pi_comm,
                        &[Dimensions {
                            width: 2,
                            // width is 2, thus height divide by 2 via right shift
                            height: n_d_i >> 1,
                        }],
                        idx,
                        slice::from_ref(&leafs),
                        proof,
                    )
                    .expect("verify failed");
                let coeff =
                    <Spec::EncodingScheme as EncodingScheme<E>>::verifier_folding_coeffs_level(
                        vp,
                        log2_strict_usize(n_d_i) - 1,
                    )[idx];
                debug_assert_eq!(
                    <Spec::EncodingScheme as EncodingScheme<E>>::verifier_folding_coeffs_level(
                        vp,
                        log2_strict_usize(n_d_i) - 1,
                    )
                    .len(),
                    n_d_i >> 1
                );
                folded = codeword_fold_with_challenge(&[leafs[0], leafs[1]], *r, coeff, inv_2);
                n_d_i >>= 1;
            }
            debug_assert!(folding_sorted_order_iter.next().is_none());
            assert!(
                final_codeword.values[idx] == folded,
                "final_codeword.values[idx] value {:?} != folded {:?}",
                final_codeword.values[idx],
                folded
            );
        },
    );
    exit_span!(check_queries_span);

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
