// Note: check all XXX comments!

use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;

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