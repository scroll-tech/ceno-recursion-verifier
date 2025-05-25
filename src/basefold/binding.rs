use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::FieldAlgebra;
use serde::Deserialize;

use crate::tower_verifier::binding::{IOPProverMessage, IOPProverMessageVariable};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;
const DIGEST_ELEMS: usize = 8;


// Basefold Proof
pub struct BasefoldProofInput {
    pub commits: Vec<Hash>,
    pub final_message: Vec<Vec<E>>,
    pub query_opening_proofs: Vec<QueryOpeningProof>,
    pub sumcheck_proof_is_some: bool,
    pub sumcheck_proof: Vec<IOPProverMessage>,
    pub trivial_proof_is_some: bool,
    pub trivial_proof: TrivialProofInput,
    pub circuit_metas: Vec<CircuitIndexMeta>,
    pub circuit_trivial_metas: Vec<CircuitIndexMeta>,
}
impl Hintable<InnerConfig> for BasefoldProofInput {
    type HintVariable = BasefoldProofVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let commits = Vec::<Hash>::read(builder);
        let final_message = Vec::<Vec<E>>::read(builder);
        let query_opening_proofs = Vec::<QueryOpeningProof>::read(builder);
        let sumcheck_proof_is_some = Usize::Var(usize::read(builder));
        let sumcheck_proof = Vec::<IOPProverMessage>::read(builder);
        let trivial_proof_is_some = Usize::Var(usize::read(builder));
        let trivial_proof = TrivialProofInput::read(builder);
        let circuit_metas = Vec::<CircuitIndexMeta>::read(builder);
        let circuit_trivial_metas = Vec::<CircuitIndexMeta>::read(builder);

        BasefoldProofVariable { 
            commits, 
            final_message, 
            query_opening_proofs, 
            sumcheck_proof_is_some, 
            sumcheck_proof, 
            trivial_proof_is_some, 
            trivial_proof, 
            circuit_metas, 
            circuit_trivial_metas 
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();

        stream.extend(self.commits.write());
        stream.extend(self.final_message.write());
        stream.extend(self.query_opening_proofs.write());
        if self.sumcheck_proof_is_some {
            stream.extend(<usize as Hintable<InnerConfig>>::write(&1));
        } else {
            stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
        }
        stream.extend(self.sumcheck_proof.write());
        if self.trivial_proof_is_some {
            stream.extend(<usize as Hintable<InnerConfig>>::write(&1));
        } else {
            stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
        }
        stream.extend(self.trivial_proof.write());
        stream.extend(self.circuit_metas.write());
        stream.extend(self.circuit_trivial_metas.write());

        stream
    }
}
#[derive(DslVariable, Clone)]
pub struct BasefoldProofVariable<C: Config> {
    pub commits: Array<C, HashVariable<C>>,
    pub final_message: Array<C, Array<C, Ext<C::F, C::EF>>>,
    pub query_opening_proofs: Array<C, QueryOpeningProofVariable<C>>,
    pub sumcheck_proof_is_some: Usize<C::N>, // None <==> 0, Some(_) <==> 1
    pub sumcheck_proof: Array<C, IOPProverMessageVariable<C>>,
    pub trivial_proof_is_some: Usize<C::N>, // None <==> 0, Some(_) <==> 1
    pub trivial_proof: TrivialProofVariable<C>,
    pub circuit_metas: Array<C, CircuitIndexMetaVariable<C>>,
    pub circuit_trivial_metas: Array<C, CircuitIndexMetaVariable<C>>,
}


// Trivial Proof
#[derive(Default)]
pub struct TrivialProofInput {
    pub rows: usize,
    pub matrices: Vec<Vec<DenseMatrixInput>>,
}
impl Hintable<InnerConfig> for TrivialProofInput {
    type HintVariable = TrivialProofVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let rows = Usize::Var(usize::read(builder));
        let matrices = builder.dyn_array(rows.clone());
        builder.range(0, rows.clone()).for_each(|idx_vec, builder| {
            let row = Vec::<DenseMatrixInput>::read(builder);
            builder.set(&matrices, idx_vec[0], row);
        });

        TrivialProofVariable { rows, matrices }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();

        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.rows));
        self.matrices.iter().for_each(|m| {
            stream.extend(m.write());
        });

        stream
    }
}

#[derive(DslVariable, Clone)]
pub struct TrivialProofVariable<C: Config> {
    pub rows: Usize<C::N>,
    pub matrices: Array<C, Array<C, DenseMatrixVariable<C>>>,
}


// Dense Matrix
pub struct DenseMatrixInput {
    pub values: Vec<Vec<F>>,
}

impl Hintable<InnerConfig> for DenseMatrixInput {
    type HintVariable = DenseMatrixVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let values = Vec::<Vec<F>>::read(builder);
        DenseMatrixVariable { values }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.values.write());
        stream
    }
}

#[derive(DslVariable, Clone)]
pub struct DenseMatrixVariable<C: Config> {
    pub values: Array<C, Array<C, Felt<C::F>>>,
}
impl VecAutoHintable for DenseMatrixInput {}


// Hash Digest
#[derive(Deserialize)]
pub struct Hash {
    pub value: [F; DIGEST_ELEMS],
}

impl Hintable<InnerConfig> for Hash {
    type HintVariable = HashVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let value = builder.dyn_array(DIGEST_ELEMS);
        for i in 0..DIGEST_ELEMS {
            let tmp = F::read(builder);
            builder.set(&value, i, tmp);
        }

        HashVariable { value }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        // Write out each entries
        for i in 0..DIGEST_ELEMS {
            stream.extend(self.value[i].write());
        }
        stream
    }
}
impl VecAutoHintable for Hash {}

#[derive(DslVariable, Clone)]
pub struct HashVariable<C: Config> {
    pub value: Array<C, Felt<C::F>>,
}


// Query Opening Proof
#[derive(Deserialize)]
pub struct QueryOpeningProof {
    pub witin_base_proof: BatchOpening,
    pub fixed_base_proof: Option<BatchOpening>,
    pub commit_phase_openings: Vec<CommitPhaseProofStep>,
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


// MMCS Proof
pub type MmcsProof = Vec<[F; DIGEST_ELEMS]>;
pub type MmcsProofVariable<C> = Array<C, Array<C, Felt<<C as Config>::F>>>;

// CommitPhaseProofStep
#[derive(Deserialize)]
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


// Batch Opening
#[derive(Deserialize, Default)]
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


// Circuit Metas
#[derive(DslVariable, Clone)]
pub struct CircuitIndexMetaVariable<C: Config> {
    pub order_idx: Usize<C::N>,
    pub witin_num_vars: Usize<C::N>,
    pub witin_num_polys: Usize<C::N>,
    pub fixed_num_vars: Usize<C::N>,
    pub fixed_num_polys: Usize<C::N>,
}

#[derive(Deserialize)]
pub struct CircuitIndexMeta {
    pub order_idx: usize,
    pub witin_num_vars: usize,
    pub witin_num_polys: usize,
    pub fixed_num_vars: usize,
    pub fixed_num_polys: usize,
}

impl Hintable<InnerConfig> for CircuitIndexMeta {
    type HintVariable = CircuitIndexMetaVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let order_idx = Usize::Var(usize::read(builder));
        let witin_num_vars = Usize::Var(usize::read(builder));
        let witin_num_polys = Usize::Var(usize::read(builder));
        let fixed_num_vars = Usize::Var(usize::read(builder));
        let fixed_num_polys = Usize::Var(usize::read(builder));

        CircuitIndexMetaVariable {
            order_idx,
            witin_num_vars,
            witin_num_polys,
            fixed_num_vars,
            fixed_num_polys,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.order_idx,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.witin_num_vars,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.witin_num_polys,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.fixed_num_vars,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.fixed_num_polys,
        ));
        stream
    }
}
impl VecAutoHintable for CircuitIndexMeta {}


/*
#[derive(Deserialize)]
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

#[allow(clippy::too_many_arguments)]
pub fn batch_verifier_query_phase<E: ExtensionField, Spec: BasefoldSpec<E>>(
    max_num_var: usize,
    indices: &[usize],
    vp: &<Spec::EncodingScheme as EncodingScheme<E>>::VerifierParameters,
    final_message: &[Vec<E>],
    batch_coeffs: &[E],
    queries: &QueryOpeningProofs<E>,
    fixed_comm: Option<&BasefoldCommitment<E>>,
    witin_comm: &BasefoldCommitment<E>,
    circuit_meta: &[CircuitIndexMeta],
    commits: &[Digest<E>],
    fold_challenges: &[E],
    sumcheck_messages: &[IOPProverMessage<E>],
    point_evals: &[(Point<E>, Vec<E>)],
) where
    E::BaseField: Serialize + DeserializeOwned,
{
*/


/*
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
                // trivial_commits: Vec::new(),
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
  */