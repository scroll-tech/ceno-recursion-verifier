use ff_ext::BabyBearExt4;
use openvm_native_compiler::prelude::*;

pub use openvm_native_recursion::fri::types::FriConfigVariable as BasefoldConfigVariable;
use openvm_native_recursion::{
    digest::DigestVariable,
    fri::{types::FriQueryProofVariable, TwoAdicMultiplicativeCosetVariable},
    hints::{Hintable, InnerFriProof, InnerVal},
    types::InnerConfig,
    vars::HintSlice,
};
use openvm_stark_sdk::p3_baby_bear::BabyBear;

#[derive(DslVariable, Clone)]
pub struct BasefoldProofVariable<C: Config> {
    pub commit_phase_commits: Array<C, DigestVariable<C>>,
    pub commit_phase_sumcheck_messages: Array<C, Array<C, Felt<C::F>>>, // TODO: should change to extension
    pub query_proofs: Array<C, FriQueryProofVariable<C>>,
    pub final_poly: Array<C, Ext<C::F, C::EF>>,
    pub pow_witness: Felt<C::F>,
}

pub struct InnerBasefoldProof {
    inner_fri_proof: InnerFriProof,
    commit_phase_sumcheck_messages: CommitPhaseSumcheckMessages,
}

pub struct CommitPhaseSumcheckMessages {
    commit_phase_sumcheck_messages: Vec<Vec<BabyBear>>,
}

impl Hintable<InnerConfig> for CommitPhaseSumcheckMessages {
    type HintVariable = Array<InnerConfig, Array<InnerConfig, Felt<<InnerConfig as Config>::F>>>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        Vec::<Vec<InnerVal>>::read(builder) // TODO: Vec::<Vec<BabyBearExt4>>::read(builder) does not work, so how to switch to ext?
    }

    fn write(&self) -> Vec<Vec<InnerVal>> {
        self.commit_phase_sumcheck_messages.write()
    }
}

impl Hintable<InnerConfig> for InnerBasefoldProof {
    type HintVariable = BasefoldProofVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let proof_variable = InnerFriProof::read(builder);
        let commit_phase_commits = proof_variable.commit_phase_commits;
        let commit_phase_sumcheck_messages = CommitPhaseSumcheckMessages::read(builder);
        let query_proofs = proof_variable.query_proofs;
        let final_poly = proof_variable.final_poly;
        let pow_witness = proof_variable.pow_witness;
        Self::HintVariable {
            commit_phase_commits,
            commit_phase_sumcheck_messages,
            query_proofs,
            final_poly,
            pow_witness,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::F>> {
        let mut stream = Vec::new();
        stream.extend(self.inner_fri_proof.write());
        stream.extend(self.commit_phase_sumcheck_messages.write());
        stream
    }
}

#[derive(DslVariable, Clone)]
pub struct BasefoldCommitPhaseProofStepVariable<C: Config> {
    pub sibling_value: Ext<C::F, C::EF>,
    pub opening_proof: HintSlice<C>,
}

#[derive(DslVariable, Clone)]
pub struct BasefoldChallengesVariable<C: Config> {
    pub query_indices: Array<C, Array<C, Var<C::N>>>,
    pub betas: Array<C, Ext<C::F, C::EF>>,
}

#[derive(DslVariable, Clone)]
pub struct DimensionsVariable<C: Config> {
    pub log_height: Usize<C::N>,
}

#[derive(DslVariable, Clone)]
pub struct BatchOpeningVariable<C: Config> {
    pub opened_values: HintSlice<C>,
    pub opening_proof: HintSlice<C>,
}

#[derive(DslVariable, Clone)]
pub struct TwoAdicPcsRoundVariable<C: Config> {
    pub batch_commit: DigestVariable<C>,
    pub mats: Array<C, TwoAdicPcsMatsVariable<C>>,
    /// Optional. `permutation` could be empty if `mats` is already sorted. Otherwise, it's a
    /// permutation of indexes of mats which domains are sorted by degree in descending order.
    pub permutation: Array<C, Usize<C::N>>,
}

#[derive(DslVariable, Clone)]
pub struct TwoAdicPcsMatsVariable<C: Config> {
    pub domain: TwoAdicMultiplicativeCosetVariable<C>,
    pub points: Array<C, Ext<C::F, C::EF>>,
    #[allow(clippy::type_complexity)]
    pub values: Array<C, Array<C, Ext<C::F, C::EF>>>,
}
