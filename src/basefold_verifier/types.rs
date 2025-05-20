use openvm_native_compiler::prelude::*;

pub use openvm_native_recursion::fri::types::FriConfigVariable;
use openvm_native_recursion::{
    digest::DigestVariable,
    fri::{types::FriQueryProofVariable, TwoAdicMultiplicativeCosetVariable},
    hints::{Hintable, InnerFriProof as OpenVMInnerFriProof},
    types::InnerConfig,
    vars::HintSlice,
};

#[derive(DslVariable, Clone)]
pub struct FriProofVariable<C: Config> {
    pub commit_phase_commits: Array<C, DigestVariable<C>>,
    pub query_proofs: Array<C, FriQueryProofVariable<C>>,
    pub final_poly: Array<C, Ext<C::F, C::EF>>,
    pub pow_witness: Felt<C::F>,
}

pub struct InnerFriProof(OpenVMInnerFriProof);

impl Hintable<InnerConfig> for InnerFriProof {
    type HintVariable = FriProofVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let proof_variable = OpenVMInnerFriProof::read(builder);
        let commit_phase_commits = proof_variable.commit_phase_commits;
        let query_proofs = proof_variable.query_proofs;
        let final_poly = proof_variable.final_poly;
        let pow_witness = proof_variable.pow_witness;
        Self::HintVariable {
            commit_phase_commits,
            query_proofs,
            final_poly,
            pow_witness,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::F>> {
        self.0.write()
    }
}

#[derive(DslVariable, Clone)]
pub struct FriCommitPhaseProofStepVariable<C: Config> {
    pub sibling_value: Ext<C::F, C::EF>,
    pub opening_proof: HintSlice<C>,
}

#[derive(DslVariable, Clone)]
pub struct FriChallengesVariable<C: Config> {
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
