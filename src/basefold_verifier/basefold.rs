use mpcs::basefold::BasefoldProof as InnerBasefoldProof;
use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use serde::Deserialize;

use crate::{
    basefold_verifier::{
        hash::{Hash, HashVariable},
        query_phase::{
            PointAndEvals, PointAndEvalsVariable, QueryOpeningProofs, QueryOpeningProofsVariable,
        },
    },
    tower_verifier::binding::{IOPProverMessage, IOPProverMessageVariable},
};

use super::{mmcs::*, structs::DIMENSIONS};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, DIMENSIONS>;
pub type InnerConfig = AsmConfig<F, E>;

pub type HashDigest = MmcsCommitment;
#[derive(Deserialize)]
pub struct BasefoldCommitment {
    pub commit: HashDigest,
    pub log2_max_codeword_size: usize,
}

use mpcs::BasefoldCommitment as InnerBasefoldCommitment;

impl From<InnerBasefoldCommitment<E>> for BasefoldCommitment {
    fn from(value: InnerBasefoldCommitment<E>) -> Self {
        Self {
            commit: Hash {
                value: value.commit().into(),
            },
            log2_max_codeword_size: value.log2_max_codeword_size,
        }
    }
}

impl Hintable<InnerConfig> for BasefoldCommitment {
    type HintVariable = BasefoldCommitmentVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let commit = HashDigest::read(builder);
        let log2_max_codeword_size = Usize::Var(usize::read(builder));
        // let trivial_commits = Vec::<HashDigest>::read(builder);

        BasefoldCommitmentVariable {
            commit,
            log2_max_codeword_size,
            // trivial_commits,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.commit.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.log2_max_codeword_size,
        ));
        // stream.extend(self.trivial_commits.write());
        stream
    }
}

pub type HashDigestVariable<C> = MmcsCommitmentVariable<C>;
#[derive(DslVariable, Clone)]
pub struct BasefoldCommitmentVariable<C: Config> {
    pub commit: HashDigestVariable<C>,
    pub log2_max_codeword_size: Usize<C::N>,
    // pub trivial_commits: Array<C, HashDigestVariable<C>>,
}

#[derive(Deserialize)]
pub struct BasefoldProof {
    pub commits: Vec<Hash>,
    pub final_message: Vec<Vec<E>>,
    pub query_opening_proof: QueryOpeningProofs,
    pub sumcheck_proof: Vec<IOPProverMessage>,
}

#[derive(DslVariable, Clone)]
pub struct BasefoldProofVariable<C: Config> {
    pub commits: Array<C, HashVariable<C>>,
    pub final_message: Array<C, Array<C, Ext<C::F, C::EF>>>,
    pub query_opening_proof: QueryOpeningProofsVariable<C>,
    pub sumcheck_proof: Array<C, IOPProverMessageVariable<C>>,
}

impl Hintable<InnerConfig> for BasefoldProof {
    type HintVariable = BasefoldProofVariable<InnerConfig>;
    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let commits = Vec::<Hash>::read(builder);
        let final_message = Vec::<Vec<E>>::read(builder);
        let query_opening_proof = QueryOpeningProofs::read(builder);
        let sumcheck_proof = Vec::<IOPProverMessage>::read(builder);
        BasefoldProofVariable {
            commits,
            final_message,
            query_opening_proof,
            sumcheck_proof,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.commits.write());
        stream.extend(self.final_message.write());
        stream.extend(self.query_opening_proof.write());
        stream.extend(self.sumcheck_proof.write());
        stream
    }
}

impl From<InnerBasefoldProof<E>> for BasefoldProof {
    fn from(proof: InnerBasefoldProof<E>) -> Self {
        BasefoldProof {
            commits: proof.commits.iter().map(|c| c.clone().into()).collect(),
            final_message: proof.final_message.into(),
            query_opening_proof: proof
                .query_opening_proof
                .iter()
                .map(|proof| proof.clone().into())
                .collect(),
            sumcheck_proof: proof.sumcheck_proof.map_or(vec![], |proof| {
                proof.into_iter().map(|proof| proof.into()).collect()
            }),
        }
    }
}

#[derive(Deserialize)]
pub struct RoundOpening {
    pub num_var: usize,
    pub point_and_evals: PointAndEvals,
}

#[derive(DslVariable, Clone)]
pub struct RoundOpeningVariable<C: Config> {
    pub num_var: Var<C::N>,
    pub point_and_evals: PointAndEvalsVariable<C>,
}

impl Hintable<InnerConfig> for RoundOpening {
    type HintVariable = RoundOpeningVariable<InnerConfig>;
    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let num_var = usize::read(builder);
        let point_and_evals = PointAndEvals::read(builder);
        RoundOpeningVariable {
            num_var,
            point_and_evals,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = vec![];
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.num_var));
        stream.extend(self.point_and_evals.write());
        stream
    }
}

impl VecAutoHintable for RoundOpening {}

#[derive(Deserialize)]
pub struct Round {
    pub commit: BasefoldCommitment,
    pub openings: Vec<RoundOpening>,
}

#[derive(DslVariable, Clone)]
pub struct RoundVariable<C: Config> {
    pub commit: BasefoldCommitmentVariable<C>,
    pub openings: Array<C, RoundOpeningVariable<C>>,
}

impl Hintable<InnerConfig> for Round {
    type HintVariable = RoundVariable<InnerConfig>;
    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let commit = BasefoldCommitment::read(builder);
        let openings = Vec::<RoundOpening>::read(builder);
        RoundVariable { commit, openings }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = vec![];
        stream.extend(self.commit.write());
        stream.extend(self.openings.write());
        stream
    }
}

impl VecAutoHintable for Round {}
