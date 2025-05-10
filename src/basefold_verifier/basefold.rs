use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use serde::Deserialize;

use super::{mmcs::*, structs::DIMENSIONS};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, DIMENSIONS>;
pub type InnerConfig = AsmConfig<F, E>;

pub type HashDigest = MmcsCommitment;
#[derive(Deserialize)]
pub struct BasefoldCommitment {
    pub commit: HashDigest,
    pub log2_max_codeword_size: usize,
    pub trivial_commits: Vec<HashDigest>,
}

impl Hintable<InnerConfig> for BasefoldCommitment {
    type HintVariable = BasefoldCommitmentVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let commit = HashDigest::read(builder);
        let log2_max_codeword_size = Usize::Var(usize::read(builder));
        let trivial_commits = Vec::<HashDigest>::read(builder);

        BasefoldCommitmentVariable {
            commit,
            log2_max_codeword_size,
            trivial_commits,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.commit.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.log2_max_codeword_size));
        stream.extend(self.trivial_commits.write());
        stream
    }
}

pub type HashDigestVariable<C> = MmcsCommitmentVariable<C>;
#[derive(DslVariable, Clone)]
pub struct BasefoldCommitmentVariable<C: Config> {
    pub commit: HashDigestVariable<C>,
    pub log2_max_codeword_size: Usize<C::N>,
    pub trivial_commits: Array<C, HashDigestVariable<C>>,
}
