use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::FieldAlgebra;
use serde::Deserialize;

use super::structs::DIMENSIONS;

pub const DIGEST_ELEMS: usize = 8;

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, DIMENSIONS>;
pub type InnerConfig = AsmConfig<F, E>;

#[derive(Deserialize)]
pub struct Hash {
    pub value: [F; DIGEST_ELEMS],
}

impl Default for Hash {
    fn default() -> Self {
        Hash {
            value: [F::ZERO; DIGEST_ELEMS],
        }
    }
}

impl From<p3_symmetric::Hash<F, F, DIGEST_ELEMS>> for Hash {
    fn from(hash: p3_symmetric::Hash<F, F, DIGEST_ELEMS>) -> Self {
        Hash { value: hash.into() }
    }
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

pub fn hash_iter_slices<C: Config>(
    builder: &mut Builder<C>,
    // _hash: HashVariable<C>,
    _values: Array<C, Array<C, Felt<C::F>>>,
) -> Array<C, Felt<C::F>> {
    // XXX: verify hash
    builder.hint_felts_fixed(DIGEST_ELEMS)
}

pub fn compress<C: Config>(
    builder: &mut Builder<C>,
    // _hash: HashVariable<C>,
    _values: Array<C, Array<C, Felt<C::F>>>,
) -> Array<C, Felt<C::F>> {
    // XXX: verify hash
    builder.hint_felts_fixed(DIGEST_ELEMS)
}

#[cfg(test)]
mod tests {
    use openvm_native_compiler::asm::AsmBuilder;
    use openvm_native_compiler_derive::iter_zip;
    use openvm_stark_backend::config::StarkGenericConfig;
    use openvm_stark_sdk::config::baby_bear_poseidon2::BabyBearPoseidon2Config;
    type SC = BabyBearPoseidon2Config;
    type F = BabyBear;
    type E = BinomialExtensionField<F, 4>;
    type EF = <SC as StarkGenericConfig>::Challenge;

    use crate::basefold_verifier::basefold::HashDigest;

    use super::*;
    #[test]
    fn test_read_to_hash_variable() {
        let mut builder = AsmBuilder::<F, EF>::default();

        let hint = HashDigest::read(&mut builder);
        let dst: HashVariable<_> = builder.uninit();
        builder.assign(&dst, hint);
    }
}
