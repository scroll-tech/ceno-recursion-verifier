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

#[derive(DslVariable, Clone)]
pub struct HashVariable<C: Config> {
    pub value: Array<C, Felt<C::F>>,
}

impl VecAutoHintable for Hash {}

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

#[cfg(test)]
mod tests {
    use openvm_circuit::arch::{SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::AsmBuilder;
    type F = BabyBear;
    type E = BinomialExtensionField<F, 4>;

    use crate::basefold_verifier::basefold::HashDigest;

    use super::*;
    #[test]
    fn test_read_to_hash_variable() {
        // simple test program
        let mut builder = AsmBuilder::<F, E>::default();
        let _digest = HashDigest::read(&mut builder);
        builder.halt();

        // configure the VM executor
        let system_config = SystemConfig::default().with_max_segment_len(1 << 20);
        let config = NativeConfig::new(system_config, Native);
        let executor = VmExecutor::new(config);

        // prepare input
        let mut input = Vec::new();
        input.extend(Hash::default().write());

        // execute the program
        let program = builder.compile_isa();
        executor.execute(program, input).unwrap();
    }
}
