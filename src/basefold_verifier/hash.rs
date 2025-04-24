use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

pub const DIGEST_ELEMS: usize = 4;

pub struct Hash<const DIGEST_ELEMS: usize> {
    pub value: [F; DIGEST_ELEMS],
}

impl Hintable<InnerConfig> for Hash<DIGEST_ELEMS> {
    type HintVariable = HashVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let value = builder.uninit_fixed_array(DIGEST_ELEMS);
        for i in 0..DIGEST_ELEMS {
            let tmp = F::read(builder);
            builder.set(&value, i, tmp);
        }

        HashVariable {
            value,
        }
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