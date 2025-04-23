use openvm_native_compiler::{asm::AsmConfig, ir::*};
use openvm_native_compiler_derive::DslVariable;
use openvm_native_recursion::hints::Hintable;
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

#[derive(DslVariable, Clone)]
pub struct CircuitIndexMetaVariable<C: Config> {
    pub witin_num_vars: Usize<C::N>,
    pub witin_num_polys: Usize<C::N>,
    pub fixed_num_vars: Usize<C::N>,
    pub fixed_num_polys: Usize<C::N>,
}

pub struct CircuitIndexMeta {
    pub witin_num_vars: usize,
    pub witin_num_polys: usize,
    pub fixed_num_vars: usize,
    pub fixed_num_polys: usize,
}

impl Hintable<InnerConfig> for CircuitIndexMeta {
    type HintVariable = CircuitIndexMetaVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let witin_num_vars = Usize::Var(usize::read(builder));
        let witin_num_polys = Usize::Var(usize::read(builder));
        let fixed_num_vars = Usize::Var(usize::read(builder));
        let fixed_num_polys = Usize::Var(usize::read(builder));

        CircuitIndexMetaVariable {
            witin_num_vars,
            witin_num_polys,
            fixed_num_vars,
            fixed_num_polys,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
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

#[derive(DslVariable, Clone)]
pub struct DimensionsVariable<C: Config> {
    pub width: Var<C::N>,
    pub height: Var<C::N>,
}

pub struct Dimensions {
    pub width: usize,
    pub height: usize,
}

impl Hintable<InnerConfig> for Dimensions {
    type HintVariable = DimensionsVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let width = usize::read(builder);
        let height = usize::read(builder);

        DimensionsVariable { width, height }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.width));
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.height));
        stream
    }
}
