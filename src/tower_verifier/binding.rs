use openvm_native_compiler::{
    asm::AsmConfig,
    ir::{Array, Builder, Config},
    prelude::*,
};
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

use openvm_stark_sdk::p3_baby_bear::BabyBear;
use openvm_stark_backend::p3_field::extension::BinomialExtensionField;
use serde::Deserialize;

#[derive(DslVariable, Clone)]
pub struct PointVariable<C: Config> {
    pub fs: Array<C, Ext<C::F, C::EF>>,
}

#[derive(DslVariable, Clone)]
pub struct PointAndEvalVariable<C: Config> {
    pub point: PointVariable<C>,
    pub eval: Ext<C::F, C::EF>,
}

#[derive(DslVariable, Clone)]
pub struct IOPProverMessageVariable<C: Config> {
    pub evaluations: Array<C, Ext<C::F, C::EF>>,
}

#[derive(Clone, Deserialize)]
pub struct Point {
    pub fs: Vec<E>,
}
impl Hintable<InnerConfig> for Point {
    type HintVariable = PointVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        PointVariable {
            fs: builder.hint_exts(),
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.fs.write());
        stream
    }
}
impl VecAutoHintable for Point {}

pub struct PointAndEval {
    pub point: Point,
    pub eval: E,
}
impl Hintable<InnerConfig> for PointAndEval {
    type HintVariable = PointAndEvalVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let point = Point::read(builder);
        let eval = E::read(builder);
        PointAndEvalVariable { point, eval }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.point.write());
        stream.extend(self.eval.write());
        stream
    }
}
impl VecAutoHintable for PointAndEval {}

#[derive(Debug, Deserialize)]
pub struct IOPProverMessage {
    pub evaluations: Vec<E>,
}

use ceno_sumcheck::structs::IOPProverMessage as InnerIOPProverMessage;
impl From<InnerIOPProverMessage<E>> for IOPProverMessage {
    fn from(value: InnerIOPProverMessage<E>) -> Self {
        IOPProverMessage {
            evaluations: value.evaluations,
        }
    }
}

impl Hintable<InnerConfig> for IOPProverMessage {
    type HintVariable = IOPProverMessageVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        IOPProverMessageVariable {
            evaluations: builder.hint_exts(),
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.evaluations.write());
        stream
    }
}
impl VecAutoHintable for IOPProverMessage {}