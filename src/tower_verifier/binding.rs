use itertools::Itertools;
use openvm_native_compiler::{
    asm::AsmConfig,
    ir::{Array, Builder, Config},
    prelude::*,
};
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use serde::{Deserialize, Serialize};

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

#[derive(DslVariable, Clone)]
pub struct IOPProverMessageVecVariable<C: Config> {
    pub prover_message_size: Var<C::N>,
    pub length: Var<C::N>,
    pub evaluations: Array<C, Ext<C::F, C::EF>>,
}

impl<C: Config> IOPProverMessageVecVariable<C> {
    pub fn get(&self, builder: &mut Builder<C>, index: Var<C::N>) -> Array<C, Ext<C::F, C::EF>> {
        let start: Var<C::N> = builder.eval(self.prover_message_size * index);
        let end: Var<C::N> = builder.eval(start + self.prover_message_size);
        self.evaluations.slice(builder, start, end)
    }

    pub fn len(&self) -> Var<C::N> {
        self.length
    }
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

/// Assume that all the prover messages have the same size.
#[derive(Debug, Deserialize)]
pub struct IOPProverMessageVec {
    pub prover_message_size: usize,
    pub data: Vec<E>,
}

impl IOPProverMessageVec {
    pub fn get(&self, index: usize) -> &[E] {
        let start = index * self.prover_message_size;
        let end = start + self.prover_message_size;
        &self.data[start..end]
    }
}

impl From<Vec<IOPProverMessage>> for IOPProverMessageVec {
    fn from(messages: Vec<IOPProverMessage>) -> Self {
        let prover_message_size = messages[0].evaluations.len();
        assert!(messages
            .iter()
            .map(|message| message.evaluations.len())
            .all_equal());
        let data = messages
            .into_iter()
            .flat_map(|msg| msg.evaluations)
            .collect();
        IOPProverMessageVec {
            prover_message_size,
            data,
        }
    }
}

impl Hintable<InnerConfig> for IOPProverMessageVec {
    type HintVariable = IOPProverMessageVecVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let prover_message_size: Var<F> = usize::read(builder);
        let length: Var<F> = usize::read(builder);
        let evaluations = Vec::<E>::read(builder);
        builder.assert_eq::<Var<F>>(evaluations.len(), prover_message_size * length);
        IOPProverMessageVecVariable {
            prover_message_size,
            length,
            evaluations,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.prover_message_size,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &if self.data.len() == 0 {
                0
            } else {
                self.data.len() / self.prover_message_size
            },
        ));
        stream.extend(self.data.write());
        stream
    }
}

pub struct TowerVerifierInput {
    pub prod_out_evals: Vec<Vec<E>>,
    pub logup_out_evals: Vec<Vec<E>>,
    pub num_variables: Vec<usize>,
    pub num_fanin: usize,

    // TowerProof
    pub num_proofs: usize,
    pub num_prod_specs: usize,
    pub num_logup_specs: usize,
    pub _max_num_variables: usize,

    pub proofs: Vec<Vec<IOPProverMessage>>,
    pub prod_specs_eval: Vec<Vec<Vec<E>>>,
    pub logup_specs_eval: Vec<Vec<Vec<E>>>,
}
