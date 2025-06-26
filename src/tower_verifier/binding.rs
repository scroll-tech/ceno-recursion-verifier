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

#[derive(DslVariable, Clone)]
pub struct TowerVerifierInputVariable<C: Config> {
    pub prod_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>>,
    pub logup_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>>,
    pub num_variables: Array<C, Usize<C::N>>,
    pub num_fanin: Usize<C::N>,

    // TowerProofVariable
    pub num_proofs: Usize<C::N>,
    pub num_prod_specs: Usize<C::N>,
    pub num_logup_specs: Usize<C::N>,
    pub max_num_variables: Usize<C::N>,

    pub proofs: Array<C, Array<C, IOPProverMessageVariable<C>>>,
    pub prod_specs_eval: Array<C, Array<C, Array<C, Ext<C::F, C::EF>>>>,
    pub logup_specs_eval: Array<C, Array<C, Array<C, Ext<C::F, C::EF>>>>,
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

impl Hintable<InnerConfig> for TowerVerifierInput {
    type HintVariable = TowerVerifierInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let prod_out_evals = Vec::<Vec<E>>::read(builder);
        let logup_out_evals = Vec::<Vec<E>>::read(builder);
        let num_variables_var = Vec::<usize>::read(builder);
        let num_variables = builder.dyn_array(num_variables_var.len());
        iter_zip!(builder, num_variables_var, num_variables).for_each(|ptr_vec, builder| {
            let v = builder.iter_ptr_get(&num_variables_var, ptr_vec[0]);
            let v_usize: Usize<<InnerConfig as Config>::N> = Usize::from(v);
            builder.iter_ptr_set(&num_variables, ptr_vec[1], v_usize);
        });

        let num_fanin = Usize::Var(usize::read(builder));
        let num_proofs = Usize::Var(usize::read(builder));
        let num_prod_specs = Usize::Var(usize::read(builder));
        let num_logup_specs = Usize::Var(usize::read(builder));
        let max_num_variables = Usize::Var(usize::read(builder));

        let proofs = builder.dyn_array(num_proofs.clone());
        let prod_specs_eval = builder.dyn_array(num_prod_specs.clone());
        let logup_specs_eval = builder.dyn_array(num_logup_specs.clone());

        iter_zip!(builder, proofs).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            let proof = Vec::<IOPProverMessage>::read(builder);
            builder.iter_ptr_set(&proofs, ptr, proof);
        });

        iter_zip!(builder, prod_specs_eval).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            let evals = Vec::<Vec<E>>::read(builder);
            builder.iter_ptr_set(&prod_specs_eval, ptr, evals);
        });

        iter_zip!(builder, logup_specs_eval).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            let evals = Vec::<Vec<E>>::read(builder);
            builder.iter_ptr_set(&logup_specs_eval, ptr, evals);
        });

        TowerVerifierInputVariable {
            prod_out_evals,
            logup_out_evals,
            num_variables,
            num_fanin,
            num_proofs,
            num_prod_specs,
            num_logup_specs,
            max_num_variables,
            proofs,
            prod_specs_eval,
            logup_specs_eval,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.prod_out_evals.write());
        stream.extend(self.logup_out_evals.write());
        stream.extend(self.num_variables.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.num_fanin));
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.num_proofs));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.num_prod_specs,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.num_logup_specs,
        ));

        let max_num_variables = self.num_variables.iter().max().unwrap().clone();
        stream.extend(<usize as Hintable<InnerConfig>>::write(&max_num_variables));

        for p in &self.proofs {
            stream.extend(p.write());
        }
        for evals in &self.prod_specs_eval {
            stream.extend(evals.write());
        }
        for evals in &self.logup_specs_eval {
            stream.extend(evals.write());
        }

        stream
    }
}
