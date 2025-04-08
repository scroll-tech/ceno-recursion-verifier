use openvm_native_compiler::{
    asm::AsmConfig,
    ir::{Array, Builder, Config, Felt},
    prelude::*,
};
use crate::tower_verifier::binding::IOPProverMessage;
use mpcs::{Basefold, BasefoldCommitment, BasefoldRSParams};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use ff_ext::BabyBearExt4;
use openvm_native_recursion::hints::Hintable;

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

#[derive(DslVariable, Clone)]
pub struct ZKVMProofInputVariable<C: Config> {
    pub phantom: Usize<C::N>,
}

#[derive(Default, Debug)]
pub(crate) struct ZKVMProofInput {
    pub phantom: usize,

    // raw_pi: Vec<Vec<F>>,

    // circuit_vks_fixed_commits: Vec<BasefoldCommitment<BabyBearExt4>>,
    // opcode_proof_commits: Vec<BasefoldCommitment<BabyBearExt4>>,
    // table_proof_commits: Vec<BasefoldCommitment<BabyBearExt4>>,

    // pub prod_out_evals: Vec<Vec<E>>,
    // pub logup_out_evals: Vec<Vec<E>>,
    // pub num_variables: Vec<usize>,
    // pub num_fanin: usize,

    // // TowerProof
    // pub num_proofs: usize,
    // pub num_prod_specs: usize,
    // pub num_logup_specs: usize,
    // pub max_num_variables: usize,

    // proofs: Vec<Vec<IOPProverMessage>>,
    // prod_specs_eval: Vec<Vec<Vec<E>>>,
    // logup_specs_eval: Vec<Vec<Vec<E>>>,
}

impl Hintable<InnerConfig> for ZKVMProofInput {
    type HintVariable = ZKVMProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        // let prod_out_evals = Vec::<Vec<E>>::read(builder);
        // let logup_out_evals = Vec::<Vec<E>>::read(builder);
        // let num_variables = Vec::<usize>::read(builder);
        // let num_fanin = Usize::Var(usize::read(builder));
        let phantom = Usize::Var(usize::read(builder));
        // let num_prod_specs = Usize::Var(usize::read(builder));
        // let num_logup_specs = Usize::Var(usize::read(builder));
        // let max_num_variables = Usize::Var(usize::read(builder));

        // let proofs = builder.dyn_array(num_proofs.clone());
        // let prod_specs_eval = builder.dyn_array(num_prod_specs.clone());
        // let logup_specs_eval = builder.dyn_array(num_logup_specs.clone());

        // iter_zip!(builder, proofs).for_each(|idx_vec, builder| {
        //     let ptr = idx_vec[0];
        //     let proof = Vec::<IOPProverMessage>::read(builder);
        //     builder.iter_ptr_set(&proofs, ptr, proof);
        // });

        // iter_zip!(builder, prod_specs_eval).for_each(|idx_vec, builder| {
        //     let ptr = idx_vec[0];
        //     let evals = Vec::<Vec<E>>::read(builder);
        //     builder.iter_ptr_set(&prod_specs_eval, ptr, evals);
        // });

        // iter_zip!(builder, logup_specs_eval).for_each(|idx_vec, builder| {
        //     let ptr = idx_vec[0];
        //     let evals = Vec::<Vec<E>>::read(builder);
        //     builder.iter_ptr_set(&logup_specs_eval, ptr, evals);
        // });

        ZKVMProofInputVariable {
            phantom,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        // stream.extend(self.prod_out_evals.write());
        // stream.extend(self.logup_out_evals.write());
        // stream.extend(self.num_variables.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.phantom));
        // stream.extend(<usize as Hintable<InnerConfig>>::write(&self.num_proofs));
        // stream.extend(<usize as Hintable<InnerConfig>>::write(
        //     &self.num_prod_specs,
        // ));
        // stream.extend(<usize as Hintable<InnerConfig>>::write(
        //     &self.num_logup_specs,
        // ));

        // let max_num_variables = self.num_variables.iter().max().unwrap().clone();
        // stream.extend(<usize as Hintable<InnerConfig>>::write(&max_num_variables));

        // for p in &self.proofs {
        //     stream.extend(p.write());
        // }
        // for evals in &self.prod_specs_eval {
        //     stream.extend(evals.write());
        // }
        // for evals in &self.logup_specs_eval {
        //     stream.extend(evals.write());
        // }

        stream
    }
}