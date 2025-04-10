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
    pub raw_pi: Vec<Vec<F>>,
    // Evaluation of raw_pi.
    pub pi_evals: Vec<E>,
    pub opcode_proofs: Vec<ZKVMOpcodeProofInput>,
    pub table_proofs: Vec<ZKVMTableProofInput>,

    // VKs for opcode and table circuits
    pub circuit_vks_fixed_commits: Vec<BasefoldCommitment<BabyBearExt4>>,
}

#[derive(Default, Debug)]
pub struct TowerProofInput {
    pub num_proofs: usize,
    pub proofs: Vec<Vec<IOPProverMessage>>,
    // specs -> layers -> evals
    pub num_prod_specs: usize,
    pub prod_specs_eval: Vec<Vec<Vec<E>>>,
    // specs -> layers -> evals
    pub num_logup_specs: usize,
    pub logup_specs_eval: Vec<Vec<Vec<E>>>,
}

#[derive(Default, Debug)]
pub struct ZKVMOpcodeProofInput {
    pub idx: usize,
    pub num_instances: usize,

    // product constraints
    pub record_r_out_evals: Vec<E>,
    pub record_w_out_evals: Vec<E>,
    
    // logup sum at layer 1
    pub lk_p1_out_eval: E,
    pub lk_p2_out_eval: E,
    pub lk_q1_out_eval: E,
    pub lk_q2_out_eval: E,

    pub tower_proof: TowerProofInput,

    // main constraint and select sumcheck proof
    pub main_sel_sumcheck_proofs: Vec<IOPProverMessage>,
    pub r_records_in_evals: Vec<E>,
    pub w_records_in_evals: Vec<E>,
    pub lk_records_in_evals: Vec<E>,

    pub wits_commit: BasefoldCommitment<BabyBearExt4>,
    // TODO: PCS
    // pub wits_opening_proof: PCS::Proof,
    pub wits_in_evals: Vec<E>,
}

#[derive(Default, Debug)]
pub struct ZKVMTableProofInput {
    pub idx: usize,

    // tower evaluation at layer 1
    pub r_out_evals: Vec<E>, // Vec<[E; 2]>
    pub w_out_evals: Vec<E>, // Vec<[E; 2]>
    pub lk_out_evals: Vec<E>, // Vec<[E; 4]>

    pub has_same_r_sumcheck_proofs: usize,
    pub same_r_sumcheck_proofs: Vec<IOPProverMessage>, // Could be empty
    pub rw_in_evals: Vec<E>,
    pub lk_in_evals: Vec<E>,

    pub tower_proof: TowerProofInput,

    // num_vars hint for rw dynamic address to work
    pub rw_hints_num_vars: Vec<usize>,

    pub fixed_in_evals: Vec<E>,
    // TODO: PCS
    // pub fixed_opening_proof: Option<PCS::Proof>,
    pub wits_commit: BasefoldCommitment<BabyBearExt4>,
    pub wits_in_evals: Vec<E>,
    // TODO: PCS
    // pub wits_opening_proof: PCS::Proof,
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
        stream.extend(<usize as Hintable<InnerConfig>>::write(&0usize));
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





