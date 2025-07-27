use crate::arithmetics::next_pow2_instance_padding;
use crate::basefold_verifier::basefold::{BasefoldProof, BasefoldProofVariable};
use crate::basefold_verifier::query_phase::{
    QueryPhaseVerifierInput, QueryPhaseVerifierInputVariable,
};
use crate::{
    arithmetics::ceil_log2,
    tower_verifier::binding::{IOPProverMessage, IOPProverMessageVariable},
};
use ark_std::iterable::Iterable;
use ff_ext::BabyBearExt4;
use mpcs::BasefoldCommitment;
use openvm_native_compiler::{
    asm::AsmConfig,
    ir::{Array, Builder, Config, Felt},
    prelude::*,
};
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::{extension::BinomialExtensionField, FieldAlgebra};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

#[derive(DslVariable, Clone)]
pub struct ZKVMProofInputVariable<C: Config> {
    pub raw_pi: Array<C, Array<C, Felt<C::F>>>,
    pub raw_pi_num_variables: Array<C, Var<C::N>>,
    pub pi_evals: Array<C, Ext<C::F, C::EF>>,
    pub chip_proofs: Array<C, ZKVMChipProofInputVariable<C>>,

    pub witin_commit: Array<C, Felt<C::F>>,
    pub witin_commit_log2_max_codeword_size: Felt<C::F>,
    pub pcs_proof: BasefoldProofVariable<C>,
}

#[derive(DslVariable, Clone)]
pub struct TowerProofInputVariable<C: Config> {
    pub num_proofs: Usize<C::N>,
    pub proofs: Array<C, Array<C, IOPProverMessageVariable<C>>>,
    pub num_prod_specs: Usize<C::N>,
    pub prod_specs_eval: Array<C, Array<C, Array<C, Ext<C::F, C::EF>>>>,
    pub num_logup_specs: Usize<C::N>,
    pub logup_specs_eval: Array<C, Array<C, Array<C, Ext<C::F, C::EF>>>>,
}

#[derive(DslVariable, Clone)]
pub struct ZKVMChipProofInputVariable<C: Config> {
    pub idx: Usize<C::N>,
    pub idx_felt: Felt<C::F>,
    pub num_instances: Usize<C::N>,
    pub num_instances_minus_one_bit_decomposition: Array<C, Felt<C::F>>,
    pub log2_num_instances: Usize<C::N>,

    pub record_r_out_evals_len: Usize<C::N>,
    pub record_w_out_evals_len: Usize<C::N>,
    pub record_lk_out_evals_len: Usize<C::N>,

    pub record_r_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>>,
    pub record_w_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>>,
    pub record_lk_out_evals: Array<C, Array<C, Ext<C::F, C::EF>>>,

    pub tower_proof: TowerProofInputVariable<C>,

    pub main_sel_sumcheck_proofs: Array<C, IOPProverMessageVariable<C>>,
    pub wits_in_evals: Array<C, Ext<C::F, C::EF>>,
    pub fixed_in_evals: Array<C, Ext<C::F, C::EF>>,
}

pub(crate) struct ZKVMProofInput {
    pub raw_pi: Vec<Vec<F>>,
    // Evaluation of raw_pi.
    pub pi_evals: Vec<E>,
    pub chip_proofs: Vec<ZKVMChipProofInput>,
    pub witin_commit: BasefoldCommitment<BabyBearExt4>,
    pub pcs_proof: BasefoldProof,
}

impl Hintable<InnerConfig> for ZKVMProofInput {
    type HintVariable = ZKVMProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let raw_pi = Vec::<Vec<F>>::read(builder);
        let raw_pi_num_variables = Vec::<usize>::read(builder);
        let pi_evals = Vec::<E>::read(builder);
        let chip_proofs = Vec::<ZKVMChipProofInput>::read(builder);
        let witin_commit = Vec::<F>::read(builder);
        let witin_commit_log2_max_codeword_size = F::read(builder);
        let pcs_proof = BasefoldProof::read(builder);

        ZKVMProofInputVariable {
            raw_pi,
            raw_pi_num_variables,
            pi_evals,
            chip_proofs,
            witin_commit,
            witin_commit_log2_max_codeword_size,
            pcs_proof,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.raw_pi.write());

        let mut raw_pi_num_variables: Vec<usize> = vec![];
        for v in &self.raw_pi {
            raw_pi_num_variables.push(ceil_log2(v.len().next_power_of_two()));
        }
        stream.extend(raw_pi_num_variables.write());

        stream.extend(self.pi_evals.write());
        stream.extend(self.chip_proofs.write());

        // Write in witin_commit
        let mut cmt_vec: Vec<F> = vec![];
        self.witin_commit.commit().iter().for_each(|x| {
            // let f: F = serde_json::from_value(serde_json::to_value(&x).unwrap()).unwrap();
            cmt_vec.push(x);
        });
        let witin_commit_log2_max_codeword_size =
            F::from_canonical_u32(self.witin_commit.log2_max_codeword_size as u32);
        stream.extend(cmt_vec.write());
        stream.extend(witin_commit_log2_max_codeword_size.write());
        stream.extend(self.pcs_proof.write());

        stream
    }
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

impl Hintable<InnerConfig> for TowerProofInput {
    type HintVariable = TowerProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let num_proofs = Usize::Var(usize::read(builder));
        let proofs = builder.dyn_array(num_proofs.clone());
        iter_zip!(builder, proofs).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            let proof = Vec::<IOPProverMessage>::read(builder);
            builder.iter_ptr_set(&proofs, ptr, proof);
        });

        let num_prod_specs = Usize::Var(usize::read(builder));
        let prod_specs_eval = builder.dyn_array(num_prod_specs.clone());
        iter_zip!(builder, prod_specs_eval).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            let evals = Vec::<Vec<E>>::read(builder);
            builder.iter_ptr_set(&prod_specs_eval, ptr, evals);
        });

        let num_logup_specs = Usize::Var(usize::read(builder));
        let logup_specs_eval = builder.dyn_array(num_logup_specs.clone());
        iter_zip!(builder, logup_specs_eval).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            let evals = Vec::<Vec<E>>::read(builder);
            builder.iter_ptr_set(&logup_specs_eval, ptr, evals);
        });

        TowerProofInputVariable {
            num_proofs,
            proofs,
            num_prod_specs,
            prod_specs_eval,
            num_logup_specs,
            logup_specs_eval,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.num_proofs));
        for p in &self.proofs {
            stream.extend(p.write());
        }
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.num_prod_specs,
        ));
        for evals in &self.prod_specs_eval {
            stream.extend(evals.write());
        }
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.num_logup_specs,
        ));
        for evals in &self.logup_specs_eval {
            stream.extend(evals.write());
        }
        stream
    }
}

pub struct ZKVMChipProofInput {
    pub idx: usize,
    pub num_instances: usize,

    // product constraints
    pub record_r_out_evals_len: usize,
    pub record_w_out_evals_len: usize,
    pub record_lk_out_evals_len: usize,
    pub record_r_out_evals: Vec<Vec<E>>,
    pub record_w_out_evals: Vec<Vec<E>>,
    pub record_lk_out_evals: Vec<Vec<E>>,

    pub tower_proof: TowerProofInput,

    // main constraint and select sumcheck proof
    pub main_sumcheck_proofs: Vec<IOPProverMessage>,
    pub wits_in_evals: Vec<E>,
    pub fixed_in_evals: Vec<E>,
}

impl VecAutoHintable for ZKVMChipProofInput {}

impl Hintable<InnerConfig> for ZKVMChipProofInput {
    type HintVariable = ZKVMChipProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let idx = Usize::Var(usize::read(builder));
        let idx_felt = F::read(builder);
        let num_instances = Usize::Var(usize::read(builder));
        let num_instances_minus_one_bit_decomposition = Vec::<F>::read(builder);
        let log2_num_instances = Usize::Var(usize::read(builder));

        let record_r_out_evals_len = Usize::Var(usize::read(builder));
        let record_w_out_evals_len = Usize::Var(usize::read(builder));
        let record_lk_out_evals_len = Usize::Var(usize::read(builder));

        let record_r_out_evals = Vec::<Vec<E>>::read(builder);
        let record_w_out_evals = Vec::<Vec<E>>::read(builder);
        let record_lk_out_evals = Vec::<Vec<E>>::read(builder);

        let tower_proof = TowerProofInput::read(builder);
        let main_sel_sumcheck_proofs = Vec::<IOPProverMessage>::read(builder);
        let wits_in_evals = Vec::<E>::read(builder);
        let fixed_in_evals = Vec::<E>::read(builder);

        ZKVMChipProofInputVariable {
            idx,
            idx_felt,
            num_instances,
            num_instances_minus_one_bit_decomposition,
            log2_num_instances,
            record_r_out_evals_len,
            record_w_out_evals_len,
            record_lk_out_evals_len,
            record_r_out_evals,
            record_w_out_evals,
            record_lk_out_evals,
            tower_proof,
            main_sel_sumcheck_proofs,
            wits_in_evals,
            fixed_in_evals,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.idx));

        let idx_u32: F = F::from_canonical_u32(self.idx as u32);
        stream.extend(idx_u32.write());

        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.num_instances));

        let eq_instance = self.num_instances - 1;
        let mut bit_decomp: Vec<F> = vec![];
        for i in 0..32usize {
            bit_decomp.push(F::from_canonical_usize((eq_instance >> i) & 1));
        }
        stream.extend(bit_decomp.write());

        let next_pow2_instance = next_pow2_instance_padding(self.num_instances);
        let log2_num_instances = ceil_log2(next_pow2_instance);
        stream.extend(<usize as Hintable<InnerConfig>>::write(&log2_num_instances));

        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.record_r_out_evals_len,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.record_w_out_evals_len,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.record_lk_out_evals_len,
        ));

        stream.extend(self.record_r_out_evals.write());
        stream.extend(self.record_w_out_evals.write());
        stream.extend(self.record_lk_out_evals.write());

        stream.extend(self.tower_proof.write());
        stream.extend(self.main_sumcheck_proofs.write());
        stream.extend(self.wits_in_evals.write());
        stream.extend(self.fixed_in_evals.write());

        stream
    }
}
