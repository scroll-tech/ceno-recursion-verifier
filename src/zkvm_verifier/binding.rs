use crate::{arithmetics::ceil_log2, tower_verifier::binding::{IOPProverMessage, IOPProverMessageVariable}};
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
use crate::arithmetics::next_pow2_instance_padding;

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

#[derive(DslVariable, Clone)]
pub struct ZKVMProofInputVariable<C: Config> {
    pub raw_pi: Array<C, Array<C, Felt<C::F>>>,
    pub raw_pi_num_variables: Array<C, Var<C::N>>,
    pub pi_evals: Array<C, Ext<C::F, C::EF>>,
    pub opcode_proofs: Array<C, ZKVMOpcodeProofInputVariable<C>>,
    pub table_proofs: Array<C, ZKVMTableProofInputVariable<C>>,
    pub circuit_vks_fixed_commits: Array<C, Array<C, Felt<C::F>>>,
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
pub struct ZKVMOpcodeProofInputVariable<C: Config> {
    pub idx: Usize<C::N>,
    pub idx_felt: Felt<C::F>,
    pub num_instances: Usize<C::N>,
    pub num_instances_minus_one_bit_decomposition: Array<C, Felt<C::F>>,
    pub log2_num_instances: Usize<C::N>,

    pub record_r_out_evals: Array<C, Ext<C::F, C::EF>>,
    pub record_w_out_evals: Array<C, Ext<C::F, C::EF>>,

    pub lk_p1_out_eval: Ext<C::F, C::EF>,
    pub lk_p2_out_eval: Ext<C::F, C::EF>,
    pub lk_q1_out_eval: Ext<C::F, C::EF>,
    pub lk_q2_out_eval: Ext<C::F, C::EF>,

    pub tower_proof: TowerProofInputVariable<C>,

    pub main_sel_sumcheck_proofs: Array<C, IOPProverMessageVariable<C>>,
    pub r_records_in_evals: Array<C, Ext<C::F, C::EF>>,
    pub w_records_in_evals: Array<C, Ext<C::F, C::EF>>,
    pub lk_records_in_evals: Array<C, Ext<C::F, C::EF>>,

    pub wits_commit: Array<C, Felt<C::F>>, // LEN = DIGEST_WIDTH, TODO: SPEC
    pub wits_in_evals: Array<C, Ext<C::F, C::EF>>,
}

#[derive(DslVariable, Clone)]
pub struct ZKVMTableProofInputVariable<C: Config> {
    pub idx: Usize<C::N>,
    pub idx_felt: Felt<C::F>,

    pub r_out_evals: Array<C, Ext<C::F, C::EF>>,    // Vec<[E; 2]>,
    pub w_out_evals: Array<C, Ext<C::F, C::EF>>,    // Vec<[E; 2]>,
    pub compressed_rw_out_len: Usize<C::N>,
    pub lk_out_evals: Array<C, Ext<C::F, C::EF>>,   // Vec<[E; 4]>,
    pub compressed_lk_out_len: Usize<C::N>,

    pub has_same_r_sumcheck_proofs: Usize<C::N>, // Either 1 or 0
    pub same_r_sumcheck_proofs: Array<C, IOPProverMessageVariable<C>>, // Could be empty
    pub rw_in_evals: Array<C, Ext<C::F, C::EF>>,
    pub lk_in_evals: Array<C, Ext<C::F, C::EF>>,

    pub tower_proof: TowerProofInputVariable<C>,
    pub rw_hints_num_vars: Array<C, Var<C::N>>,
    pub fixed_in_evals: Array<C, Ext<C::F, C::EF>>,
    pub wits_commit: Array<C, Felt<C::F>>, // LEN = DIGEST_WIDTH, TODO: SPEC
    pub wits_in_evals: Array<C, Ext<C::F, C::EF>>,
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
impl Hintable<InnerConfig> for ZKVMProofInput {
    type HintVariable = ZKVMProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let raw_pi = Vec::<Vec<F>>::read(builder);
        let raw_pi_num_variables = Vec::<usize>::read(builder);
        let pi_evals = Vec::<E>::read(builder);
        let opcode_proofs = Vec::<ZKVMOpcodeProofInput>::read(builder);
        let table_proofs = Vec::<ZKVMTableProofInput>::read(builder);
        let circuit_vks_fixed_commits = Vec::<Vec<F>>::read(builder);

        ZKVMProofInputVariable {
            raw_pi,
            raw_pi_num_variables,
            pi_evals,
            opcode_proofs,
            table_proofs,
            circuit_vks_fixed_commits,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.raw_pi.write());

        let mut raw_pi_num_variables: Vec<usize> = vec![];
        for v in &self.raw_pi {
            raw_pi_num_variables.push(v.len().next_power_of_two());
        }
        stream.extend(raw_pi_num_variables.write());

        stream.extend(self.pi_evals.write());
        stream.extend(self.opcode_proofs.write());
        stream.extend(self.table_proofs.write());

        let mut circuit_vks_fixed_commits: Vec<Vec<F>> = vec![];
        for cmt in &self.circuit_vks_fixed_commits {
            let mut cmt_vec: Vec<F> = vec![];
            cmt.root().0.iter().for_each(|x| {
                let f: F = serde_json::from_str(&serde_json::to_string(x).expect("serialization"))
                    .expect("serialization bridge");
                cmt_vec.push(f);
            });
            circuit_vks_fixed_commits.push(cmt_vec);
        }
        stream.extend(circuit_vks_fixed_commits.write());

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
impl VecAutoHintable for ZKVMOpcodeProofInput {}
impl Hintable<InnerConfig> for ZKVMOpcodeProofInput {
    type HintVariable = ZKVMOpcodeProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let idx = Usize::Var(usize::read(builder));
        let idx_felt = F::read(builder);
        let num_instances = Usize::Var(usize::read(builder));
        let num_instances_minus_one_bit_decomposition = Vec::<F>::read(builder);
        let log2_num_instances = Usize::Var(usize::read(builder));
        let record_r_out_evals = Vec::<E>::read(builder);
        let record_w_out_evals = Vec::<E>::read(builder);
        let lk_p1_out_eval = E::read(builder);
        let lk_p2_out_eval = E::read(builder);
        let lk_q1_out_eval = E::read(builder);
        let lk_q2_out_eval = E::read(builder);
        let tower_proof = TowerProofInput::read(builder);
        let main_sel_sumcheck_proofs = Vec::<IOPProverMessage>::read(builder);
        let r_records_in_evals = Vec::<E>::read(builder);
        let w_records_in_evals = Vec::<E>::read(builder);
        let lk_records_in_evals = Vec::<E>::read(builder);
        let wits_commit = Vec::<F>::read(builder);
        let wits_in_evals = Vec::<E>::read(builder);

        ZKVMOpcodeProofInputVariable {
            idx,
            idx_felt,
            num_instances,
            num_instances_minus_one_bit_decomposition,
            log2_num_instances,
            record_r_out_evals,
            record_w_out_evals,
            lk_p1_out_eval,
            lk_p2_out_eval,
            lk_q1_out_eval,
            lk_q2_out_eval,
            tower_proof,
            main_sel_sumcheck_proofs,
            r_records_in_evals,
            w_records_in_evals,
            lk_records_in_evals,
            wits_commit,
            wits_in_evals,
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

        stream.extend(self.record_r_out_evals.write());
        stream.extend(self.record_w_out_evals.write());
        stream.extend(<E as Hintable<InnerConfig>>::write(&self.lk_p1_out_eval));
        stream.extend(<E as Hintable<InnerConfig>>::write(&self.lk_p2_out_eval));
        stream.extend(<E as Hintable<InnerConfig>>::write(&self.lk_q1_out_eval));
        stream.extend(<E as Hintable<InnerConfig>>::write(&self.lk_q2_out_eval));
        stream.extend(self.tower_proof.write());
        stream.extend(self.main_sel_sumcheck_proofs.write());
        stream.extend(self.r_records_in_evals.write());
        stream.extend(self.w_records_in_evals.write());
        stream.extend(self.lk_records_in_evals.write());
        let mut cmt_vec: Vec<F> = vec![];
        self.wits_commit.root().0.iter().for_each(|x| {
            let f: F = serde_json::from_str(&serde_json::to_string(x).expect("serialization"))
                .expect("serialization bridge");
            cmt_vec.push(f);
        });
        stream.extend(cmt_vec.write());
        stream.extend(self.wits_in_evals.write());

        stream
    }
}

#[derive(Default, Debug)]
pub struct ZKVMTableProofInput {
    pub idx: usize,

    // tower evaluation at layer 1
    pub r_out_evals: Vec<E>,  // Vec<[E; 2]>
    pub w_out_evals: Vec<E>,  // Vec<[E; 2]>
    pub compressed_rw_out_len: usize,
    pub lk_out_evals: Vec<E>, // Vec<[E; 4]>
    pub compressed_lk_out_len: usize,

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
impl VecAutoHintable for ZKVMTableProofInput {}
impl Hintable<InnerConfig> for ZKVMTableProofInput {
    type HintVariable = ZKVMTableProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let idx = Usize::Var(usize::read(builder));
        let idx_felt = F::read(builder);

        let r_out_evals = Vec::<E>::read(builder);
        let w_out_evals = Vec::<E>::read(builder);
        let compressed_rw_out_len = Usize::Var(usize::read(builder));
        let lk_out_evals = Vec::<E>::read(builder);
        let compressed_lk_out_len = Usize::Var(usize::read(builder));

        let has_same_r_sumcheck_proofs = Usize::Var(usize::read(builder));
        let same_r_sumcheck_proofs = Vec::<IOPProverMessage>::read(builder);
        let rw_in_evals = Vec::<E>::read(builder);
        let lk_in_evals = Vec::<E>::read(builder);
        let tower_proof = TowerProofInput::read(builder);
        let rw_hints_num_vars = Vec::<usize>::read(builder);
        let fixed_in_evals = Vec::<E>::read(builder);
        let wits_commit = Vec::<F>::read(builder);
        let wits_in_evals = Vec::<E>::read(builder);

        ZKVMTableProofInputVariable {
            idx,
            idx_felt,
            r_out_evals,
            w_out_evals,
            compressed_rw_out_len,
            lk_out_evals,
            compressed_lk_out_len,
            has_same_r_sumcheck_proofs,
            same_r_sumcheck_proofs,
            rw_in_evals,
            lk_in_evals,
            tower_proof,
            rw_hints_num_vars,
            fixed_in_evals,
            wits_commit,
            wits_in_evals,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.idx));

        let idx_u32: F = F::from_canonical_u32(self.idx as u32);
        stream.extend(idx_u32.write());

        stream.extend(self.r_out_evals.write());
        stream.extend(self.w_out_evals.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.compressed_rw_out_len,
        ));
        stream.extend(self.lk_out_evals.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.compressed_lk_out_len,
        ));

        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.has_same_r_sumcheck_proofs,
        ));
        stream.extend(self.same_r_sumcheck_proofs.write());
        stream.extend(self.rw_in_evals.write());
        stream.extend(self.lk_in_evals.write());
        stream.extend(self.tower_proof.write());
        stream.extend(self.rw_hints_num_vars.write());
        stream.extend(self.fixed_in_evals.write());

        let mut cmt_vec: Vec<F> = vec![];
        self.wits_commit.root().0.iter().for_each(|x| {
            let f: F = serde_json::from_str(&serde_json::to_string(x).expect("serialization"))
                .expect("serialization bridge");
            cmt_vec.push(f);
        });
        stream.extend(cmt_vec.write());
        stream.extend(self.wits_in_evals.write());
        stream
    }
}
