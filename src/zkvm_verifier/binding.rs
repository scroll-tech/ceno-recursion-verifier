use crate::arithmetics::next_pow2_instance_padding;
use crate::basefold_verifier::basefold::{
    BasefoldCommitment, BasefoldCommitmentVariable, BasefoldProof, BasefoldProofVariable,
};
use crate::basefold_verifier::query_phase::{
    QueryPhaseVerifierInput, QueryPhaseVerifierInputVariable,
};
use crate::{
    arithmetics::ceil_log2,
    tower_verifier::binding::{IOPProverMessage, IOPProverMessageVariable},
};
use ark_std::iterable::Iterable;
use ff_ext::BabyBearExt4;
use itertools::Itertools;
use openvm_circuit::derive;
use openvm_native_compiler::{
    asm::AsmConfig,
    ir::{Array, Builder, Config, Felt},
    prelude::*,
};
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use openvm_stark_backend::p3_field::{FieldAlgebra, extension::BinomialExtensionField};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

#[derive(DslVariable, Clone)]
pub struct ZKVMProofInputVariable<C: Config> {
    pub raw_pi: Array<C, Array<C, Felt<C::F>>>,
    pub raw_pi_num_variables: Array<C, Var<C::N>>,
    pub pi_evals: Array<C, Ext<C::F, C::EF>>,
    pub chip_proofs: Array<C, ZKVMChipProofInputVariable<C>>,
    pub max_num_var: Var<C::N>,
    pub witin_commit: BasefoldCommitmentVariable<C>,
    pub witin_perm: Array<C, Var<C::N>>,
    pub fixed_perm: Array<C, Var<C::N>>,
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
    pub witin_commit: BasefoldCommitment,
    pub pcs_proof: BasefoldProof,
}

impl Hintable<InnerConfig> for ZKVMProofInput {
    type HintVariable = ZKVMProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let raw_pi = Vec::<Vec<F>>::read(builder);
        let raw_pi_num_variables = Vec::<usize>::read(builder);
        let pi_evals = Vec::<E>::read(builder);
        let chip_proofs = Vec::<ZKVMChipProofInput>::read(builder);
        let max_num_var = usize::read(builder);
        let witin_commit = BasefoldCommitment::read(builder);
        let witin_perm = Vec::<usize>::read(builder);
        let fixed_perm = Vec::<usize>::read(builder);
        let pcs_proof = BasefoldProof::read(builder);

        ZKVMProofInputVariable {
            raw_pi,
            raw_pi_num_variables,
            pi_evals,
            chip_proofs,
            max_num_var,
            witin_commit,
            witin_perm,
            fixed_perm,
            pcs_proof,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        let raw_pi_num_variables: Vec<usize> = self
            .raw_pi
            .iter()
            .map(|v| ceil_log2(v.len().next_power_of_two()))
            .collect();
        let witin_num_vars = self
            .chip_proofs
            .iter()
            .map(|proof| ceil_log2(proof.num_instances).max(1))
            .collect::<Vec<_>>();
        let fixed_num_vars = self
            .chip_proofs
            .iter()
            .filter(|proof| proof.fixed_in_evals.len() > 0)
            .map(|proof| ceil_log2(proof.num_instances).max(1))
            .collect::<Vec<_>>();
        let max_num_var = witin_num_vars.iter().map(|x| *x).max().unwrap_or(0);
        let get_perm = |v: Vec<usize>| {
            let mut perm = vec![0; v.len()];
            v.into_iter()
                // the original order
                .enumerate()
                .sorted_by(|(_, nv_a), (_, nv_b)| Ord::cmp(nv_b, nv_a))
                .enumerate()
                // j is the new index where i is the original index
                .map(|(j, (i, _))| (i, j))
                .for_each(|(i, j)| {
                    perm[i] = j;
                });
            perm
        };
        let witin_perm = get_perm(witin_num_vars);
        let fixed_perm = get_perm(fixed_num_vars);

        stream.extend(self.raw_pi.write());
        stream.extend(raw_pi_num_variables.write());
        stream.extend(self.pi_evals.write());
        stream.extend(self.opcode_proofs.write());
        stream.extend(self.table_proofs.write());

        // Write in witin_commit
        let mut cmt_vec: Vec<F> = vec![];
        self.witin_commit.commit().iter().for_each(|x| {
            let f: F = serde_json::from_value(serde_json::to_value(&x).unwrap()).unwrap();
            cmt_vec.push(f);
        });
        let mut witin_commit_trivial_commits: Vec<Vec<F>> = vec![];
        /* _debug
        for trivial_commit in &self.witin_commit.trivial_commits {
            let mut t_cmt_vec: Vec<F> = vec![];
            trivial_commit.iter().for_each(|x| {
                let f: F =
                    serde_json::from_value(serde_json::to_value(x.clone()).unwrap()).unwrap();
                t_cmt_vec.push(f);
            });
            witin_commit_trivial_commits.push(t_cmt_vec);
        }
        */
        let witin_commit_log2_max_codeword_size =
            F::from_canonical_u32(self.witin_commit.log2_max_codeword_size as u32);
        stream.extend(cmt_vec.write());
        stream.extend(witin_commit_trivial_commits.write());
        stream.extend(witin_commit_log2_max_codeword_size.write());

        // Write in fixed_commit
        let has_fixed_commit: usize = if self.fixed_commit.is_some() { 1 } else { 0 };
        let mut fixed_commit_vec: Vec<F> = vec![];
        let mut fixed_commit_trivial_commits: Vec<Vec<F>> = vec![];
        let mut fixed_commit_log2_max_codeword_size: F = F::ZERO.clone();
        if has_fixed_commit > 0 {
            self.fixed_commit
                .as_ref()
                .unwrap()
                .commit()
                .iter()
                .for_each(|x| {
                    let f: F =
                        serde_json::from_value(serde_json::to_value(x.clone()).unwrap()).unwrap();
                    fixed_commit_vec.push(f);
                });

            /* _debug
            for trivial_commit in &self.fixed_commit.as_ref().unwrap().trivial_commits {
                let mut t_cmt_vec: Vec<F> = vec![];
                trivial_commit.iter().for_each(|x| {
                    let f: F =
                        serde_json::from_value(serde_json::to_value(x.clone()).unwrap()).unwrap();
                    t_cmt_vec.push(f);
                });
                fixed_commit_trivial_commits.push(t_cmt_vec);
            }
            */
            fixed_commit_log2_max_codeword_size = F::from_canonical_u32(
                self.fixed_commit.as_ref().unwrap().log2_max_codeword_size as u32,
            );
        }
        stream.extend(<usize as Hintable<InnerConfig>>::write(&has_fixed_commit));
        stream.extend(fixed_commit_vec.write());
        stream.extend(fixed_commit_trivial_commits.write());
        stream.extend(fixed_commit_log2_max_codeword_size.write());

        // Write num_instances
        let mut num_instances_vec: Vec<Vec<F>> = vec![];
        for (circuit_size, num_var) in &self.num_instances {
            num_instances_vec.push(vec![
                F::from_canonical_usize(*circuit_size),
                F::from_canonical_usize(*num_var),
            ]);
        }
        stream.extend(num_instances_vec.write());

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

#[derive(Default)]
pub(crate) struct SumcheckLayerProofInput {
    pub proof: Vec<IOPProverMessage>,
    pub evals: Vec<E>,
}
#[derive(DslVariable, Clone)]
pub(crate) struct SumcheckLayerProofVariable<C: Config> {
    pub proof: Array<C, IOPProverMessageVariable<C>>,
    pub evals: Array<C, Ext<C::F, C::EF>>,
}
impl VecAutoHintable for SumcheckLayerProofInput {}
impl Hintable<InnerConfig> for SumcheckLayerProofInput {
    type HintVariable = SumcheckLayerProofVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let proof = Vec::<IOPProverMessage>::read(builder);
        let evals = Vec::<E>::read(builder);
        Self::HintVariable {
            proof,
            evals
        }
    }
    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.proof.write());
        stream.extend(self.evals.write());
        stream
    }
}

pub(crate) struct LayerProofInput {
    pub has_rotation: usize,
    pub rotation: SumcheckLayerProofInput,
    pub main: SumcheckLayerProofInput,
}
#[derive(DslVariable, Clone)]
pub(crate) struct LayerProofVariable<C: Config> {
    pub has_rotation: Var<C::N>,
    pub rotation: SumcheckLayerProofVariable<C>,
    pub main: SumcheckLayerProofVariable<C>,
}
impl VecAutoHintable for LayerProofInput {}
impl Hintable<InnerConfig> for LayerProofInput {
    type HintVariable = LayerProofVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let has_rotation = usize::read(builder);
        let rotation = SumcheckLayerProofInput::read(builder);
        let main = SumcheckLayerProofInput::read(builder);

        Self::HintVariable {
            has_rotation,
            rotation,
            main,
        }
    }
    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.has_rotation));
        stream.extend(self.rotation.write());
        stream.extend(self.main.write());
        stream
    }
}
#[derive(Default)]
pub(crate) struct GKRProofInput {
    pub num_var_with_rotation: usize,
    pub layer_proofs: Vec<LayerProofInput>,
}
#[derive(DslVariable, Clone)]
pub(crate) struct GKRProofVariable<C: Config> {
    pub num_var_with_rotation: Var<C::N>,
    pub layer_proofs: Array<C, LayerProofVariable<C>>,
}
impl Hintable<InnerConfig> for GKRProofInput {
    type HintVariable = GKRProofVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let num_var_with_rotation = usize::read(builder);
        let layer_proofs = Vec::<LayerProofInput>::read(builder);
        Self::HintVariable {
            num_var_with_rotation,
            layer_proofs,
        }
    }
    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.num_var_with_rotation));
        stream.extend(self.layer_proofs.write());
        stream
    }
}