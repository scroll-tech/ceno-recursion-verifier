use crate::arithmetics::next_pow2_instance_padding;
use crate::basefold_verifier::basefold::{
    BasefoldCommitment, BasefoldCommitmentVariable, BasefoldProof, BasefoldProofVariable,
};
use crate::basefold_verifier::query_phase::{
    QueryPhaseVerifierInput, QueryPhaseVerifierInputVariable,
};
use crate::tower_verifier::binding::{
    IOPProverMessageVec, IOPProverMessageVecVariable, ThreeDimensionalVecVariable,
    ThreeDimensionalVector,
};
use crate::{
    arithmetics::ceil_log2,
    tower_verifier::binding::{IOPProverMessage, IOPProverMessageVariable},
};
use ark_std::iterable::Iterable;
use ff_ext::BabyBearExt4;
use itertools::Itertools;
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
    pub max_num_var: Var<C::N>,
    pub max_width: Var<C::N>,
    pub witin_commit: BasefoldCommitmentVariable<C>,
    pub witin_perm: Array<C, Var<C::N>>,
    pub fixed_perm: Array<C, Var<C::N>>,
    pub pcs_proof: BasefoldProofVariable<C>,
}

#[derive(DslVariable, Clone)]
pub struct TowerProofInputVariable<C: Config> {
    pub num_proofs: Usize<C::N>,
    pub proofs: Array<C, IOPProverMessageVecVariable<C>>,
    pub num_prod_specs: Usize<C::N>,
    pub prod_specs_eval: ThreeDimensionalVecVariable<C>,
    pub num_logup_specs: Usize<C::N>,
    pub logup_specs_eval: ThreeDimensionalVecVariable<C>,
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

    pub main_sel_sumcheck_proofs: IOPProverMessageVecVariable<C>,
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
        builder.cycle_tracker_start("read raw pi");
        let raw_pi = Vec::<Vec<F>>::read(builder);
        builder.cycle_tracker_end("read raw pi");
        builder.cycle_tracker_start("read raw pi num vars");
        let raw_pi_num_variables = Vec::<usize>::read(builder);
        builder.cycle_tracker_end("read raw pi num vars");
        builder.cycle_tracker_start("read pi evals");
        let pi_evals = Vec::<E>::read(builder);
        builder.cycle_tracker_end("read pi evals");
        builder.cycle_tracker_start("read chip proofs");
        let chip_proofs = Vec::<ZKVMChipProofInput>::read(builder);
        builder.cycle_tracker_end("read chip proofs");
        builder.cycle_tracker_start("read max num var");
        let max_num_var = usize::read(builder);
        builder.cycle_tracker_end("read max num var");
        builder.cycle_tracker_start("read max width");
        let max_width = usize::read(builder);
        builder.cycle_tracker_end("read max width");
        builder.cycle_tracker_start("read witin commit");
        let witin_commit = BasefoldCommitment::read(builder);
        builder.cycle_tracker_end("read witin commit");
        builder.cycle_tracker_start("read witin perm");
        let witin_perm = Vec::<usize>::read(builder);
        builder.cycle_tracker_end("read witin perm");
        builder.cycle_tracker_start("read fixed perm");
        let fixed_perm = Vec::<usize>::read(builder);
        builder.cycle_tracker_end("read fixed perm");
        builder.cycle_tracker_start("read pcs proof");
        let pcs_proof = BasefoldProof::read(builder);
        builder.cycle_tracker_end("read pcs proof");

        ZKVMProofInputVariable {
            raw_pi,
            raw_pi_num_variables,
            pi_evals,
            chip_proofs,
            max_num_var,
            max_width,
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
        let witin_max_widths = self
            .chip_proofs
            .iter()
            .map(|proof| proof.wits_in_evals.len().max(1))
            .collect::<Vec<_>>();
        let fixed_num_vars = self
            .chip_proofs
            .iter()
            .filter(|proof| proof.fixed_in_evals.len() > 0)
            .map(|proof| ceil_log2(proof.num_instances).max(1))
            .collect::<Vec<_>>();
        let fixed_max_widths = self
            .chip_proofs
            .iter()
            .filter(|proof| proof.fixed_in_evals.len() > 0)
            .map(|proof| proof.fixed_in_evals.len())
            .collect::<Vec<_>>();
        let max_num_var = witin_num_vars.iter().map(|x| *x).max().unwrap_or(0);
        let max_width = witin_max_widths
            .iter()
            .chain(fixed_max_widths.iter())
            .map(|x| *x)
            .max()
            .unwrap_or(0);
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
        stream.extend(self.chip_proofs.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(&max_num_var));
        stream.extend(<usize as Hintable<InnerConfig>>::write(&max_width));
        stream.extend(self.witin_commit.write());
        stream.extend(witin_perm.write());
        stream.extend(fixed_perm.write());
        stream.extend(self.pcs_proof.write());

        stream
    }
}

#[derive(Default, Debug)]
pub struct TowerProofInput {
    pub num_proofs: usize,
    pub proofs: Vec<IOPProverMessageVec>,
    // specs -> layers -> evals
    pub num_prod_specs: usize,
    pub prod_specs_eval: ThreeDimensionalVector,
    // specs -> layers -> evals
    pub num_logup_specs: usize,
    pub logup_specs_eval: ThreeDimensionalVector,
}

impl Hintable<InnerConfig> for TowerProofInput {
    type HintVariable = TowerProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let num_proofs = Usize::Var(usize::read(builder));
        let proofs = builder.dyn_array(num_proofs.clone());
        iter_zip!(builder, proofs).for_each(|idx_vec, builder| {
            let ptr = idx_vec[0];
            builder.cycle_tracker_start("IOPProver Message Vec read");
            let proof = IOPProverMessageVec::read(builder);
            builder.cycle_tracker_end("IOPProver Message Vec read");
            builder.iter_ptr_set(&proofs, ptr, proof);
        });

        let num_prod_specs = Usize::Var(usize::read(builder));
        builder.cycle_tracker_start("Product Specifications Evaluation read");
        let prod_specs_eval = ThreeDimensionalVector::read(builder);
        builder.cycle_tracker_end("Product Specifications Evaluation read");

        let num_logup_specs = Usize::Var(usize::read(builder));
        builder.cycle_tracker_start("Logup Specifications Evaluation read");
        let logup_specs_eval = ThreeDimensionalVector::read(builder);
        builder.cycle_tracker_end("Logup Specifications Evaluation read");

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
            println!("IOP Proof length {}", p.data.len() * 4);
            stream.extend(p.write());
        }
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.num_prod_specs,
        ));
        println!("Prod spec length {}", self.prod_specs_eval.data.len() * 4);
        stream.extend(self.prod_specs_eval.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.num_logup_specs,
        ));
        println!("Logup spec length {}", self.logup_specs_eval.data.len() * 4);
        stream.extend(self.logup_specs_eval.write());

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
    pub main_sumcheck_proofs: IOPProverMessageVec,
    pub wits_in_evals: Vec<E>,
    pub fixed_in_evals: Vec<E>,
}

impl VecAutoHintable for ZKVMChipProofInput {}

impl Hintable<InnerConfig> for ZKVMChipProofInput {
    type HintVariable = ZKVMChipProofInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        builder.cycle_tracker_start("Read chip proof");
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

        builder.cycle_tracker_start("Tower proof");
        let tower_proof = TowerProofInput::read(builder);
        builder.cycle_tracker_end("Tower proof");
        let main_sel_sumcheck_proofs = IOPProverMessageVec::read(builder);
        let wits_in_evals = Vec::<E>::read(builder);
        let fixed_in_evals = Vec::<E>::read(builder);
        builder.cycle_tracker_end("Read chip proof");

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
