use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::FieldExtensionAlgebra;

use super::{mmcs::*, structs::*};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, DIMENSIONS>;
pub type InnerConfig = AsmConfig<F, E>;

pub struct ExtensionMmcs {
    pub inner: MerkleTreeMmcs,
}

#[derive(Default, Clone)]
pub struct ExtensionMmcsVariable<C: Config> {
    pub inner: MerkleTreeMmcsVariable<C>,
}

pub struct ExtMmcsVerifierInput {
    pub commit: MmcsCommitment,
    pub dimensions: Vec<Dimensions>,
    pub index: usize,
    pub opened_values: Vec<Vec<E>>,
    pub proof: MmcsProof,
}

impl Hintable<InnerConfig> for ExtMmcsVerifierInput {
    type HintVariable = ExtMmcsVerifierInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let commit = MmcsCommitment::read(builder);
        let dimensions = Vec::<Dimensions>::read(builder);
        let index = usize::read(builder);
        let opened_values = Vec::<Vec<E>>::read(builder);
        let proof = Vec::<Vec<F>>::read(builder);

        ExtMmcsVerifierInputVariable {
            commit,
            dimensions,
            index,
            opened_values,
            proof,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.commit.write());
        stream.extend(self.dimensions.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.index));
        stream.extend(self.opened_values.write());
        stream.extend(
            self.proof
                .iter()
                .map(|p| p.to_vec())
                .collect::<Vec<_>>()
                .write(),
        );
        stream
    }
}

#[derive(DslVariable, Clone)]
pub struct ExtMmcsVerifierInputVariable<C: Config> {
    pub commit: MmcsCommitmentVariable<C>,
    pub dimensions: Array<C, DimensionsVariable<C>>,
    pub index: Var<C::N>,
    pub opened_values: Array<C, Array<C, Ext<C::F, C::EF>>>,
    pub proof: MmcsProofVariable<C>,
}

pub(crate) fn ext_mmcs_verify_batch<C: Config>(
    builder: &mut Builder<C>,
    mmcs: ExtensionMmcsVariable<C>, // self
    input: ExtMmcsVerifierInputVariable<C>,
) {
    let dim_factor: Var<C::N> = builder.eval(Usize::from(C::EF::D));
    let opened_base_values = builder.dyn_array(input.opened_values.len());
    let base_dimensions = builder.dyn_array(input.dimensions.len());

    builder
        .range(0, input.opened_values.len())
        .for_each(|i_vec, builder| {
            let i = i_vec[0];
            // opened_values
            let next_opened_values = builder.get(&input.opened_values, i);
            let next_opened_base_values_len: Var<C::N> =
                builder.eval(next_opened_values.len() * dim_factor);
            let next_opened_base_values = builder.dyn_array(next_opened_base_values_len);
            let next_opened_base_index: Var<C::N> = builder.eval(Usize::from(0));
            builder
                .range(0, next_opened_values.len())
                .for_each(|j_vec, builder| {
                    let j = j_vec[0];
                    let next_opened_value = builder.get(&next_opened_values, j);
                    // XXX: how to convert Ext to [Felt]?
                    let next_opened_value_felt = builder.ext2felt(next_opened_value);
                    builder
                        .range(0, next_opened_value_felt.len())
                        .for_each(|k_vec, builder| {
                            let k = k_vec[0];
                            let next_felt = builder.get(&next_opened_value_felt, k);
                            builder.set_value(
                                &next_opened_base_values,
                                next_opened_base_index,
                                next_felt,
                            );
                            builder.assign(
                                &next_opened_base_index,
                                next_opened_base_index + Usize::from(1),
                            );
                        });
                });
            builder.set_value(&opened_base_values, i, next_opened_base_values);

            // dimensions
            let next_dimension = builder.get(&input.dimensions, i);
            let next_base_dimension = DimensionsVariable {
                width: builder.eval(next_dimension.width.clone() * dim_factor),
                height: next_dimension.height.clone(),
            };
            builder.set_value(&base_dimensions, i, next_base_dimension);
        });

    let dimensions = match input.dimensions {
        Array::Dyn(ptr, len) => Array::Dyn(ptr, len.clone()),
        _ => panic!("Expected a dynamic array of felts"),
    };

    builder.verify_batch_ext(
        &dimensions,
        &input.opened_values,
        &input.proof_id,
        &input.index_bits,
        &input.commit.value,
    );

    let input = MmcsVerifierInputVariable {
        commit: input.commit,
        dimensions: base_dimensions,
        index: input.index,
        opened_values: opened_base_values,
        proof: input.proof,
    };
    mmcs_verify_batch(builder, mmcs.inner, input);
}
