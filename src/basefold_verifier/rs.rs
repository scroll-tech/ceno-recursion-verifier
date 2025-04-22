use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

pub struct DenseMatrix {
    pub values: Vec<E>,
    pub width: usize,
}

impl Hintable<InnerConfig> for DenseMatrix {
    type HintVariable = DenseMatrixVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let values = Vec::<E>::read(builder);
        let width = Usize::Var(usize::read(builder));

        DenseMatrixVariable {
            values,
            width,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(self.values.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.width));
        stream
    }
}

#[derive(DslVariable, Clone)]
pub struct DenseMatrixVariable<C: Config> {
    pub values: Array<C, Ext<C::F, C::EF>>,
    pub width: Usize<C::N>,
}
pub type RowMajorMatrixVariable<C> = DenseMatrixVariable<C>;

impl<C: Config> DenseMatrixVariable<C> {
    // XXX: Find better ways to handle this without cloning
    pub fn pad_to_height(
        &self,
        builder: &mut Builder<C>,
        new_height: Usize<C::N>,
        fill: Ext<C::F, C::EF>,
    ) -> DenseMatrixVariable<C> {
        // assert!(new_height >= self.height());
        let new_size = builder.eval_expr(self.width.clone() * new_height);
        let evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(new_size);
        builder.range(0, self.values.len()).for_each(|i_vec, builder| {
            let i = i_vec[0];
            let tmp: Ext<C::F, C::EF> = builder.get(&self.values, i);
            builder.set(&evals, i, tmp);
        });
        builder.range(self.values.len(), evals.len()).for_each(|i_vec, builder| {
            let i = i_vec[0];
            builder.set(&evals, i, fill);
        });
        DenseMatrixVariable::<C> {
            values: evals,
            width: self.width.clone(),
        }
    }
}

/*
/// The DIT FFT algorithm.
#[derive(DslVariable, Clone)]
pub struct Radix2DitVariable<C: Config> {
    /// Memoized twiddle factors for each length log_n.
    /// Precise definition is a map from usize to E
    pub twiddles: Array<C, Ext<C::F, C::EF>>,
}

#[derive(DslVariable, Clone)]
pub struct RSCodeVerifierParametersVariable<C: Config> {
    pub dft: Radix2DitVariable<C>,
    pub t_inv_halves: Array<C, Array<C, C::F>>,
    pub full_message_size_log: Usize<C::N>,
}

pub(crate) fn encode_small<C: Config>(
    builder: &mut Builder<C>,
    vp: RSCodeVerifierParametersVariable<C>,
    rmm: RowMajorMatrixVariable<C>,
) -> RowMajorMatrixVariable<C> {
    let mut m = rmm;
}
*/

pub mod tests {
    use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::AsmBuilder;
    use openvm_native_compiler::prelude::*;
    use openvm_native_recursion::hints::Hintable;
    use openvm_stark_backend::config::StarkGenericConfig;
    use openvm_stark_sdk::{
        config::baby_bear_poseidon2::BabyBearPoseidon2Config,
        p3_baby_bear::BabyBear,
    };
    use p3_field::{extension::BinomialExtensionField, FieldAlgebra};
    type SC = BabyBearPoseidon2Config;

    type F = BabyBear;
    type E = BinomialExtensionField<F, 4>;
    type EF = <SC as StarkGenericConfig>::Challenge;
    use super::DenseMatrix;

    #[allow(dead_code)]
    pub fn build_test_dense_matrix_pad() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        // OpenVM DSL
        let mut builder = AsmBuilder::<F, EF>::default();

        // Witness inputs
        let dense_matrix_variable = DenseMatrix::read(&mut builder);
        let new_height = Usize::from(8);
        let fill = Ext::new(0);
        dense_matrix_variable.pad_to_height(&mut builder, new_height, fill);
        builder.halt();

        // Pass in witness stream
        let mut witness_stream: Vec<
            Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
        > = Vec::new();

        let verifier_input = DenseMatrix {
            values: vec![E::ONE; 25],
            width: 5,
        };
        witness_stream.extend(verifier_input.write());

        let program: Program<
            p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
        > = builder.compile_isa();

        (program, witness_stream)
    }

    #[test]
    fn test_dense_matrix_pad() {
        let (program, witness) = build_test_dense_matrix_pad();

        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100);
        let config = NativeConfig::new(system_config, Native);

        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
        executor.execute(program, witness).unwrap();

        // _debug
        // let results = executor.execute_segments(program, witness).unwrap();
        // for seg in results {
        //     println!("=> cycle count: {:?}", seg.metrics.cycle_count);
        // }
    }
}