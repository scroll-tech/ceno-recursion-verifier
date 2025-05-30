use openvm_native_compiler::{asm::AsmConfig, ir::*};
use openvm_native_compiler_derive::DslVariable;
use openvm_native_recursion::hints::{Hintable, VecAutoHintable};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use serde::Deserialize;

pub const DIMENSIONS: usize = 4;

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, DIMENSIONS>;
pub type InnerConfig = AsmConfig<F, E>;

use super::rs::get_rate_log;
use super::utils::pow_2;

#[derive(DslVariable, Clone)]
pub struct CircuitIndexMetaVariable<C: Config> {
    pub witin_num_vars: Usize<C::N>,
    pub witin_num_polys: Usize<C::N>,
    pub fixed_num_vars: Usize<C::N>,
    pub fixed_num_polys: Usize<C::N>,
}

#[derive(Deserialize)]
pub struct CircuitIndexMeta {
    pub witin_num_vars: usize,
    pub witin_num_polys: usize,
    pub fixed_num_vars: usize,
    pub fixed_num_polys: usize,
}

impl Hintable<InnerConfig> for CircuitIndexMeta {
    type HintVariable = CircuitIndexMetaVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let witin_num_vars = Usize::Var(usize::read(builder));
        let witin_num_polys = Usize::Var(usize::read(builder));
        let fixed_num_vars = Usize::Var(usize::read(builder));
        let fixed_num_polys = Usize::Var(usize::read(builder));

        CircuitIndexMetaVariable {
            witin_num_vars,
            witin_num_polys,
            fixed_num_vars,
            fixed_num_polys,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.witin_num_vars,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.witin_num_polys,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.fixed_num_vars,
        ));
        stream.extend(<usize as Hintable<InnerConfig>>::write(
            &self.fixed_num_polys,
        ));
        stream
    }
}
impl VecAutoHintable for CircuitIndexMeta {}

#[derive(DslVariable, Clone)]
pub struct DimensionsVariable<C: Config> {
    pub width: Var<C::N>,
    pub height: Var<C::N>,
}

pub struct Dimensions {
    pub width: usize,
    pub height: usize,
}

impl Hintable<InnerConfig> for Dimensions {
    type HintVariable = DimensionsVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let width = usize::read(builder);
        let height = usize::read(builder);

        DimensionsVariable { width, height }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.width));
        stream.extend(<usize as Hintable<InnerConfig>>::write(&self.height));
        stream
    }
}
impl VecAutoHintable for Dimensions {}

pub fn get_base_codeword_dimensions<C: Config>(
    builder: &mut Builder<C>,
    circuit_meta_map: Array<C, CircuitIndexMetaVariable<C>>,
) -> (Array<C, Var<C::N>>, Array<C, Var<C::N>>) {
    let dim_len = circuit_meta_map.len();
    let wit_dim: Array<C, Var<C::N>> = builder.dyn_array(dim_len.clone());
    let fixed_dim: Array<C, Var<C::N>> = builder.dyn_array(dim_len.clone());

    builder.range(0, dim_len).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let tmp = builder.get(&circuit_meta_map, i);
        let witin_num_vars = tmp.witin_num_vars;
        let witin_num_polys = tmp.witin_num_polys;
        let fixed_num_vars = tmp.fixed_num_vars;
        let fixed_num_polys = tmp.fixed_num_polys;
        // wit_dim
        // let width = builder.eval(witin_num_polys * Usize::from(2));
        let height_exp = builder.eval(witin_num_vars + get_rate_log::<C>() - Usize::from(1));
        let height = pow_2(builder, height_exp);
        // let next_wit: DimensionsVariable<C> = DimensionsVariable { width, height };
        // Only keep the height because the width is not needed in the mmcs batch
        // verify instruction
        builder.set_value(&wit_dim, i, height);

        // fixed_dim
        // XXX: since fixed_num_vars is usize, fixed_num_vars > 0 is equivalent to fixed_num_vars != 0
        builder
            .if_ne(fixed_num_vars.clone(), Usize::from(0))
            .then(|builder| {
                // let width = builder.eval(fixed_num_polys.clone() * Usize::from(2));
                let height_exp =
                    builder.eval(fixed_num_vars.clone() + get_rate_log::<C>() - Usize::from(1));
                // XXX: more efficient pow implementation
                let height = pow_2(builder, height_exp);
                // let next_fixed: DimensionsVariable<C> = DimensionsVariable { width, height };
                builder.set_value(&fixed_dim, i, height);
            });
    });
    (wit_dim, fixed_dim)
}

pub mod tests {
    use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::AsmBuilder;
    use openvm_native_compiler::prelude::*;
    use openvm_native_recursion::hints::Hintable;
    use openvm_stark_backend::config::StarkGenericConfig;
    use openvm_stark_sdk::{
        config::baby_bear_poseidon2::BabyBearPoseidon2Config, p3_baby_bear::BabyBear,
    };
    use p3_field::extension::BinomialExtensionField;
    type SC = BabyBearPoseidon2Config;

    type F = BabyBear;
    type E = BinomialExtensionField<F, 4>;
    type EF = <SC as StarkGenericConfig>::Challenge;
    use crate::basefold_verifier::structs::*;

    use super::{get_base_codeword_dimensions, InnerConfig};

    #[allow(dead_code)]
    pub fn build_test_get_base_codeword_dimensions() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        // OpenVM DSL
        let mut builder = AsmBuilder::<F, EF>::default();

        // Witness inputs
        let map_len = Usize::Var(usize::read(&mut builder));
        let circuit_meta_map = builder.dyn_array(map_len.clone());
        builder
            .range(0, map_len.clone())
            .for_each(|i_vec, builder| {
                let i = i_vec[0];
                let next_meta = CircuitIndexMeta::read(builder);
                builder.set(&circuit_meta_map, i, next_meta);
            });

        let (wit_dim, fixed_dim) = get_base_codeword_dimensions(&mut builder, circuit_meta_map);
        builder.range(0, map_len).for_each(|i_vec, builder| {
            let i = i_vec[0];
            let wit = builder.get(&wit_dim, i);
            let fixed = builder.get(&fixed_dim, i);
            let i_val: Var<_> = builder.eval(i);
            builder.print_v(i_val);
            // let ww_val: Var<_> = builder.eval(wit.width);
            // let wh_val: Var<_> = builder.eval(wit.height);
            // let fw_val: Var<_> = builder.eval(fixed.width);
            // let fh_val: Var<_> = builder.eval(fixed.height);
            // builder.print_v(ww_val);
            builder.print_v(wit);
            // builder.print_v(fw_val);
            builder.print_v(fixed);
        });
        builder.halt();

        // Pass in witness stream
        let mut witness_stream: Vec<
            Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
        > = Vec::new();

        // Map length
        let map_len = 5;
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&map_len));
        for i in 0..map_len {
            // Individual metas
            let circuit_meta = CircuitIndexMeta {
                witin_num_vars: i,
                witin_num_polys: i,
                fixed_num_vars: i,
                fixed_num_polys: i,
            };
            witness_stream.extend(circuit_meta.write());
        }

        let program: Program<
            p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
        > = builder.compile_isa();

        (program, witness_stream)
    }

    #[test]
    fn test_dense_matrix_pad() {
        let (program, witness) = build_test_get_base_codeword_dimensions();

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
