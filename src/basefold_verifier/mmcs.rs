// Note: check all XXX comments!

use std::marker::PhantomData;

use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::{hints::Hintable, vars::HintSlice};
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;

use super::{hash::*, structs::*};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, DIMENSIONS>;
pub type InnerConfig = AsmConfig<F, E>;

pub type MmcsCommitment = Hash;
pub type MmcsProof = Vec<[F; DIGEST_ELEMS]>;
pub struct MmcsVerifierInput {
    pub commit: MmcsCommitment,
    pub dimensions: Vec<usize>,
    pub index: usize,
    pub opened_values: Vec<Vec<F>>,
    pub proof: MmcsProof,
}

impl Hintable<InnerConfig> for MmcsVerifierInput {
    type HintVariable = MmcsVerifierInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let commit = MmcsCommitment::read(builder);
        let dimensions = Vec::<usize>::read(builder);
        let index_bits = Vec::<usize>::read(builder);
        let opened_values = Vec::<Vec<F>>::read(builder);
        let length = Usize::from(builder.hint_var());
        let id = Usize::from(builder.hint_load());
        let proof = HintSlice { length, id };

        MmcsVerifierInputVariable {
            commit,
            dimensions,
            index_bits,
            opened_values,
            proof,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        // Split index into bits
        stream.extend(self.commit.write());
        stream.extend(self.dimensions.write());
        let mut index_bits = Vec::new();
        let mut index = self.index;
        while index > 0 {
            index_bits.push(index % 2);
            index /= 2;
        }
        stream.extend(<Vec<usize> as Hintable<InnerConfig>>::write(&index_bits));
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

pub type MmcsCommitmentVariable<C> = HashVariable<C>;

#[derive(DslVariable, Clone)]
pub struct MmcsVerifierInputVariable<C: Config> {
    pub commit: MmcsCommitmentVariable<C>,
    pub dimensions: Array<C, Var<C::N>>,
    pub index_bits: Array<C, Var<C::N>>,
    pub opened_values: Array<C, Array<C, Felt<C::F>>>,
    pub proof: HintSlice<C>,
}

pub(crate) fn mmcs_verify_batch<C: Config>(
    builder: &mut Builder<C>,
    input: MmcsVerifierInputVariable<C>,
) {
    let dimensions = match input.dimensions {
        Array::Dyn(ptr, len) => Array::Dyn(ptr, len.clone()),
        _ => panic!("Expected a dynamic array of felts"),
    };
    builder.verify_batch_felt(
        &dimensions,
        &input.opened_values,
        input.proof.id.get_var(),
        &input.index_bits,
        &input.commit.value,
    );
}

pub mod tests {
    use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::AsmBuilder;
    use openvm_native_recursion::hints::Hintable;
    use openvm_stark_backend::config::StarkGenericConfig;
    use openvm_stark_sdk::{
        config::baby_bear_poseidon2::BabyBearPoseidon2Config, p3_baby_bear::BabyBear,
    };
    use p3_field::{extension::BinomialExtensionField, FieldAlgebra};
    type SC = BabyBearPoseidon2Config;

    type F = BabyBear;
    type E = BinomialExtensionField<F, 4>;
    type EF = <SC as StarkGenericConfig>::Challenge;
    use crate::basefold_verifier::structs::Dimensions;

    use super::{mmcs_verify_batch, InnerConfig, MmcsCommitment, MmcsVerifierInput};

    #[allow(dead_code)]
    pub fn build_mmcs_verify_batch() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        // OpenVM DSL
        let mut builder = AsmBuilder::<F, EF>::default();

        // Witness inputs
        let mmcs_input = MmcsVerifierInput::read(&mut builder);
        mmcs_verify_batch(&mut builder, mmcs_input);
        builder.halt();

        // Pass in witness stream
        let f = |n: usize| F::from_canonical_usize(n);
        let mut witness_stream: Vec<
            Vec<p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>>,
        > = Vec::new();
        let commit = MmcsCommitment {
            value: [
                f(1715944678),
                f(1204294900),
                f(59582177),
                f(320945505),
                f(1470843790),
                f(1773915204),
                f(380281369),
                f(383365269),
            ],
        };
        // let dimensions = vec![
        //     Dimensions {
        //         width: 8,
        //         height: 1,
        //     },
        //     Dimensions {
        //         width: 8,
        //         height: 1,
        //     },
        //     Dimensions {
        //         width: 8,
        //         height: 70,
        //     },
        // ];
        let dimensions = vec![1, 1, 70];
        let index = 6;
        let opened_values = vec![
            vec![
                f(774319227),
                f(1631186743),
                f(254325873),
                f(504149682),
                f(239740532),
                f(1126519109),
                f(1044404585),
                f(1274764277),
            ],
            vec![
                f(1486505160),
                f(631183960),
                f(329388712),
                f(1934479253),
                f(115532954),
                f(1978455077),
                f(66346996),
                f(821157541),
            ],
            vec![
                f(149196326),
                f(1186650877),
                f(1970038391),
                f(1893286029),
                f(1249658956),
                f(1618951617),
                f(419030634),
                f(1967997848),
            ],
        ];
        let proof = vec![
            [
                f(845920358),
                f(1201648213),
                f(1087654550),
                f(264553580),
                f(633209321),
                f(877945079),
                f(1674449089),
                f(1062812099),
            ],
            [
                f(5498027),
                f(1901489519),
                f(179361222),
                f(41261871),
                f(1546446894),
                f(266690586),
                f(1882928070),
                f(844710372),
            ],
            [
                f(721245096),
                f(388358486),
                f(1443363461),
                f(1349470697),
                f(253624794),
                f(1359455861),
                f(237485093),
                f(1955099141),
            ],
            [
                f(1816731864),
                f(402719753),
                f(1972161922),
                f(693018227),
                f(1617207065),
                f(1848150948),
                f(360933015),
                f(669793414),
            ],
            [
                f(1746479395),
                f(457185725),
                f(1263857148),
                f(328668702),
                f(1743038915),
                f(582282833),
                f(927410326),
                f(376217274),
            ],
            [
                f(1146845382),
                f(1117439420),
                f(1622226137),
                f(1449227765),
                f(138752938),
                f(1251889563),
                f(1266915653),
                f(267248408),
            ],
            [
                f(1992750195),
                f(1604624754),
                f(1748646393),
                f(1777984113),
                f(861317745),
                f(564150089),
                f(1371546358),
                f(460033967),
            ],
        ];
        let mmcs_input = MmcsVerifierInput {
            commit,
            dimensions,
            index,
            opened_values,
            proof,
        };
        witness_stream.extend(mmcs_input.write());

        // PROGRAM
        let program: Program<
            p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
        > = builder.compile_isa();

        (program, witness_stream)
    }

    #[test]
    fn test_mmcs_verify_batch() {
        let (program, witness) = build_mmcs_verify_batch();

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
