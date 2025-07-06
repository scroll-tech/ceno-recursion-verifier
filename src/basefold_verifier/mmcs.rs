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
        for _ in 0..self.proof.len() {
            index_bits.push(index % 2);
            index /= 2;
        }
        // index_bits.reverse(); // Index bits is big endian ?
        stream.extend(<Vec<usize> as Hintable<InnerConfig>>::write(&index_bits));
        stream.extend(self.opened_values.write());
        stream.extend(<usize as Hintable<InnerConfig>>::write(&(self.proof.len()))); // According to openvm extensions/native/recursion/src/fri/hints.rs
        stream.extend(
            self.proof
                .iter()
                .flat_map(|p| p.iter().copied())
                .collect::<Vec<_>>()
                .write(),
        ); // According to openvm extensions/native/recursion/src/fri/hints.rs
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

    /// The witness in this test is produced by:
    /// https://github.com/Jiangkm3/Plonky3 branch cyte/mmcs-poseidon2-constants
    /// cargo test --package p3-merkle-tree --lib -- mmcs::tests::size_gaps --exact --show-output
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
                f(414821839),
                f(366064801),
                f(76927727),
                f(1054874897),
                f(522043147),
                f(638338172),
                f(1583746438),
                f(941156703),
            ],
        };
        let dimensions = vec![7, 0, 0];
        let index = 6;
        let opened_values = vec![
            vec![
                f(783379538),
                f(1083745632),
                f(1297755122),
                f(739705382),
                f(1249630435),
                f(1794480926),
                f(706129135),
                f(51286871),
            ],
            vec![
                f(1782820525),
                f(487690259),
                f(1939320991),
                f(1236615939),
                f(1149125220),
                f(1681169264),
                f(418636771),
                f(1198975790),
            ],
            vec![
                f(1782820525),
                f(487690259),
                f(1939320991),
                f(1236615939),
                f(1149125220),
                f(1681169264),
                f(418636771),
                f(1198975790),
            ],
        ];
        let proof = vec![
            [
                f(709175359),
                f(862600965),
                f(21724453),
                f(1644204827),
                f(1122851899),
                f(902491334),
                f(187250228),
                f(766400688),
            ],
            [
                f(1500388444),
                f(788589576),
                f(699109303),
                f(1804289606),
                f(295155621),
                f(328080503),
                f(198482491),
                f(1942550078),
            ],
            [
                f(132120813),
                f(362247724),
                f(635527855),
                f(709381234),
                f(1331884835),
                f(1016275827),
                f(962247980),
                f(1772849136),
            ],
            [
                f(1707124288),
                f(1917010688),
                f(261076785),
                f(346295418),
                f(1637246858),
                f(1607442625),
                f(777235843),
                f(194556598),
            ],
            [
                f(1410853257),
                f(1598063795),
                f(1111574219),
                f(1465562989),
                f(1102456901),
                f(1433687377),
                f(1376477958),
                f(1087266135),
            ],
            [
                f(278709284),
                f(1823086849),
                f(1969802325),
                f(633552560),
                f(1780238760),
                f(297873878),
                f(421105965),
                f(1357131680),
            ],
            [
                f(883611536),
                f(685305811),
                f(56966874),
                f(170904280),
                f(1353579462),
                f(1357636937),
                f(1565241058),
                f(209109553),
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
