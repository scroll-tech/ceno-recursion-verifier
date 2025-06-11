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
    /// https://github.com/Jiangkm3/Plonky3
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
                f(1680031158),
                f(1530464150),
                f(442938890),
                f(1915006716),
                f(1586505947),
                f(567492512),
                f(78546285),
                f(122995307),
            ],
        };
        let dimensions = vec![7, 1, 1];
        let index = 6;
        let opened_values = vec![
            vec![
                f(960601660),
                f(1192659670),
                f(1578824022),
                f(144975148),
                f(1177686049),
                f(1685481888),
                f(743505857),
                f(279845322),
            ],
            vec![
                f(1097397493),
                f(887027944),
                f(980566941),
                f(1572544252),
                f(597464337),
                f(396275662),
                f(819983943),
                f(1414101776),
            ],
            vec![
                f(1198674230),
                f(1468910507),
                f(453723651),
                f(1663663454),
                f(1329515200),
                f(85748328),
                f(660749682),
                f(2010576218),
            ],
        ];
        let proof = vec![
            [
                f(1334234643),
                f(588743138),
                f(1420323154),
                f(735905746),
                f(495445129),
                f(1544297066),
                f(1062502165),
                f(1322613112),
            ],
            [
                f(1882651949),
                f(572080113),
                f(152683464),
                f(14829179),
                f(2006886314),
                f(133167211),
                f(745961821),
                f(1681442214),
            ],
            [
                f(1157629442),
                f(1439934290),
                f(1996877031),
                f(124179660),
                f(1785268039),
                f(1531335481),
                f(172600848),
                f(717903005),
            ],
            [
                f(1686363855),
                f(364530059),
                f(127515555),
                f(1313410702),
                f(1401384952),
                f(1701278059),
                f(1934144441),
                f(120278217),
            ],
            [
                f(1819568176),
                f(1745841261),
                f(211079785),
                f(941471227),
                f(981333411),
                f(1989076935),
                f(1836318175),
                f(421578048),
            ],
            [
                f(1722987777),
                f(675846798),
                f(583189961),
                f(1322278935),
                f(575957852),
                f(238416543),
                f(382123109),
                f(1551859129),
            ],
            [
                f(1129037404),
                f(615143781),
                f(1557998657),
                f(978670363),
                f(325351741),
                f(1598221158),
                f(60344644),
                f(1792544175),
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
