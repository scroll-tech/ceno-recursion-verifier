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
                f(1093866670),
                f(574851776),
                f(1247953105),
                f(1203327509),
                f(1533188113),
                f(685187947),
                f(1288273829),
                f(1115279794),
            ],
        };
        let dimensions = vec![7, 1, 1]; // The dimensions are logarithmic of the heights
        let index = 6;
        let opened_values = vec![
            vec![
                f(1900166735),
                f(489844155),
                f(447015069),
                f(1088472428),
                f(741990823),
                f(629716069),
                f(1813856950),
                f(993673429),
            ],
            vec![
                f(461805816),
                f(38690267),
                f(628409367),
                f(326210486),
                f(1399484986),
                f(1106048341),
                f(1653752726),
                f(1508026260),
            ],
            vec![
                f(1179435248),
                f(589758130),
                f(102692717),
                f(1240806078),
                f(1326867049),
                f(1843793614),
                f(1140390710),
                f(1590488665),
            ],
        ];
        let proof = vec![
            [
                f(296596654),
                f(678058943),
                f(1998719115),
                f(927782063),
                f(2012932188),
                f(651079256),
                f(106721600),
                f(1671237590),
            ],
            [
                f(1631182650),
                f(1639600768),
                f(451941478),
                f(204140132),
                f(471048369),
                f(277644394),
                f(1867343362),
                f(592993761),
            ],
            [
                f(138270113),
                f(983240556),
                f(868154296),
                f(1436014073),
                f(1333074616),
                f(74821565),
                f(220358401),
                f(494000015),
            ],
            [
                f(14047213),
                f(1523499359),
                f(1105004739),
                f(222898207),
                f(696072743),
                f(913719856),
                f(411499939),
                f(250843350),
            ],
            [
                f(1093746185),
                f(368171740),
                f(1405456697),
                f(103797304),
                f(1561352958),
                f(90154716),
                f(154291788),
                f(1719437900),
            ],
            [
                f(1988708734),
                f(580748340),
                f(1935380041),
                f(236593751),
                f(230821177),
                f(232517197),
                f(451633153),
                f(423978451),
            ],
            [
                f(319678818),
                f(1076607925),
                f(615756225),
                f(508582464),
                f(991750834),
                f(1175188849),
                f(1143234948),
                f(1588353893),
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
