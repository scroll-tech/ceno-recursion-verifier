// Note: check all XXX comments!

use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;

use super::{binding::*, utils::*, hash::*};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

type Commitment = Hash<DIGEST_ELEMS>;
type MmcsProof = Vec<[F; DIGEST_ELEMS]>;
pub struct MmcsVerifierInput {
    pub commit: Commitment,
    pub dimensions: Vec<Dimensions>,
    pub index: usize,
    pub opened_values: Vec<Vec<F>>,
    pub proof: MmcsProof,
}

impl Hintable<InnerConfig> for MmcsVerifierInput {
    type HintVariable = MmcsVerifierInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let commit = Commitment::read(builder);
        let dimensions = Vec::<Dimensions>::read(builder);
        let index = usize::read(builder);
        let opened_values = Vec::<Vec::<F>>::read(builder);
        let proof = Vec::<Vec::<F>>::read(builder);

        MmcsVerifierInputVariable {
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
        stream.extend(self.proof.iter().map(|p| p.to_vec()).collect::<Vec<_>>().write());
        stream
    }
}

type CommitmentVariable<C> = HashVariable<C>;
type MmcsProofVariable<C> = Array<C, Array<C, Felt<<C as Config>::F>>>;
#[derive(DslVariable, Clone)]
pub struct MmcsVerifierInputVariable<C: Config> {
    pub commit: CommitmentVariable<C>,
    pub dimensions: Array<C, DimensionsVariable<C>>,
    pub index: Var<C::N>,
    pub opened_values: Array<C, Array<C, Felt<C::F>>>,
    pub proof: MmcsProofVariable<C>,
}

pub(crate) fn mmcs_verify_batch<C: Config>(
    builder: &mut Builder<C>,
    input: MmcsVerifierInputVariable<C>,
) {
    // Check that the openings have the correct shape.
    let num_dims = input.dimensions.len();
    // Assert dimensions is not empty
    builder.assert_nonzero(&num_dims);
    builder.assert_usize_eq(num_dims.clone(), input.opened_values.len());

    // TODO: Disabled for now since TwoAdicFriPcs and CirclePcs currently pass 0 for width.

    // TODO: Disabled for now, CirclePcs sometimes passes a height that's off by 1 bit.
    // Nondeterministically supplies max_height
    let max_height = builder.hint_var();
    builder.range(0, input.dimensions.len()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let next_height = builder.get(&input.dimensions, i).height;
        let max_height_plus_one = builder.eval(max_height + Usize::from(1));
        builder.assert_less_than_slow_bit_decomp(next_height, max_height_plus_one);
    });

    // Verify correspondence between log_h and h
    let log_max_height = builder.hint_var();
    let purported_max_height = pow_2(builder, log_max_height);
    builder.assert_var_eq(purported_max_height, max_height);
    builder.assert_usize_eq(input.proof.len(), log_max_height);

    // Nondeterministically supplies:
    // 1. num_unique_height: number of different heights
    // 2. unique_height_count: for each unique height, number of dimensions of that height
    // 3. height_order: after sorting by decreasing height, the original index of each entry
    // 4. height_diff: whether the height of the sorted entry differ from the next. 0 - no diff; 1 - diff
    let num_unique_height = builder.hint_var();
    let unique_height_count = builder.dyn_array(num_unique_height);
    builder.range(0, num_unique_height).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let next_count = builder.hint_var();
        builder.set_value(&unique_height_count, i, next_count);
    });

    let height_order = builder.dyn_array(num_dims.clone());
    let height_diff = builder.dyn_array(num_dims.clone());
    let mut last_order = builder.hint_var();
    let mut last_diff = builder.hint_var();
    builder.set_value(&height_order, 0, last_order);
    builder.set_value(&height_diff, 0, last_diff);
    let mut last_height = builder.get(&input.dimensions, last_order).height;
    
    let curr_height_padded = next_power_of_two(builder, last_height);
    
    let last_unique_height_index: Var<C::N> = builder.eval(Usize::from(0));
    let last_unique_height_count: Var<C::N> = builder.eval(Usize::from(1));
    builder.range(1, num_dims).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let next_order = builder.hint_var();
        let next_diff = builder.hint_var();
        let next_height = builder.get(&input.dimensions, next_order).height;

        builder.if_eq(last_diff, Usize::from(0)).then(|builder| {
            // last_diff == 0 ==> next_height == last_height
            builder.assert_var_eq(last_height, next_height);
            builder.assign(&last_unique_height_count, last_unique_height_count + Usize::from(1));
        });
        builder.if_ne(last_diff, Usize::from(0)).then(|builder| {
            // last_diff != 0 ==> next_height < last_height
            builder.assert_less_than_slow_small_rhs(next_height, last_height);
            
            // Verify correctness of unique_height_count
            let purported_unique_height_count = builder.get(&unique_height_count, last_unique_height_index);
            builder.assert_var_eq(purported_unique_height_count, last_unique_height_count);
            builder.assign(&last_unique_height_index, last_unique_height_index + Usize::from(1));
            builder.assign(&last_unique_height_count, Usize::from(1));
        });

        last_order = next_order;
        last_diff = next_diff;
        builder.set_value(&height_order, i, last_order);
        builder.set_value(&height_diff, i, last_diff);
        last_height = next_height;
    });
    // Final check on num_unique_height and unique_height_count
    let purported_unique_height_count = builder.get(&unique_height_count, last_unique_height_index);
    builder.assert_var_eq(purported_unique_height_count, last_unique_height_count);
    builder.assign(&last_unique_height_index, last_unique_height_index + Usize::from(1));
    builder.assert_var_eq(last_unique_height_index, num_unique_height);

    // Construct root through hashing
    let root_dims_count = builder.get(&unique_height_count, 0);
    let root_values = builder.dyn_array(root_dims_count);
    builder.range(0, root_dims_count).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let index = builder.get(&height_order, i);
        let tmp = builder.get(&input.opened_values, index);
        builder.set_value(&root_values, i, tmp);
    });
    let root = hash_iter_slices(builder, root_values);

    // Index_pow and reassembled_index for bit split
    let index_pow: Var<C::N> = builder.eval(Usize::from(1));
    let reassembled_index: Var<C::N> = builder.eval(Usize::from(0));
    // next_height is the height of the next dim to be incorporated into root
    let next_unique_height_index: Var<C::N> = builder.eval(Usize::from(1));
    let next_unique_height_count: Var<C::N> = builder.eval(root_dims_count);
    let next_height = builder.get(&input.dimensions, next_unique_height_count).height;
    let next_height_padded = next_power_of_two(builder, next_height);
    builder.range(0, input.proof.len()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let sibling = builder.get(&input.proof, i);
        let two_var: Var<C::N> = builder.eval(Usize::from(2)); // XXX: is there a better way to do this?
        // Supply the next index bit as hint, assert that it is a bit
        let next_index_bit = builder.hint_var();
        builder.assert_var_eq(next_index_bit, next_index_bit * next_index_bit);
        builder.assign(&reassembled_index, reassembled_index + index_pow * next_index_bit);
        builder.assign(&index_pow, index_pow * two_var);

        // left, right
        let compress_elem = builder.dyn_array(2);
        builder.if_eq(next_index_bit, Usize::from(0)).then(|builder| {
            // root, sibling
            builder.set_value(&compress_elem, 0, root.clone());
            builder.set_value(&compress_elem, 0, sibling.clone());
        });
        builder.if_ne(next_index_bit, Usize::from(0)).then(|builder| {
            // sibling, root
            builder.set_value(&compress_elem, 0, sibling.clone());
            builder.set_value(&compress_elem, 0, root.clone());
        });
        let new_root = compress(builder, compress_elem);
        builder.assign(&root, new_root);

        // curr_height_padded >>= 1 given curr_height_padded is a power of two
        // Nondeterministically supply next_curr_height_padded
        let next_curr_height_padded = builder.hint_var();
        builder.assert_var_eq(next_curr_height_padded * two_var, curr_height_padded);
        builder.assign(&curr_height_padded, next_curr_height_padded);

        // determine whether next_height matches curr_height
        builder.if_eq(curr_height_padded, next_height_padded).then(|builder| {
            // hash opened_values of all dims of next_height to root
            let root_dims_count = builder.get(&unique_height_count, next_unique_height_index);
            let root_size: Var<C::N> = builder.eval(root_dims_count + Usize::from(1));
            let root_values = builder.dyn_array(root_size);
            builder.set_value(&root_values, 0, root.clone());
            builder.range(0, root_dims_count).for_each(|i_vec, builder| {
                let i = i_vec[0];
                let index = builder.get(&height_order, i);
                let tmp = builder.get(&input.opened_values, index);
                let j = builder.eval_expr(i + RVar::from(1));
                builder.set_value(&root_values, j, tmp);
            });
            let new_root = hash_iter_slices(builder, root_values);
            builder.assign(&root, new_root);

            // Update parameters
            builder.assign(&next_unique_height_count, next_unique_height_count + root_dims_count);
            builder.assign(&next_unique_height_index, next_unique_height_index + Usize::from(1));
            builder.if_eq(next_unique_height_index, num_unique_height).then(|builder| {
                builder.assign(&next_height_padded, Usize::from(0));
            });
            let next_height = builder.get(&input.dimensions, next_unique_height_count).height;
            let next_tmp_height_padded = next_power_of_two(builder, next_height);
            builder.assign(&next_height_padded, next_tmp_height_padded);
        });

    });
    builder.assert_var_eq(reassembled_index, input.index);
    builder.range(0, DIGEST_ELEMS).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let next_input = builder.get(&input.commit.value, i);
        let next_root = builder.get(&root, i);
        builder.assert_felt_eq(next_input, next_root);
    });
}

pub mod tests {
    use openvm_circuit::arch::{instructions::program::Program, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::AsmBuilder;
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
    use crate::basefold_verifier::{binding::Dimensions, hash::DIGEST_ELEMS};

    use super::{mmcs_verify_batch, Commitment, InnerConfig, MmcsVerifierInput};

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
        let commit = Commitment {
            value: [f(0); DIGEST_ELEMS]
        };
        let dimensions = vec![
            Dimensions { width: 9, height: 9 },
            Dimensions { width: 7, height: 7 },
            Dimensions { width: 5, height: 5 },
            Dimensions { width: 3, height: 3 },
        ];
        let opened_values = vec![
            vec![f(47), f(22), f(14), f(6)],
            vec![f(35), f(3), f(1)],
            vec![f(29), f(11), f(2)],
            vec![f(14), f(4)],
        ];
        let proof = vec![
            [f(47); 4],
            [f(35); 4],
            [f(29); 4],
            [f(14); 4],
        ];
        let mmcs_input = MmcsVerifierInput {
            commit,
            dimensions,
            index: 7,
            opened_values,
            proof,
        };
        witness_stream.extend(mmcs_input.write());
        // Hints
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&5));

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