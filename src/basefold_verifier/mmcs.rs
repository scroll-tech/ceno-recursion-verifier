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
type Proof = Vec<[F; DIGEST_ELEMS]>;
pub struct MmcsVerifierInput {
    pub commit: Commitment,
    pub dimensions: Vec<Dimensions>,
    pub index: usize,
    pub opened_values: Vec<Vec<F>>,
    pub proof: Proof,
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
type ProofVariable<C> = Array<C, Array<C, Felt<<C as Config>::F>>>;
#[derive(DslVariable, Clone)]
pub struct MmcsVerifierInputVariable<C: Config> {
    pub commit: CommitmentVariable<C>,
    pub dimensions: Array<C, DimensionsVariable<C>>,
    pub index: Var<C::N>,
    pub opened_values: Array<C, Array<C, Felt<C::F>>>,
    pub proof: ProofVariable<C>,
}

pub(crate) fn verify_batch<C: Config>(
    builder: &mut Builder<C>,
    input: MmcsVerifierInputVariable<C>,
) {
    // Check that the openings have the correct shape.
    let num_dims = input.dimensions.len();
    // Assert dimensions is not empty
    builder.assert_nonzero(&num_dims);
    builder.assert_eq(num_dims.clone(), input.opened_values.len());

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
    builder.assert_eq(purported_max_height, max_height);
    builder.assert_eq(input.proof.len(), log_max_height);

    // Nondeterministically supplies:
    // 1. num_unique_height: number of different heights
    // 2. unique_height_count: for each unique height, number of dimensions of that height
    // 3. height_order: after sorting by decreasing height, the original index of each entry
    // 4. height_diff: whether the height of the sorted entry differ from the next. 0 - no diff; 1 - diff
    let num_unique_height = builder.hint_var();
    let unique_height_count = builder.dyn_array(num_unique_height);
    builder.range(0, num_unique_height).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let mut next_count = builder.hint_var();
        builder.set_value(&unique_height_count, i, next_count);
    });

    let height_order = builder.dyn_array(num_dims);
    let height_diff = builder.dyn_array(num_dims);
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
        let mut next_order = builder.hint_var();
        let mut next_diff = builder.hint_var();
        let next_height = builder.get(&input.dimensions, next_order).height;

        builder.if_eq(last_diff, Usize::from(0)).then(|builder| {
            // last_diff == 0 ==> next_height == last_height
            builder.assert_eq(last_height, next_height);
            builder.assign(&last_unique_height_count, last_unique_height_count + Usize::from(1));
        });
        builder.if_ne(last_diff, Usize::from(0)).then(|builder| {
            // last_diff != 0 ==> next_height < last_height
            builder.assert_less_than_slow_small_rhs(next_height, last_height);
            
            // Verify correctness of unique_height_count
            let purported_unique_height_count = builder.get(&unique_height_count, last_unique_height_index);
            builder.assert_eq(purported_unique_height_count, last_unique_height_count);
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
    builder.assert_eq(purported_unique_height_count, last_unique_height_count);
    builder.assign(&last_unique_height_index, last_unique_height_index + Usize::from(1));
    builder.assert_eq(last_unique_height_index, num_unique_height);

    // Construct root through hashing
    let root_dims_count = builder.get(&unique_height_count, 0);
    let root_values = builder.dyn_array(root_dims_count);
    builder.range(0, root_dims_count).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let tmp = builder.get(&input.opened_values, i);
        builder.set_value(&root_values, i, tmp);
    });
    let root = hash_iter_slices(builder, root_values);

    builder.range(0, input.proof.len()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        
    });

    for &sibling in proof {
        let (left, right) = if index & 1 == 0 {
            (root, sibling)
        } else {
            (sibling, root)
        };

        root = self.compress.compress([left, right]);
        index >>= 1;
        curr_height_padded >>= 1;

        let next_height = heights_tallest_first
            .peek()
            .map(|(_, dims)| dims.height)
            .filter(|h| h.next_power_of_two() == curr_height_padded);
        if let Some(next_height) = next_height {
            let next_height_openings_digest = self.hash.hash_iter_slices(
                heights_tallest_first
                    .peeking_take_while(|(_, dims)| dims.height == next_height)
                    .map(|(i, _)| opened_values[i].as_slice()),
            );

            root = self.compress.compress([root, next_height_openings_digest]);
        }
    }

    if commit == &root {
        Ok(())
    } else {
        Err(RootMismatch)
    }
}
