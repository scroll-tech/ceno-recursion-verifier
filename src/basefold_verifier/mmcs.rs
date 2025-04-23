// Note: check all XXX comments!

use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::FieldAlgebra;

use super::{binding::*, utils::*};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

const DIGEST_ELEMS: usize = 4;

pub struct Hash<const DIGEST_ELEMS: usize> {
    pub value: [F; DIGEST_ELEMS],
}

impl Hintable<InnerConfig> for Hash<DIGEST_ELEMS> {
    type HintVariable = HashVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let value = builder.uninit_fixed_array(DIGEST_ELEMS);
        for i in 0..DIGEST_ELEMS {
            let tmp = F::read(builder);
            builder.set(&value, i, tmp);
        }

        HashVariable {
            value,
        }
    }

    fn write(&self) -> Vec<Vec<<InnerConfig as Config>::N>> {
        let mut stream = Vec::new();
        // Write out each entries
        for i in 0..DIGEST_ELEMS {
            stream.extend(self.value[i].write());
        }
        stream
    }
}

#[derive(DslVariable, Clone)]
pub struct HashVariable<C: Config> {
    pub value: Array<C, Felt<C::F>>,
}

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
    builder.assert_eq(input.dimensions.len(), input.opened_values.len());

    // TODO: Disabled for now since TwoAdicFriPcs and CirclePcs currently pass 0 for width.

    // TODO: Disabled for now, CirclePcs sometimes passes a height that's off by 1 bit.
    // Nondeterministically supply max_height and check
    let max_height = builder.hint_var();
    builder.range(0, input.dimensions.len()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let next_height = builder.get(&input.dimensions, i).height;
        let max_height_plus_one = builder.eval(max_height + Usize::from(1));
        builder.assert_less_than_slow_bit_decomp(next_height, max_height_plus_one);
    });

    // Verify correspondence between log_h and h
    let log_max_height = builder.hint_var();
    let two: Var<C::N> = builder.constant(C::N::from_canonical_usize(2));
    let purported_max_height = pow(builder, two, log_max_height);
    builder.assert_eq(purported_max_height, max_height);
    builder.assert_eq(input.proof.len(), log_max_height);


    let mut heights_tallest_first = dimensions
        .iter()
        .enumerate()
        .sorted_by_key(|(_, dims)| Reverse(dims.height))
        .peekable();

    let Some(mut curr_height_padded) = heights_tallest_first
        .peek()
        .map(|x| x.1.height.next_power_of_two())
    else {
        // dimensions is empty
        return Err(EmptyBatch);
    };

    let mut root = self.hash.hash_iter_slices(
        heights_tallest_first
            .peeking_take_while(|(_, dims)| {
                dims.height.next_power_of_two() == curr_height_padded
            })
            .map(|(i, _)| opened_values[i].as_slice()),
    );

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
