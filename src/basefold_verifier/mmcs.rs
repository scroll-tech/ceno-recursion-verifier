// Note: check all XXX comments!

use std::marker::PhantomData;

use openvm_native_compiler::{asm::AsmConfig, prelude::*};
use openvm_native_recursion::hints::Hintable;
use openvm_stark_sdk::p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::FieldAlgebra;

use super::{structs::*, utils::*, hash::*};

pub type F = BabyBear;
pub type E = BinomialExtensionField<F, 4>;
pub type InnerConfig = AsmConfig<F, E>;

// XXX: Fill in MerkleTreeMmcs
pub struct MerkleTreeMmcs {
    pub hash: (),
    pub compress: (),
}

#[derive(Default, Clone)]
pub struct MerkleTreeMmcsVariables<C: Config> {
    pub hash: (),
    pub compress: (),
    _phantom: PhantomData<C>,
}

pub type MmcsCommitment = Hash<DIGEST_ELEMS>;
pub type MmcsProof = Vec<[F; DIGEST_ELEMS]>;
pub struct MmcsVerifierInput {
    pub commit: MmcsCommitment,
    pub dimensions: Vec<Dimensions>,
    pub index: usize,
    pub opened_values: Vec<Vec<F>>,
    pub proof: MmcsProof,
}

impl Hintable<InnerConfig> for MmcsVerifierInput {
    type HintVariable = MmcsVerifierInputVariable<InnerConfig>;

    fn read(builder: &mut Builder<InnerConfig>) -> Self::HintVariable {
        let commit = MmcsCommitment::read(builder);
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

pub type MmcsCommitmentVariable<C> = HashVariable<C>;
pub type MmcsProofVariable<C> = Array<C, Array<C, Felt<<C as Config>::F>>>;
#[derive(DslVariable, Clone)]
pub struct MmcsVerifierInputVariable<C: Config> {
    pub commit: MmcsCommitmentVariable<C>,
    pub dimensions: Array<C, DimensionsVariable<C>>,
    pub index: Var<C::N>,
    pub opened_values: Array<C, Array<C, Felt<C::F>>>,
    pub proof: MmcsProofVariable<C>,
}

pub(crate) fn mmcs_verify_batch<C: Config>(
    builder: &mut Builder<C>,
    _mmcs: MerkleTreeMmcsVariables<C>, // self
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
        let max_height_plus_one: Var<C::N> = builder.eval(max_height + Usize::from(1));
        builder.assert_less_than_slow_small_rhs(next_height, max_height_plus_one);
    });

    // Verify correspondence between log_h and h
    let log_max_height = builder.hint_var();
    let log_max_height_minus_1: Var<C::N> = builder.eval(log_max_height - Usize::from(1));
    let purported_max_height_lower_bound: Var<C::N> = pow_2(builder, log_max_height_minus_1);
    let two: Var<C::N> = builder.constant(C::N::TWO);
    let purported_max_height_upper_bound: Var<C::N> = builder.eval(purported_max_height_lower_bound * two);
    builder.assert_less_than_slow_small_rhs(purported_max_height_lower_bound, max_height);
    builder.assert_less_than_slow_small_rhs(max_height, purported_max_height_upper_bound);
    builder.assert_usize_eq(input.proof.len(), log_max_height);

    // Nondeterministically supplies:
    // 1. num_unique_height: number of different heights
    // 2. height_order: after sorting by decreasing height, the original index of each entry
    // To ensure that height_order represents sorted index, assert that
    // 1. It has the same length as input.dimensions (checked by requesting num_dims hints)
    // 2. It does not contain the same index twice (checked via a correspondence array)
    // 3. Indexed heights are sorted in decreasing order
    // While checking, record:
    // 1. unique_height_count: for each unique height, number of dimensions of that height
    let num_unique_height = builder.hint_var();
    let unique_height_count = builder.dyn_array(num_unique_height);
    let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let height_sort_surjective: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(num_dims.clone());
    builder.range(0, num_dims.clone()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        builder.set(&height_sort_surjective, i, zero.clone());
    });

    let height_order = builder.dyn_array(num_dims.clone());
    let next_order = builder.hint_var();
    // Check surjection
    let surjective = builder.get(&height_sort_surjective, next_order);
    builder.assert_ext_eq(surjective, zero.clone());
    builder.set(&height_sort_surjective, next_order, one.clone());
    builder.set_value(&height_order, 0, next_order);
    let last_height = builder.get(&input.dimensions, next_order).height;
    
    let last_unique_height_index: Var<C::N> = builder.eval(Usize::from(0));
    let last_unique_height_count: Var<C::N> = builder.eval(Usize::from(1));
    builder.range(1, num_dims).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let next_order = builder.hint_var();
        // Check surjection
        let surjective = builder.get(&height_sort_surjective, next_order);
        builder.assert_ext_eq(surjective, zero.clone());
        builder.set(&height_sort_surjective, next_order, one.clone());
        // Check height
        let next_height = builder.get(&input.dimensions, next_order).height;
        builder.if_eq(last_height, next_height).then(|builder| {
            // next_height == last_height
            builder.assign(&last_unique_height_count, last_unique_height_count + Usize::from(1));
        });
        builder.if_ne(last_height, next_height).then(|builder| {
            // next_height < last_height
            builder.assert_less_than_slow_small_rhs(next_height, last_height);
            
            // Update unique_height_count
            builder.set(&unique_height_count, last_unique_height_index, last_unique_height_count);
            builder.assign(&last_height, next_height);
            builder.assign(&last_unique_height_index, last_unique_height_index + Usize::from(1));
            builder.assign(&last_unique_height_count, Usize::from(1));
        });

        builder.set_value(&height_order, i, next_order);
    });

    // Final check on num_unique_height and unique_height_count
    builder.set(&unique_height_count, last_unique_height_index, last_unique_height_count);
    builder.assign(&last_unique_height_index, last_unique_height_index + Usize::from(1));
    builder.assert_var_eq(last_unique_height_index, num_unique_height);

    // First padded_height
    let first_order = builder.get(&height_order, 0);
    let first_height = builder.get(&input.dimensions, first_order).height;
    let curr_height_padded = next_power_of_two(builder, first_height);

    // Construct root through hashing
    let root_dims_count: Var<C::N> = builder.get(&unique_height_count, 0);
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
    let next_height_padded: Var<C::N> = builder.eval(Usize::from(0));
    builder.if_ne(num_unique_height, Usize::from(1)).then(|builder| {
        let next_height = builder.get(&input.dimensions, next_unique_height_count).height;
        let tmp_next_height_padded = next_power_of_two(builder, next_height);
        builder.assign(&next_height_padded, tmp_next_height_padded);
    });
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
            builder.if_ne(next_unique_height_index, num_unique_height).then(|builder| {
                let next_height = builder.get(&input.dimensions, next_unique_height_count).height;
                let next_tmp_height_padded = next_power_of_two(builder, next_height);
                builder.assign(&next_height_padded, next_tmp_height_padded);
            });
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
    use crate::basefold_verifier::structs::Dimensions;

    use super::{mmcs_verify_batch, MmcsCommitment, InnerConfig, MmcsVerifierInput};

    #[allow(dead_code)]
    pub fn build_mmcs_verify_batch() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        // OpenVM DSL
        let mut builder = AsmBuilder::<F, EF>::default();

        // Witness inputs
        let mmcs_self = Default::default();
        let mmcs_input = MmcsVerifierInput::read(&mut builder);
        mmcs_verify_batch(&mut builder, mmcs_self, mmcs_input);
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
            ]
        };
        let dimensions = vec![
            Dimensions { width: 8, height: 1 },
            Dimensions { width: 8, height: 1 },
            Dimensions { width: 8, height: 70 },
        ];
        let index = 6;
        let opened_values = vec![
            vec![f(774319227), f(1631186743), f(254325873), f(504149682), f(239740532), f(1126519109), f(1044404585), f(1274764277)],
            vec![f(1486505160), f(631183960), f(329388712), f(1934479253), f(115532954), f(1978455077), f(66346996), f(821157541)],
            vec![f(149196326), f(1186650877), f(1970038391), f(1893286029), f(1249658956), f(1618951617), f(419030634), f(1967997848)],
        ];
        let proof = vec![
            [f(845920358), f(1201648213), f(1087654550), f(264553580), f(633209321), f(877945079), f(1674449089), f(1062812099)],
            [f(5498027), f(1901489519), f(179361222), f(41261871), f(1546446894), f(266690586), f(1882928070), f(844710372)],
            [f(721245096), f(388358486), f(1443363461), f(1349470697), f(253624794), f(1359455861), f(237485093), f(1955099141)],
            [f(1816731864), f(402719753), f(1972161922), f(693018227), f(1617207065), f(1848150948), f(360933015), f(669793414)],
            [f(1746479395), f(457185725), f(1263857148), f(328668702), f(1743038915), f(582282833), f(927410326), f(376217274)],
            [f(1146845382), f(1117439420), f(1622226137), f(1449227765), f(138752938), f(1251889563), f(1266915653), f(267248408)],
            [f(1992750195), f(1604624754), f(1748646393), f(1777984113), f(861317745), f(564150089), f(1371546358), f(460033967)],
        ];
        let mmcs_input = MmcsVerifierInput {
            commit,
            dimensions,
            index,
            opened_values,
            proof,
        };
        witness_stream.extend(mmcs_input.write());
        // max_height
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&70));
        // log_max_height
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&7));
        // num_unique_height
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&2));
        // height_order
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&2));
        // height_order
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
        // height_order
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&1));
        // curr_height_log
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&6));
        // root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1782972889)));
        // root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(279434715)));
        // root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1209301918)));
        // root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1853868602)));
        // root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(883945353)));
        // root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(368353728)));
        // root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1699837443)));
        // root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(908962698)));
        // next_height_log
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
        // next_bit
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(271352274)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1918158485)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1538604111)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1122013445)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1844193149)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(501326061)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1508959271)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1549189152)));
        // next_curr_height_padded
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&64));
        // next_bit
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&1));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(222162520)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(785634830)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1461778378)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(836284568)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1141654637)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1339589042)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1081824021)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(698316542)));
        // next_curr_height_padded
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&32));
        // next_bit
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&1));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(567517164)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(915833994)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(621327606)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(476128789)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1976747536)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1385950652)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1416073024)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(862764478)));
        // next_curr_height_padded
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&16));
        // next_bit
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(822965313)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1036402058)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(117603799)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1087591966)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(443405499)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1334745091)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(901165815)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1187124281)));
        // next_curr_height_padded
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&8));
        // next_bit
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(875508647)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1313410483)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(355713834)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1976667383)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1804021525)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(294385081)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(669164730)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1187763617)));
        // next_curr_height_padded
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&4));
        // next_bit
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1992024140)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(439080849)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1032272714)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1304584689)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1795447062)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(859522945)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1661892383)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1980559722)));
        // next_curr_height_padded
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&2));
        // next_bit
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&0));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1121119596)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(369487248)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(834451573)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1120744826)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(758930984)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(632316631)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1593276657)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(507031465)));
        // next_curr_height_padded
        witness_stream.extend(<usize as Hintable<InnerConfig>>::write(&1));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1715944678)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1204294900)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(59582177)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(320945505)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1470843790)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(1773915204)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(380281369)));
        // new_root
        witness_stream.extend(<F as Hintable<InnerConfig>>::write(&F::from_canonical_usize(383365269)));

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