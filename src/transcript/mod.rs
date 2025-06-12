use ff_ext::{BabyBearExt4, ExtensionField as CenoExtensionField, SmallField};
use openvm_native_compiler::prelude::*;
use openvm_native_recursion::challenger::ChallengerVariable;
use p3_field::FieldAlgebra;
use openvm_native_recursion::challenger::{
    duplex::DuplexChallengerVariable, CanObserveVariable, FeltChallenger,
};

pub fn transcript_observe_label<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    label: &[u8],
) {
    let label_f = <BabyBearExt4 as CenoExtensionField>::BaseField::bytes_to_field_elements(label);
    for n in label_f {
        let f: Felt<C::F> = builder.constant(C::F::from_canonical_u64(n.to_canonical_u64()));
        challenger.observe(builder, f);
    }
}
