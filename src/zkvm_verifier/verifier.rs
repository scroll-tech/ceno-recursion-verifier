use openvm_native_compiler::prelude::*;
use super::binding::ZKVMProofInputVariable;
use openvm_native_recursion::challenger::ChallengerVariable;

pub fn verify_zkvm_proof<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    zkvm_proof_input: ZKVMProofInputVariable<C>,
) {
    // TODO
}