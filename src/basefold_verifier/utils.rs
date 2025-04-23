use openvm_native_compiler::ir::*;
use p3_field::FieldAlgebra;

// XXX: more efficient pow implementation
pub fn pow<C: Config>(
    builder: &mut Builder<C>,
    base: Var<C::N>,
    exponent: Var<C::N>,
) -> Var<C::N> {
    let value: Var<C::N> = builder.constant(C::N::ONE);
    builder.range(0, exponent).for_each(|_, builder| {
        builder.assign(&value, value * base);
    });
    value
}