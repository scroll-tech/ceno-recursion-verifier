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

pub fn pow_2<C: Config>(
    builder: &mut Builder<C>,
    exponent: Var<C::N>,
) -> Var<C::N> {
    let two: Var<C::N> = builder.constant(C::N::from_canonical_usize(2));
    pow(builder, two, exponent)
}

// XXX: Equally outrageously inefficient
pub fn next_power_of_two<C: Config>(
    builder: &mut Builder<C>,
    value: Var<C::N>,
) -> Var<C::N> {
    // Non-deterministically supply the exponent n such that
    // 2^n < v <= 2^{n+1}
    let n: Var<C::N> = builder.hint_var();
    let ret = pow_2(builder, n);
    builder.assert_less_than_slow_bit_decomp(ret, value);
    let two: Var<C::N> = builder.constant(C::N::from_canonical_usize(2));
    builder.assign(&ret, ret * two);
    let ret_plus_one = builder.eval(ret.clone() + Usize::from(1));
    builder.assert_less_than_slow_bit_decomp(value, ret_plus_one);
    ret
}