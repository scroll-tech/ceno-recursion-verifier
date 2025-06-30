use crate::tower_verifier::binding::PointAndEvalVariable;
use crate::zkvm_verifier::binding::ZKVMOpcodeProofInputVariable;
use ceno_mle::expression::{Expression, Fixed, Instance};
use ceno_zkvm::structs::{ChallengeId, WitnessId};
use ff_ext::ExtensionField;
use ff_ext::{BabyBearExt4, SmallField};
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::ChallengerVariable;
use openvm_native_recursion::challenger::{
    duplex::DuplexChallengerVariable, CanObserveVariable, FeltChallenger,
};
use itertools::Either;
use p3_field::{FieldAlgebra, FieldExtensionAlgebra};
type E = BabyBearExt4;
const HASH_RATE: usize = 8;

pub fn _print_ext_arr<C: Config>(builder: &mut Builder<C>, arr: &Array<C, Ext<C::F, C::EF>>) {
    iter_zip!(builder, arr).for_each(|ptr_vec, builder| {
        let e = builder.iter_ptr_get(arr, ptr_vec[0]);
        builder.print_e(e);
    });
}

pub fn print_felt_arr<C: Config>(builder: &mut Builder<C>, arr: &Array<C, Felt<C::F>>) {
    iter_zip!(builder, arr).for_each(|ptr_vec, builder| {
        let f = builder.iter_ptr_get(arr, ptr_vec[0]);
        builder.print_f(f);
    });
}

pub fn _print_usize_arr<C: Config>(builder: &mut Builder<C>, arr: &Array<C, Usize<C::N>>) {
    iter_zip!(builder, arr).for_each(|ptr_vec, builder| {
        let n = builder.iter_ptr_get(arr, ptr_vec[0]);
        builder.print_v(n.get_var());
    });
}

pub unsafe fn exts_to_felts<C: Config>(
    builder: &mut Builder<C>,
    exts: &Array<C, Ext<C::F, C::EF>>,
) -> Array<C, Felt<C::F>> {
    assert!(
        matches!(exts, Array::Dyn(_, _)),
        "Expected dynamic array of Exts"
    );
    let f_len: Usize<C::N> = builder.eval(exts.len() * Usize::from(C::EF::D));
    let f_arr: Array<C, Felt<C::F>> = Array::Dyn(exts.ptr(), f_len);
    f_arr
}

pub fn challenger_multi_observe<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    arr: &Array<C, Felt<C::F>>,
) {
    let next_input_ptr =
        builder.poseidon2_multi_observe(&challenger.sponge_state, challenger.input_ptr, &arr);
    builder.assign(
        &challenger.input_ptr,
        challenger.io_empty_ptr + next_input_ptr.clone(),
    );
    builder.if_ne(next_input_ptr, Usize::from(0)).then_or_else(
        |builder| {
            builder.assign(&challenger.output_ptr, challenger.io_empty_ptr);
        },
        |builder| {
            builder.assign(&challenger.output_ptr, challenger.io_full_ptr);
        },
    );
}

pub fn is_smaller_than<C: Config>(
    builder: &mut Builder<C>,
    left: RVar<C::N>,
    right: RVar<C::N>,
) -> RVar<C::N> {
    let res: Felt<C::F> = builder.constant(C::F::ZERO);
    let one: Felt<C::F> = builder.constant(C::F::ONE);

    builder.range(0, right).for_each(|idx_vec, builder| {
        builder.if_eq(left, idx_vec[0]).then(|builder| {
            builder.assign(&res, res + one);
        });
    });
    let v = builder.cast_felt_to_var(res);

    RVar::from(v)
}

pub fn evaluate_at_point<C: Config>(
    builder: &mut Builder<C>,
    evals: &Array<C, Ext<C::F, C::EF>>,
    point: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<C::F, C::EF> {
    // TODO: Dynamic length
    // TODO: Sanity checks
    let left = builder.get(&evals, 0);
    let right = builder.get(&evals, 1);
    let r = builder.get(point, 0);

    builder.eval(r * (right - left) + left)
}

pub fn dot_product<C: Config>(
    builder: &mut Builder<C>,
    a: &Array<C, Ext<C::F, C::EF>>,
    b: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<<C as Config>::F, <C as Config>::EF> {
    let acc: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);

    iter_zip!(builder, a, b).for_each(|ptr_vec, builder| {
        let v_a = builder.iter_ptr_get(&a, ptr_vec[0]);
        let v_b = builder.iter_ptr_get(&b, ptr_vec[1]);
        builder.assign(&acc, acc + v_a * v_b);
    });

    acc
}

pub fn fixed_dot_product<C: Config>(
    builder: &mut Builder<C>,
    a: &[Ext<C::F, C::EF>],
    b: &Array<C, Ext<C::F, C::EF>>,
    zero: Ext<C::F, C::EF>,
) -> Ext<<C as Config>::F, <C as Config>::EF> {
    // simple trick to prefer AddE(1 cycle) than AddEI(4 cycles)
    let acc: Ext<C::F, C::EF> = builder.eval(zero + zero);

    for (i, va) in a.iter().enumerate() {
        let vb = builder.get(b, i);
        builder.assign(&acc, acc + *va * vb);
    }

    acc
}

pub fn reverse<C: Config, T: MemVariable<C>>(
    builder: &mut Builder<C>,
    arr: &Array<C, T>,
) -> Array<C, T> {
    let len = arr.len();
    let res: Array<C, T> = builder.dyn_array(len.clone());
    builder.range(0, len.clone()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let rev_i: RVar<_> = builder.eval_expr(len.clone() - i - RVar::from(1));

        let el = builder.get(arr, i);
        builder.set(&res, rev_i, el);
    });

    res
}

pub fn concat<C: Config, T: MemVariable<C>>(
    builder: &mut Builder<C>,
    a: &Array<C, T>,
    b: &Array<C, T>,
) -> Array<C, T> {
    let res_len: Usize<C::N> = builder.eval(a.len() + b.len());
    let res: Array<C, T> = builder.dyn_array(res_len);

    builder.range(0, a.len()).for_each(|idx_vec, builder| {
        let a_v = builder.get(&a, idx_vec[0]);
        builder.set(&res, idx_vec[0], a_v);
    });
    builder.range(0, b.len()).for_each(|idx_vec, builder| {
        let b_v = builder.get(&b, idx_vec[0]);
        let res_idx: Usize<C::N> = builder.eval(a.len() + idx_vec[0]);
        builder.set(&res, res_idx, b_v);
    });

    res
}

pub fn gen_idx_arr<C: Config>(builder: &mut Builder<C>, len: Usize<C::N>) -> Array<C, Usize<C::N>> {
    let res: Array<C, Usize<C::N>> = builder.dyn_array(len.clone());

    builder.range(0, len).for_each(|idx_vec, builder| {
        let u: Usize<C::N> = builder.eval(idx_vec[0]);
        builder.set(&res, idx_vec[0], u);
    });

    res
}

// Evaluate eq polynomial.
pub fn eq_eval<C: Config>(
    builder: &mut Builder<C>,
    x: &Array<C, Ext<C::F, C::EF>>,
    y: &Array<C, Ext<C::F, C::EF>>,
    one: Ext<C::F, C::EF>,
    zero: Ext<C::F, C::EF>,
) -> Ext<C::F, C::EF> {
    let acc: Ext<C::F, C::EF> = builder.eval(zero + one); // simple trick to use AddE

    iter_zip!(builder, x, y).for_each(|idx_vec, builder| {
        let ptr_x = idx_vec[0];
        let ptr_y = idx_vec[1];
        let v_x = builder.iter_ptr_get(&x, ptr_x);
        let v_y = builder.iter_ptr_get(&y, ptr_y);
        // x*y + (1-x)*(1-y)
        let xi_yi: Ext<C::F, C::EF> = builder.eval(v_x * v_y);
        let new_acc: Ext<C::F, C::EF> = builder.eval(acc * (xi_yi + xi_yi - v_x - v_y + one));
        builder.assign(&acc, new_acc);
    });

    acc
}

// Multiply all elements in the Array
pub fn product<C: Config>(
    builder: &mut Builder<C>,
    arr: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<C::F, C::EF> {
    let acc = builder.constant(C::EF::ONE);
    iter_zip!(builder, arr).for_each(|idx_vec, builder| {
        let el = builder.iter_ptr_get(arr, idx_vec[0]);
        builder.assign(&acc, acc * el);
    });

    acc
}

// Add all elements in the Array
pub fn sum<C: Config>(
    builder: &mut Builder<C>,
    arr: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<C::F, C::EF> {
    let acc = builder.constant(C::EF::ZERO);
    iter_zip!(builder, arr).for_each(|idx_vec, builder| {
        let el = builder.iter_ptr_get(arr, idx_vec[0]);
        builder.assign(&acc, acc + el);
    });

    acc
}

// Extend an array by one element
pub fn extend<C: Config>(
    builder: &mut Builder<C>,
    arr: &Array<C, Ext<C::F, C::EF>>,
    elem: &Ext<C::F, C::EF>,
) -> Array<C, Ext<C::F, C::EF>> {
    let new_len: Var<C::N> = builder.eval(arr.len() + C::N::ONE);
    let out = builder.dyn_array(new_len);

    builder.range(0, arr.len()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let val = builder.get(arr, i);
        builder.set_value(&out, i, val);
    });
    builder.set_value(&out, arr.len(), elem.clone());

    out
}

// Generate alpha power challenges
pub fn gen_alpha_pows<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    alpha_len: Usize<<C as Config>::N>,
) -> Array<C, Ext<C::F, C::EF>> {
    let alpha = challenger.sample_ext(builder);

    // let alpha_felts = builder.ext2felt(alpha);
    // challenger.observe_slice(builder, alpha_felts);

    let alpha_pows: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(alpha_len);
    let prev: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    iter_zip!(builder, alpha_pows).for_each(|ptr_vec: Vec<RVar<<C as Config>::N>>, builder| {
        let ptr = ptr_vec[0];
        builder.iter_ptr_set(&alpha_pows, ptr, prev.clone());
        builder.assign(&prev, prev * alpha);
    });
    alpha_pows
}

/// This is to compute a variant of eq(\mathbf{x}, \mathbf{y}) for indices in
/// [0..=max_idx]. Specifically, it is an MLE of the following vector:
///     partial_eq_{\mathbf{x}}(\mathbf{y})
///         = \sum_{\mathbf{b}=0}^{max_idx} \prod_{i=0}^{n-1} (x_i y_i b_i + (1 - x_i)(1 - y_i)(1 - b_i))
pub fn eq_eval_less_or_equal_than<C: Config>(
    builder: &mut Builder<C>,
    _challenger: &mut DuplexChallengerVariable<C>,
    opcode_proof: &ZKVMOpcodeProofInputVariable<C>,
    a: &Array<C, Ext<C::F, C::EF>>,
    b: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<C::F, C::EF> {
    let eq_bit_decomp: Array<C, Felt<C::F>> = opcode_proof
        .num_instances_minus_one_bit_decomposition
        .slice(builder, 0, b.len());

    let one_ext: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    let rp_len = builder.eval_expr(RVar::from(b.len()) + RVar::from(1));
    let running_product: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(rp_len);
    builder.set(&running_product, 0, one_ext);

    builder.range(0, b.len()).for_each(|idx_vec, builder| {
        let a_i = builder.get(a, idx_vec[0]);
        let b_i = builder.get(b, idx_vec[0]);
        let v = builder.get(&running_product, idx_vec[0]);
        let next_v: Ext<C::F, C::EF> =
            builder.eval(v * (a_i * b_i + (one_ext - a_i) * (one_ext - b_i)));
        let next_idx = builder.eval_expr(idx_vec[0] + RVar::from(1));
        builder.set(&running_product, next_idx, next_v);
    });

    let running_product2: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(rp_len);
    builder.set(&running_product2, b.len(), one_ext);

    let eq_bit_decomp_rev = reverse(builder, &eq_bit_decomp);
    let idx_arr = gen_idx_arr(builder, b.len());
    let idx_arr_rev = reverse(builder, &idx_arr);
    builder.assert_usize_eq(eq_bit_decomp_rev.len(), idx_arr_rev.len());

    iter_zip!(builder, idx_arr_rev, eq_bit_decomp_rev).for_each(|ptr_vec, builder| {
        let i = builder.iter_ptr_get(&idx_arr_rev, ptr_vec[0]);
        let bit = builder.iter_ptr_get(&eq_bit_decomp_rev, ptr_vec[1]);
        let bit_ext = builder.ext_from_base_slice(&[bit]);
        let last_idx = builder.eval_expr(i.clone() + RVar::from(1));

        let v = builder.get(&running_product2, last_idx);
        let a_i = builder.get(a, i.clone());
        let b_i = builder.get(b, i.clone());

        let next_v: Ext<C::F, C::EF> = builder.eval(
            v * (a_i * b_i * bit_ext + (one_ext - a_i) * (one_ext - b_i) * (one_ext - bit_ext)),
        );
        builder.set(&running_product2, i, next_v);
    });

    // Here is an example of how this works:
    // Suppose max_idx = (110101)_2
    // Then ans = eq(a, b)
    //          - eq(11011, a[1..6], b[1..6])eq(a[0..1], b[0..1])
    //          - eq(111, a[3..6], b[3..6])eq(a[0..3], b[0..3])
    let ans = builder.get(&running_product, b.len());
    builder.range(0, b.len()).for_each(|idx_vec, builder| {
        let bit = builder.get(&eq_bit_decomp, idx_vec[0]);
        let bit_rvar = RVar::from(builder.cast_felt_to_var(bit));

        builder.if_ne(bit_rvar, RVar::from(1)).then(|builder| {
            let next_idx = builder.eval_expr(idx_vec[0] + RVar::from(1));
            let v1 = builder.get(&running_product, idx_vec[0]);
            let v2 = builder.get(&running_product2, next_idx);
            let a_i = builder.get(a, idx_vec[0]);
            let b_i = builder.get(b, idx_vec[0]);

            builder.assign(&ans, ans - v1 * v2 * a_i * b_i);
        });
    });

    let a_remainder_arr: Array<C, Ext<C::F, C::EF>> = a.slice(builder, b.len(), a.len());
    iter_zip!(builder, a_remainder_arr).for_each(|ptr_vec, builder| {
        let a = builder.iter_ptr_get(&a_remainder_arr, ptr_vec[0]);
        builder.assign(&ans, ans * (one_ext - a));
    });

    ans
}

pub fn build_eq_x_r_vec_sequential<C: Config>(
    builder: &mut Builder<C>,
    r: &Array<C, Ext<C::F, C::EF>>,
) -> Array<C, Ext<C::F, C::EF>> {
    let evals_len = pow_of_2(builder, RVar::from(r.len()));
    let evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(evals_len);
    let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
    builder.set(&evals, 0, one);

    let r_rev = reverse(builder, r);
    builder.range(0, r_rev.len()).for_each(|idx_vec, builder| {
        let r = builder.get(&r_rev, idx_vec[0]);
        let next_size = Usize::Var(pow_of_2(builder, idx_vec[0]).variable());
        let idx_arr = gen_idx_arr(builder, next_size);
        let idx_arr_rev = reverse(builder, &idx_arr);

        iter_zip!(builder, idx_arr_rev).for_each(|ptr_vec, builder| {
            let index = builder.iter_ptr_get(&idx_arr_rev, ptr_vec[0]);
            let prev_val = builder.get(&evals, index.clone());
            let tmp: Ext<C::F, C::EF> = builder.eval(r * prev_val);

            let left_i: Usize<C::N> = builder.eval(index.clone() * Usize::from(2) + Usize::from(1));
            let right_i: Usize<C::N> = builder.eval(index.clone() * Usize::from(2));

            builder.set(&evals, left_i, tmp);
            let right_v: Ext<C::F, C::EF> = builder.eval(prev_val - tmp);
            builder.set(&evals, right_i, right_v);
        });
    });

    evals
}

pub fn ceil_log2(x: usize) -> usize {
    assert!(x > 0, "ceil_log2: x must be positive");
    // Calculate the number of bits in usize
    let usize_bits = std::mem::size_of::<usize>() * 8;
    usize_bits - (x - 1).leading_zeros() as usize
}

pub fn pow_of_2<C: Config>(builder: &mut Builder<C>, log_n: RVar<C::N>) -> RVar<C::N> {
    let res: Felt<C::F> = builder.constant(C::F::ONE);
    let two: Felt<C::F> = builder.constant(C::F::TWO);
    builder.range(0, log_n).for_each(|_idx_vec, builder| {
        builder.assign(&res, res * two);
    });

    let v = builder.cast_felt_to_var(res);
    RVar::from(v)
}

/// get next power of 2 instance with minimal size 2
pub fn next_pow2_instance_padding(num_instance: usize) -> usize {
    num_instance.next_power_of_two().max(2)
}

pub fn ext_pow<C: Config>(
    builder: &mut Builder<C>,
    base: Ext<C::F, C::EF>,
    exponent: usize,
) -> Ext<C::F, C::EF> {
    let res = builder.constant(C::EF::ONE);

    builder
        .range(0, Usize::from(exponent))
        .for_each(|_, builder| {
            builder.assign(&res, res * base);
        });

    res
}

/* : _debug
pub fn eval_ceno_expr_with_instance<C: Config>(
    builder: &mut Builder<C>,
    fixed: &Array<C, Ext<C::F, C::EF>>,
    witnesses: &Array<C, Ext<C::F, C::EF>>,
    structural_witnesses: &Array<C, Ext<C::F, C::EF>>,
    instance: &Array<C, Ext<C::F, C::EF>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    expr: &Expression<E>,
) -> Ext<C::F, C::EF> {
    evaluate_ceno_expr::<C, Ext<C::F, C::EF>>(
        builder,
        expr,
        &|builder, f: &Fixed| {
            let res = builder.get(fixed, f.0);
            res
        },
        &|builder, witness_id: WitnessId| {
            let res = builder.get(witnesses, witness_id as usize);
            res
        },
        &|builder, witness_id, _, _, _| {
            let res = builder.get(structural_witnesses, witness_id as usize);
            res
        },
        &|builder, i| {
            let res = builder.get(instance, i.0);
            res
        },
        &|builder, scalar| {
            let res: Ext<C::F, C::EF> =
                builder.constant(C::EF::from_canonical_u32(scalar.to_canonical_u64() as u32));
            res
        },
        &|builder, challenge_id, pow, scalar, offset| {
            let challenge = builder.get(&challenges, challenge_id as usize);
            let challenge_exp = ext_pow(builder, challenge, pow);

            let scalar_base_slice = scalar
                .as_bases()
                .iter()
                .map(|b| C::F::from_canonical_u64(b.to_canonical_u64()))
                .collect::<Vec<C::F>>();
            let scalar_ext: Ext<C::F, C::EF> =
                builder.constant(C::EF::from_base_slice(&scalar_base_slice));

            let offset_base_slice = offset
                .as_bases()
                .iter()
                .map(|b| C::F::from_canonical_u64(b.to_canonical_u64()))
                .collect::<Vec<C::F>>();
            let offset_ext: Ext<C::F, C::EF> =
                builder.constant(C::EF::from_base_slice(&offset_base_slice));

            let res = builder.eval(challenge_exp * scalar_ext + offset_ext);

            res
        },
        &|builder, a, b| {
            let res = builder.eval(a + b);
            res
        },
        &|builder, a, b| {
            let res = builder.eval(a * b);
            res
        },
        &|builder, x, a, b| {
            let res = builder.eval(a * x + b);
            res
        },
    )
}
*/

/* : _debug
pub fn evaluate_ceno_expr<C: Config, T>(
    builder: &mut Builder<C>,
    expr: &Expression<E>,
    fixed_in: &impl Fn(&mut Builder<C>, &Fixed) -> T,
    wit_in: &impl Fn(&mut Builder<C>, WitnessId) -> T, // witin id
    structural_wit_in: &impl Fn(&mut Builder<C>, WitnessId, usize, u32, usize) -> T,
    instance: &impl Fn(&mut Builder<C>, Instance) -> T,
    constant: &impl Fn(&mut Builder<C>, Either<E::Basefield, E>) -> T,
    challenge: &impl Fn(&mut Builder<C>, ChallengeId, usize, E, E) -> T,
    sum: &impl Fn(&mut Builder<C>, T, T) -> T,
    product: &impl Fn(&mut Builder<C>, T, T) -> T,
    scaled: &impl Fn(&mut Builder<C>, T, T, T) -> T,
) -> T {
    match expr {
        Expression::Fixed(f) => fixed_in(builder, f),
        Expression::WitIn(witness_id) => wit_in(builder, *witness_id),
        Expression::StructuralWitIn(witness_id, max_len, offset, multi_factor) => {
            structural_wit_in(builder, *witness_id, *max_len, *offset, *multi_factor)
        }
        Expression::Instance(i) => instance(builder, *i),
        Expression::Constant(scalar) => constant(builder, *scalar),
        Expression::Sum(a, b) => {
            let a = evaluate_ceno_expr(
                builder,
                a,
                fixed_in,
                wit_in,
                structural_wit_in,
                instance,
                constant,
                challenge,
                sum,
                product,
                scaled,
            );
            let b = evaluate_ceno_expr(
                builder,
                b,
                fixed_in,
                wit_in,
                structural_wit_in,
                instance,
                constant,
                challenge,
                sum,
                product,
                scaled,
            );
            sum(builder, a, b)
        }
        Expression::Product(a, b) => {
            let a = evaluate_ceno_expr(
                builder,
                a,
                fixed_in,
                wit_in,
                structural_wit_in,
                instance,
                constant,
                challenge,
                sum,
                product,
                scaled,
            );
            let b = evaluate_ceno_expr(
                builder,
                b,
                fixed_in,
                wit_in,
                structural_wit_in,
                instance,
                constant,
                challenge,
                sum,
                product,
                scaled,
            );
            product(builder, a, b)
        }
        Expression::ScaledSum(x, a, b) => {
            let x = evaluate_ceno_expr(
                builder,
                x,
                fixed_in,
                wit_in,
                structural_wit_in,
                instance,
                constant,
                challenge,
                sum,
                product,
                scaled,
            );
            let a = evaluate_ceno_expr(
                builder,
                a,
                fixed_in,
                wit_in,
                structural_wit_in,
                instance,
                constant,
                challenge,
                sum,
                product,
                scaled,
            );
            let b = evaluate_ceno_expr(
                builder,
                b,
                fixed_in,
                wit_in,
                structural_wit_in,
                instance,
                constant,
                challenge,
                sum,
                product,
                scaled,
            );
            scaled(builder, x, a, b)
        }
        Expression::Challenge(challenge_id, pow, scalar, offset) => {
            challenge(builder, *challenge_id, *pow, *scalar, *offset)
        }
    }
}
*/

/// evaluate MLE M(x0, x1, x2, ..., xn) address vector with it evaluation format a*[0, 1, 2, 3, ....2^n-1] + b
/// on r = [r0, r1, r2, ...rn] succintly
/// a, b, is constant
/// the result M(r0, r1,... rn) = r0 + r1 * 2 + r2 * 2^2 + .... rn * 2^n
pub fn eval_wellform_address_vec<C: Config>(
    builder: &mut Builder<C>,
    offset: u32,
    scaled: u32,
    r: &Array<C, Ext<C::F, C::EF>>,
    descending: bool,
) -> Ext<C::F, C::EF> {
    let offset: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_u32(offset));
    let scaled: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_u32(scaled));

    let r_sum: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
    let two: Ext<C::F, C::EF> = builder.constant(C::EF::TWO);
    let state: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);

    iter_zip!(builder, r).for_each(|ptr_vec, builder| {
        let x = builder.iter_ptr_get(r, ptr_vec[0]);
        builder.assign(&r_sum, r_sum + x * state);
        builder.assign(&state, state * two);
    });
    let shift: Ext<C::F, C::EF> = builder.eval(scaled * r_sum);

    if descending {
        let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
        builder.assign(&shift, zero - shift);
    }

    let res: Ext<C::F, C::EF> = builder.eval(offset + shift);

    res
}

pub fn max_usize_vec<C: Config>(builder: &mut Builder<C>, vec: Vec<Usize<C::N>>) -> Usize<C::N> {
    assert!(vec.len() > 0);

    let res = vec[0].clone();
    vec.iter().skip(1).for_each(|n| {
        let is_less = is_smaller_than(builder, RVar::from(res.clone()), RVar::from(n.clone()));
        builder.if_eq(is_less, Usize::from(1)).then(|builder| {
            builder.assign(&res, n.clone());
        });
    });

    res
}

pub fn max_usize_arr<C: Config>(
    builder: &mut Builder<C>,
    arr: &Array<C, Usize<C::N>>,
) -> Usize<C::N> {
    let max_var = builder.get(&arr, 0).get_var();

    builder.range(0, arr.len()).for_each(|idx_vec, builder| {
        let n = RVar::from(builder.get(&arr, idx_vec[0]).clone());

        let is_less = is_smaller_than(builder, RVar::from(max_var), n);
        builder.if_eq(is_less, Usize::from(1)).then(|builder| {
            builder.assign(&max_var, n.variable());
        });
    });

    Usize::from(max_var)
}

pub struct UniPolyExtrapolator<C: Config> {
    constants: [Ext<C::F, C::EF>; 12], // 0, 1, 2, 3, 4, -1, 1/2, -1/2, 1/6, -1/6, 1/4, 1/24
}

impl<C: Config> UniPolyExtrapolator<C> {
    pub fn new(builder: &mut Builder<C>) -> Self {
        let zero: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
        let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
        let two: Ext<C::F, C::EF> = builder.constant(C::EF::TWO);
        let three: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_u32(3));
        let four: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_u32(4));
        let six: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_u32(6));
        let twenty_four: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_u32(24));
        let neg_one: Ext<C::F, C::EF> = builder.eval(zero - one);
        let two_inverse: Ext<C::F, C::EF> = builder.eval(two.inverse());
        let neg_two_inverse: Ext<C::F, C::EF> = builder.eval(zero - two_inverse);
        let six_inverse: Ext<C::F, C::EF> = builder.eval(six.inverse());
        let neg_six_inverse: Ext<C::F, C::EF> = builder.eval(zero - six_inverse);
        let four_inverse: Ext<C::F, C::EF> = builder.eval(four.inverse());
        let twenty_four_inverse: Ext<C::F, C::EF> = builder.eval(twenty_four.inverse());

        Self {
            constants: [
                zero,
                one,
                two,
                three,
                four,
                neg_one,
                two_inverse,
                neg_two_inverse,
                six_inverse,
                neg_six_inverse,
                four_inverse,
                twenty_four_inverse,
            ],
        }
    }

    pub fn extrapolate_uni_poly(
        &mut self,
        builder: &mut Builder<C>,
        p_i: &Array<C, Ext<C::F, C::EF>>,
        eval_at: Ext<C::F, C::EF>,
    ) -> Ext<C::F, C::EF> {
        let res: Ext<C::F, C::EF> = builder.eval(self.constants[0] + self.constants[0]);

        builder.if_eq(p_i.len(), Usize::from(4)).then_or_else(
            |builder| {
                let ext = self.extrapolate_uni_poly_deg_3(builder, p_i, eval_at);
                builder.assign(&res, ext);
            },
            |builder| {
                builder.if_eq(p_i.len(), Usize::from(3)).then_or_else(
                    |builder| {
                        let ext = self.extrapolate_uni_poly_deg_2(builder, p_i, eval_at);
                        builder.assign(&res, ext);
                    },
                    |builder| {
                        builder.if_eq(p_i.len(), Usize::from(2)).then_or_else(
                            |builder| {
                                let ext = self.extrapolate_uni_poly_deg_1(builder, p_i, eval_at);
                                builder.assign(&res, ext);
                            },
                            |builder| {
                                builder.if_eq(p_i.len(), Usize::from(5)).then_or_else(
                                    |builder| {
                                        let ext =
                                            self.extrapolate_uni_poly_deg_4(builder, p_i, eval_at);
                                        builder.assign(&res, ext);
                                    },
                                    |builder| {
                                        builder.error();
                                    },
                                );
                            },
                        );
                    },
                );
            },
        );

        res
    }

    fn extrapolate_uni_poly_deg_1(
        &self,
        builder: &mut Builder<C>,
        p_i: &Array<C, Ext<C::F, C::EF>>,
        eval_at: Ext<C::F, C::EF>,
    ) -> Ext<C::F, C::EF> {
        // w0 = 1 / (0−1) = -1
        // w1 = 1 / (1−0) =  1
        let d0: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[0]);
        let d1: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[1]);
        let l: Ext<C::F, C::EF> = builder.eval(d0 * d1);

        let p_i_0 = builder.get(p_i, 0);
        let p_i_1 = builder.get(p_i, 1);

        let t0: Ext<C::F, C::EF> = builder.eval(self.constants[5] * p_i_0 / d0);
        let t1: Ext<C::F, C::EF> = builder.eval(self.constants[1] * p_i_1 / d1);

        builder.eval(l * (t0 + t1))
    }

    fn extrapolate_uni_poly_deg_2(
        &self,
        builder: &mut Builder<C>,
        p_i: &Array<C, Ext<C::F, C::EF>>,
        eval_at: Ext<C::F, C::EF>,
    ) -> Ext<C::F, C::EF> {
        // w0 = 1 / ((0−1)(0−2)) =  1/2
        // w1 = 1 / ((1−0)(1−2)) = -1
        // w2 = 1 / ((2−0)(2−1)) =  1/2
        let d0: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[0]);
        let d1: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[1]);
        let d2: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[2]);

        let l: Ext<C::F, C::EF> = builder.eval(d0 * d1 * d2);

        let p_i_0: Ext<C::F, C::EF> = builder.get(p_i, 0);
        let p_i_1: Ext<C::F, C::EF> = builder.get(p_i, 1);
        let p_i_2: Ext<C::F, C::EF> = builder.get(p_i, 2);

        let t0: Ext<C::F, C::EF> = builder.eval(self.constants[6] * p_i_0 / d0);
        let t1: Ext<C::F, C::EF> = builder.eval(self.constants[5] * p_i_1 / d1);
        let t2: Ext<C::F, C::EF> = builder.eval(self.constants[6] * p_i_2 / d2);

        builder.eval(l * (t0 + t1 + t2))
    }

    fn extrapolate_uni_poly_deg_3(
        &self,
        builder: &mut Builder<C>,
        p_i: &Array<C, Ext<C::F, C::EF>>,
        eval_at: Ext<C::F, C::EF>,
    ) -> Ext<C::F, C::EF> {
        // w0 = 1 / ((0−1)(0−2)(0−3)) = -1/6
        // w1 = 1 / ((1−0)(1−2)(1−3)) =  1/2
        // w2 = 1 / ((2−0)(2−1)(2−3)) = -1/2
        // w3 = 1 / ((3−0)(3−1)(3−2)) =  1/6
        let d0: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[0]);
        let d1: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[1]);
        let d2: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[2]);
        let d3: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[3]);

        let l: Ext<C::F, C::EF> = builder.eval(d0 * d1 * d2 * d3);

        let p_i_0: Ext<C::F, C::EF> = builder.get(p_i, 0);
        let p_i_1: Ext<C::F, C::EF> = builder.get(p_i, 1);
        let p_i_2: Ext<C::F, C::EF> = builder.get(p_i, 2);
        let p_i_3: Ext<C::F, C::EF> = builder.get(p_i, 3);

        let t0: Ext<C::F, C::EF> = builder.eval(self.constants[9] * p_i_0 / d0);
        let t1: Ext<C::F, C::EF> = builder.eval(self.constants[6] * p_i_1 / d1);
        let t2: Ext<C::F, C::EF> = builder.eval(self.constants[7] * p_i_2 / d2);
        let t3: Ext<C::F, C::EF> = builder.eval(self.constants[8] * p_i_3 / d3);

        builder.eval(l * (t0 + t1 + t2 + t3))
    }

    fn extrapolate_uni_poly_deg_4(
        &self,
        builder: &mut Builder<C>,
        p_i: &Array<C, Ext<C::F, C::EF>>,
        eval_at: Ext<C::F, C::EF>,
    ) -> Ext<C::F, C::EF> {
        // w0 = 1 / ((0−1)(0−2)(0−3)(0−4)) =  1/24
        // w1 = 1 / ((1−0)(1−2)(1−3)(1−4)) = -1/6
        // w2 = 1 / ((2−0)(2−1)(2−3)(2−4)) =  1/4
        // w3 = 1 / ((3−0)(3−1)(3−2)(3−4)) = -1/6
        // w4 = 1 / ((4−0)(4−1)(4−2)(4−3)) =  1/24
        let d0: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[0]);
        let d1: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[1]);
        let d2: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[2]);
        let d3: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[3]);
        let d4: Ext<C::F, C::EF> = builder.eval(eval_at - self.constants[4]);

        let l: Ext<C::F, C::EF> = builder.eval(d0 * d1 * d2 * d3 * d4);

        let p_i_0: Ext<C::F, C::EF> = builder.get(p_i, 0);
        let p_i_1: Ext<C::F, C::EF> = builder.get(p_i, 1);
        let p_i_2: Ext<C::F, C::EF> = builder.get(p_i, 2);
        let p_i_3: Ext<C::F, C::EF> = builder.get(p_i, 3);
        let p_i_4: Ext<C::F, C::EF> = builder.get(p_i, 4);

        let t0: Ext<C::F, C::EF> = builder.eval(self.constants[11] * p_i_0 / d0);
        let t1: Ext<C::F, C::EF> = builder.eval(self.constants[9] * p_i_1 / d1);
        let t2: Ext<C::F, C::EF> = builder.eval(self.constants[10] * p_i_2 / d2);
        let t3: Ext<C::F, C::EF> = builder.eval(self.constants[9] * p_i_3 / d3);
        let t4: Ext<C::F, C::EF> = builder.eval(self.constants[11] * p_i_4 / d4);

        builder.eval(l * (t0 + t1 + t2 + t3 + t4))
    }
}
