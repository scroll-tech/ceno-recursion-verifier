use crate::tower_verifier::binding::PointAndEvalVariable;
use ark_ff::Field;
use openvm_native_compiler::asm::AsmConfig;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::{
    challenger::ChallengerVariable,
    hints::{InnerChallenge, InnerVal},
};
use p3_field::{FieldAlgebra, FieldExtensionAlgebra};
use ceno_zkvm::expression::{Expression, Fixed, Instance};
use ceno_zkvm::structs::{WitnessId, ChallengeId};
use ff_ext::{BabyBearExt4, SmallField};
use ff_ext::ExtensionField;
use openvm_stark_sdk::p3_baby_bear::BabyBear;

type InnerConfig = AsmConfig<InnerVal, InnerChallenge>;
const NUM_FANIN: usize = 2;
const MAX_DEGREE: usize = 3;
type E = BabyBearExt4;
type F = BabyBear;

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
    let acc: Ext<C::F, C::EF> = builder.eval(C::F::ZERO);

    iter_zip!(builder, a, b).for_each(|idx_vec, builder| {
        let ptr_a = idx_vec[0];
        let ptr_b = idx_vec[1];
        let v_a = builder.iter_ptr_get(&a, ptr_a);
        let v_b = builder.iter_ptr_get(&b, ptr_b);
        builder.assign(&acc, acc + v_a * v_b);
    });

    acc
}

pub fn dot_product_pt_n_eval<C: Config>(
    builder: &mut Builder<C>,
    pt_and_eval: &Array<C, PointAndEvalVariable<C>>,
    b: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<<C as Config>::F, <C as Config>::EF> {
    let acc: Ext<C::F, C::EF> = builder.eval(C::F::ZERO);

    iter_zip!(builder, pt_and_eval, b).for_each(|idx_vec, builder| {
        let ptr_a = idx_vec[0];
        let ptr_b = idx_vec[1];
        let v_a = builder.iter_ptr_get(&pt_and_eval, ptr_a);
        let v_b = builder.iter_ptr_get(&b, ptr_b);
        builder.assign(&acc, acc + v_a.eval * v_b);
    });

    acc
}

pub fn reverse<C: Config>(
    builder: &mut Builder<C>,
    arr: &Array<C, Ext<C::F, C::EF>>,
) -> Array<C, Ext<C::F, C::EF>> {
    let len = arr.len();
    let res: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(len.clone());
    builder.range(0, len.clone()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let rev_i: RVar<_> = builder.eval_expr(len.clone() - i - RVar::from(1));

        let el = builder.get(arr, i);
        builder.set(&res, rev_i, el);
    });

    res
}

pub fn gen_idx_arr<C: Config>(builder: &mut Builder<C>, len: Usize<C::N>) -> Array<C, Var<C::N>> {
    let one = Usize::from(1);
    let res: Array<C, Var<C::N>> = builder.dyn_array(len.clone());

    let el: Var<C::N> = Var::<C::N>::new(0);
    builder.range(0, len).for_each(|idx_vec, builder| {
        builder.set(&res, idx_vec[0], el.clone());
        builder.assign(&el, el.clone() + one.clone());
    });

    res
}

pub fn reverse_idx_arr<C: Config>(
    builder: &mut Builder<C>,
    arr: &Array<C, Usize<C::N>>,
) -> Array<C, Usize<C::N>> {
    let len = arr.len();
    let res: Array<C, Usize<C::N>> = builder.dyn_array(len.clone());
    builder.range(0, len.clone()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let rev_i: RVar<_> = builder.eval_expr(len.clone() - i - RVar::from(1));

        let el = builder.get(arr, i);
        builder.set(&res, rev_i, el);
    });

    res
}

// Evaluate eq polynomial.
pub fn eq_eval<C: Config>(
    builder: &mut Builder<C>,
    x: &Array<C, Ext<C::F, C::EF>>,
    y: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<C::F, C::EF> {
    let acc: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);

    iter_zip!(builder, x, y).for_each(|idx_vec, builder| {
        let ptr_x = idx_vec[0];
        let ptr_y = idx_vec[1];
        let v_x = builder.iter_ptr_get(&x, ptr_x);
        let v_y = builder.iter_ptr_get(&y, ptr_y);
        let xi_yi: Ext<C::F, C::EF> = builder.eval(v_x * v_y);
        let one: Ext<C::F, C::EF> = builder.constant(C::EF::ONE);
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

// Join two arrays
pub fn join<C: Config>(
    builder: &mut Builder<C>,
    a: &Array<C, Ext<C::F, C::EF>>,
    b: &Array<C, Ext<C::F, C::EF>>,
) -> Array<C, Ext<C::F, C::EF>> {
    let a_len = a.len();
    let b_len = b.len();
    let out_len = builder.eval_expr(a_len.clone() + b_len.clone());
    let out = builder.dyn_array(out_len);

    builder.range(0, a_len.clone()).for_each(|i_vec, builder| {
        let i = i_vec[0];
        let a_val = builder.get(a, i);
        builder.set(&out, i, a_val);
    });

    builder.range(0, b_len).for_each(|i_vec, builder| {
        let b_i = i_vec[0];
        let i = builder.eval_expr(b_i + a_len.clone());
        let b_val = builder.get(b, b_i);
        builder.set(&out, i, b_val);
    });

    out
}

// Generate alpha power challenges
pub fn gen_alpha_pows<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    alpha_len: Var<<C as Config>::N>,
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
    challenger: &mut impl ChallengerVariable<C>,
    max_idx: Var<C::N>,
    a: &Array<C, Ext<C::F, C::EF>>,
    b: &Array<C, Ext<C::F, C::EF>>,
) -> Ext<C::F, C::EF> {
    let one = builder.constant(C::EF::ONE);

    // Compute running product of ( x_i y_i + (1 - x_i)(1 - y_i) )_{0 <= i <= n}
    let running_product_len = b.len();
    builder.assign(
        &running_product_len,
        running_product_len.clone() + Usize::from(1),
    );
    let idx_arr = gen_idx_arr(builder, running_product_len.clone());
    let running_product: Array<C, Ext<C::F, C::EF>> =
        builder.dyn_array(running_product_len.clone());

    builder.set(&running_product, 0, one);
    let running_product_iter_slice = running_product.slice(builder, 1, running_product_len.clone());

    iter_zip!(builder, idx_arr, running_product_iter_slice).for_each(|ptr_vec, builder| {
        let idx = builder.iter_ptr_get(&idx_arr, ptr_vec[0]);
        let prev = builder.get(&running_product, idx.clone());
        let ai = builder.get(&a, idx.clone());
        let bi = builder.get(&b, idx.clone());
        // let x: Ext<C::F, C::EF> = builder.constant(C::EF::ZERO);
        let x: Ext<C::F, C::EF> = builder.eval(prev * (ai * bi + (one - ai) * (one - bi)));
        // builder.assign(&x, prev * (ai * bi + (one - ai) * (one - bi)));
        builder.iter_ptr_set(&running_product_iter_slice, ptr_vec[1], x);
    });

    // _debug
    // let running_product2: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(running_product_len.clone());
    // builder.set(&running_product2, b.len(), one);
    // let idx_arr = gen_idx_arr(builder, running_product_len.clone());
    // let idx_arr_rev = reverse_idx_arr(builder, &idx_arr);
    // // let max_idx_bits = builder.num2bits_v_circuit(max_idx, b.len());

    // iter_zip!(builder, idx_arr_rev).for_each(|ptr_vec, builder| {
    //     let idx = builder.iter_ptr_get(&idx_arr_rev, ptr_vec[0]);
    //     idx.value();
    // });

    // _debug
    // let running_product2 = {
    //     let mut running_product = vec![E::ZERO; b.len() + 1];
    //     running_product[b.len()] = E::ONE;
    //     for i in (0..b.len()).rev() {
    //         let bit = E::from_u64(((max_idx >> i) & 1) as u64);
    //         running_product[i] = running_product[i + 1]
    //             * (a[i] * b[i] * bit + (E::ONE - a[i]) * (E::ONE - b[i]) * (E::ONE - bit));
    //     }
    //     running_product
    // };

    // // Here is an example of how this works:
    // // Suppose max_idx = (110101)_2
    // // Then ans = eq(a, b)
    // //          - eq(11011, a[1..6], b[1..6])eq(a[0..1], b[0..1])
    // //          - eq(111, a[3..6], b[3..6])eq(a[0..3], b[0..3])
    // let mut ans = running_product[b.len()];
    // for i in 0..b.len() {
    //     let bit = (max_idx >> i) & 1;
    //     if bit == 1 {
    //         continue;
    //     }
    //     ans -= running_product[i] * running_product2[i + 1] * a[i] * b[i];
    // }
    // for v in a.iter().skip(b.len()) {
    //     ans *= E::ONE - *v;
    // }
    // ans

    one
}

/// This function build the eq(x, r) polynomial for any given r, and output the
/// evaluation of eq(x, r) in its vector form.
///
/// Evaluate
///      eq(x,y) = \prod_i=1^num_var (x_i * y_i + (1-x_i)*(1-y_i))
/// over r, which is
///      eq(x,y) = \prod_i=1^num_var (x_i * r_i + (1-x_i)*(1-r_i))
pub fn build_eq_x_r_vec_sequential<C: Config>(
    builder: &mut Builder<C>,
    r: &Array<C, Ext<C::F, C::EF>>,
) -> Array<C, Ext<C::F, C::EF>> {
    // we build eq(x,r) from its evaluations
    // we want to evaluate eq(x,r) over x \in {0, 1}^num_vars
    // for example, with num_vars = 4, x is a binary vector of 4, then
    //  0 0 0 0 -> (1-r0)   * (1-r1)    * (1-r2)    * (1-r3)
    //  1 0 0 0 -> r0       * (1-r1)    * (1-r2)    * (1-r3)
    //  0 1 0 0 -> (1-r0)   * r1        * (1-r2)    * (1-r3)
    //  1 1 0 0 -> r0       * r1        * (1-r2)    * (1-r3)
    //  ....
    //  1 1 1 1 -> r0       * r1        * r2        * r3
    // we will need 2^num_var evaluations

    let mut evals_len: Felt<C::F> = builder.constant(C::F::ONE);
    let evals_len = builder.exp_power_of_2_v::<Felt<C::F>>(evals_len, r.len());
    let evals_len = builder.cast_felt_to_var(evals_len);

    let evals: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(evals_len);

    // _debug
    // build_eq_x_r_helper_sequential(r, &mut evals, E::ONE);
    // unsafe { std::mem::transmute(evals) }
    evals
}

// _debug
// /// A helper function to build eq(x, r)*init via dynamic programing tricks.
// /// This function takes 2^num_var iterations, and per iteration with 1 multiplication.
// fn build_eq_x_r_helper_sequential<E: ExtensionField>(r: &[E], buf: &mut [MaybeUninit<E>], init: E) {
//     buf[0] = MaybeUninit::new(init);

//     for (i, r) in r.iter().rev().enumerate() {
//         let next_size = 1 << (i + 1);
//         // suppose at the previous step we processed buf [0..size]
//         // for the current step we are populating new buf[0..2*size]
//         // for j travese 0..size
//         // buf[2*j + 1] = r * buf[j]
//         // buf[2*j] = (1 - r) * buf[j]
//         (0..next_size).step_by(2).rev().for_each(|index| {
//             let prev_val = unsafe { buf[index >> 1].assume_init() };
//             let tmp = *r * prev_val;
//             buf[index + 1] = MaybeUninit::new(tmp);
//             buf[index] = MaybeUninit::new(prev_val - tmp);
//         });
//     }
// }

pub fn ceil_log2(x: usize) -> usize {
    assert!(x > 0, "ceil_log2: x must be positive");
    // Calculate the number of bits in usize
    let usize_bits = std::mem::size_of::<usize>() * 8;
    usize_bits - (x - 1).leading_zeros() as usize
}

pub fn pow_of_2_var<C: Config>(
    builder: &mut Builder<C>,
    log_n: Var<C::N>,
) -> Var<C::N> {
    let res = Var::<C::N>::new(1);
    let two = Var::<C::N>::new(2);

    builder.range(0, log_n).for_each(|_idx_vec, builder| {
        builder.assign(&res, res * two);
    });

    res
}

/// get next power of 2 instance with minimal size 2
pub fn next_pow2_instance_padding(num_instance: usize) -> usize {
    num_instance.next_power_of_two().max(2)
}

pub fn ext_pow<C: Config>(builder: &mut Builder<C>, base: Ext<C::F, C::EF>, exponent: usize) -> Ext<C::F, C::EF> {
    let res = builder.constant(C::EF::ONE);
    let mut exp = exponent.clone();

    while exp > 0 {
        if exp & 1 == 1 {
            builder.assign(&res, res * base);
        }
        builder.assign(&res, res * res);
        exp >>= 1;
    }

    res
}

pub fn eval_ceno_expr_with_instance<C: Config>(
    builder: &mut Builder<C>,
    fixed: &Array<C, Ext<C::F, C::EF>>,
    witnesses: &Array<C, Ext<C::F, C::EF>>,
    structural_witnesses: &Array<C, Ext<C::F, C::EF>>,
    instance: &Array<C, Ext<C::F, C::EF>>,
    challenges: &Array<C, Ext<C::F, C::EF>>,
    expr: &Expression<E>
) -> Ext<C::F, C::EF> {
    evaluate_ceno_expr::<C, Ext<C::F, C::EF>>(
        builder,
        expr,
        &|builder, f: &Fixed| builder.get(fixed, f.0),
        &|builder, witness_id: WitnessId| builder.get(witnesses, witness_id as usize),
        &|builder, witness_id, _, _, _| builder.get(structural_witnesses, witness_id as usize),
        &|builder, i| builder.get(instance, i.0),
        &|builder, scalar| {
            let res: Ext<C::F, C::EF> = builder.constant(C::EF::from_canonical_u32(scalar.to_canonical_u64() as u32));
            res
        },
        &|builder, challenge_id, pow, scalar, offset| {
            let challenge = builder.get(&challenges, challenge_id as usize);
            let challenge_exp = ext_pow(builder, challenge, pow);

            let scalar_base_slice = scalar.as_bases().iter().map(|b| C::F::from_canonical_u32(b.to_canonical_u64() as u32)).collect::<Vec<C::F>>();
            let scalar_ext: Ext<C::F, C::EF> = builder.constant(C::EF::from_base_slice(&scalar_base_slice));

            let offset_base_slice = offset.as_bases().iter().map(|b| C::F::from_canonical_u32(b.to_canonical_u64() as u32)).collect::<Vec<C::F>>();
            let offset_ext: Ext<C::F, C::EF> = builder.constant(C::EF::from_base_slice(&offset_base_slice));

            builder.eval(challenge_exp * scalar_ext + offset_ext)
        },
        &|builder, a, b| builder.eval(a + b),
        &|builder, a, b| builder.eval(a * b),
        &|builder, x, a, b| builder.eval(a * x + b),
    )
}

pub fn evaluate_ceno_expr<C: Config, T>(
    builder: &mut Builder<C>,
    expr: &Expression<E>,
    fixed_in: &impl Fn(&mut Builder<C>, &Fixed) -> T,
    wit_in: &impl Fn(&mut Builder<C>, WitnessId) -> T, // witin id
    structural_wit_in: &impl Fn(&mut Builder<C>, WitnessId, usize, u32, usize) -> T,
    instance: &impl Fn(&mut Builder<C>, Instance) -> T,
    constant: &impl Fn(&mut Builder<C>, <E as ExtensionField>::BaseField) -> T,
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




    
