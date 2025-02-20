use ark_ff::{BigInteger, Field, PrimeField};
use openvm::io::println;
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::ChallengerVariable;
use p3_field::{Field as Plonky3Field, FieldAlgebra, TwoAdicField};
use whir::{
    crypto::fields::Field64,
    poly_utils::{coeffs::CoefficientList, eq_poly3, eq_poly_outside, MultilinearPoint},
    sumcheck::{proof::SumcheckPolynomial, prover_core::SumcheckCore},
    utils::base_decomposition,
};

fn to_plonky3_field<F: PrimeField, G: Plonky3Field>(n: F) -> G {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&n.into_bigint().to_bytes_le());
    G::from_canonical_u64(u64::from_le_bytes(bytes))
}

fn sum_over_hypercube<C: Config, WF: Field + PrimeField>(
    sumcheck_poly: &SumcheckPolynomial<WF>,
    evaluation_idxs: &Vec<usize>,
) -> SymbolicExt<C::F, C::EF> {
    let mut sum: WF = WF::ZERO;
    for idx in evaluation_idxs {
        sum += sumcheck_poly.evaluations()[*idx];
    }
    SymbolicExt::from_f(to_plonky3_field::<WF, C::EF>(sum))
}

fn dot_product<F: Field>(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len());
    let mut sum = F::zero();
    for i in 0..a.len() {
        sum += a[i] * b[i];
    }
    sum
}

fn verify_whir_sumcheck<C: Config, WF>(
    builder: &mut Builder<C>,
    num_variables: usize, // Total number of variables of the original polynomial
    folding_factor: usize,
    sumcheck_round_polys: Vec<SumcheckPolynomial<WF>>,
    folding_points: Vec<MultilinearPoint<WF>>,
    folding_randomness: Vec<MultilinearPoint<WF>>,
    folding_evaluations: Vec<WF>,
    combination_randomness: Vec<&[WF]>,
    evaluation_idxs: Vec<usize>,
) where
    C::F: TwoAdicField,
    C::EF: TwoAdicField,
    WF: Field + PrimeField,
{
    let num_rounds = num_variables / folding_factor;

    builder.assert_var_eq(
        RVar::from(sumcheck_round_polys.len()),
        RVar::from(num_rounds),
    );
    builder.assert_var_eq(RVar::from(folding_randomness.len()), RVar::from(num_rounds));

    let round_poly_sums: Array<C, Ext<C::F, C::EF>> = builder.array(num_rounds);
    for i in 0..num_rounds {
        builder.set(
            &round_poly_sums,
            i,
            sum_over_hypercube::<C, WF>(&sumcheck_round_polys[i], &evaluation_idxs),
        );
    }

    let round_check_scalars: Array<C, Ext<C::F, C::EF>> = builder.array(num_rounds);

    // Round polynomial sum checks
    builder.set(
        &round_check_scalars,
        0,
        SymbolicExt::from_f(to_plonky3_field(
            combination_randomness[0][0] * folding_evaluations[0]
                + combination_randomness[0][1] * folding_evaluations[1],
        )),
    );

    builder.set(
        &round_check_scalars,
        1,
        SymbolicExt::from_f(to_plonky3_field(
            combination_randomness[1][0]
                * &sumcheck_round_polys[0].evaluate_at_point(&folding_randomness[0])
                + combination_randomness[1][1] * folding_evaluations[2]
                + combination_randomness[1][2] * folding_evaluations[3],
        )),
    );

    builder.set(
        &round_check_scalars,
        2,
        SymbolicExt::from_f(to_plonky3_field(
            combination_randomness[2][0]
                * &sumcheck_round_polys[1].evaluate_at_point(&folding_randomness[1])
                + combination_randomness[2][1] * folding_evaluations[4],
        )),
    );

    iter_zip!(builder, round_poly_sums, round_check_scalars).for_each(|ptr_vec, builder| {
        let sum = builder.iter_ptr_get(&round_poly_sums, ptr_vec[0]);
        let scalar = builder.iter_ptr_get(&round_check_scalars, ptr_vec[1]);
        builder.assert_eq::<Ext<C::F, C::EF>>(sum, scalar);
    });

    // Final folding check
    let full_folding = MultilinearPoint(
        [
            folding_randomness[2].0.clone(),
            folding_randomness[1].0.clone(),
            folding_randomness[0].0.clone(),
        ]
        .concat(),
    );

    let final_evals = builder.array(2);
    builder.set(
        &final_evals,
        0,
        SymbolicExt::from_f(to_plonky3_field::<WF, C::EF>(
            sumcheck_round_polys[2].evaluate_at_point(&folding_randomness[2]),
        )),
    );
    builder.set(
        &final_evals,
        0,
        SymbolicExt::from_f(to_plonky3_field::<WF, C::EF>(
            folding_evaluations[5]
                * dot_product(
                    &combination_randomness[2],
                    &[
                        dot_product(
                            &combination_randomness[1],
                            &[
                                dot_product(
                                    &combination_randomness[0],
                                    &[
                                        eq_poly_outside(&full_folding, &folding_points[0]),
                                        eq_poly_outside(&full_folding, &folding_points[1]),
                                    ],
                                ),
                                eq_poly_outside(
                                    &folding_points[2],
                                    &MultilinearPoint(
                                        [
                                            folding_randomness[2].0.clone(),
                                            folding_randomness[1].0.clone(),
                                        ]
                                        .concat(),
                                    ),
                                ),
                                eq_poly_outside(
                                    &folding_points[3],
                                    &MultilinearPoint(
                                        [
                                            folding_randomness[2].0.clone(),
                                            folding_randomness[1].0.clone(),
                                        ]
                                        .concat(),
                                    ),
                                ),
                            ],
                        ),
                        eq_poly_outside(&folding_randomness[2], &folding_points[4]),
                    ],
                ),
        )),
    );

    let sum: Ext<C::F, C::EF> = builder.get(&final_evals, 0);
    let scalar: Ext<C::F, C::EF> = builder.get(&final_evals, 1);
    builder.assert_eq::<Ext<C::F, C::EF>>(sum, scalar);
}

pub mod tests {
    use crate::sumcheck::verify_whir_sumcheck;
    use openvm_circuit::arch::instructions::program::Program;
    use openvm_circuit::arch::{Streams, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::asm::{AsmBuilder, AsmConfig};
    use openvm_native_recursion::challenger::duplex::DuplexChallengerVariable;
    use openvm_stark_backend::config::{StarkGenericConfig, Val};
    use openvm_stark_sdk::{
        config::baby_bear_poseidon2::{default_engine, BabyBearPoseidon2Config},
        p3_baby_bear::BabyBear,
    };
    use whir::{
        crypto::fields::Field64,
        poly_utils::{coeffs::CoefficientList, eq_poly_outside, MultilinearPoint},
        sumcheck::prover_core::SumcheckCore,
        utils::base_decomposition,
    };

    fn construct_binary_evaluation_idxs(folding_factor: usize) -> Vec<usize> {
        (0..(1 << folding_factor))
            .into_iter()
            .filter(|&p| {
                base_decomposition(p, 3, folding_factor)
                    .into_iter()
                    .all(|v| matches!(v, 0 | 1))
            })
            .collect::<Vec<usize>>()
    }

    #[allow(dead_code)]
    pub fn build_test_whir_sumcheck() -> (Program<BabyBear>, Vec<Vec<BabyBear>>) {
        type SC = BabyBearPoseidon2Config;
        type F = Val<SC>;
        type EF = <SC as StarkGenericConfig>::Challenge;
        type Challenger = <SC as StarkGenericConfig>::Challenger;
        type ScPcs = <SC as StarkGenericConfig>::Pcs;
        type C = AsmConfig<F, EF>;
        type WF = Field64; // Whir's field

        let engine = default_engine();
        let pcs = engine.config.pcs();
        let perm = engine.perm;
        let mut challenger = Challenger::new(perm.clone());

        let mut builder = AsmBuilder::<F, EF>::default();
        let mut challenger = DuplexChallengerVariable::new(&mut builder);

        // Main e2e: Construct sumcheck instance
        // WHIR sumcheck larger e2e test: https://github.com/scroll-tech/whir/blob/main/src/sumcheck/mod.rs
        let num_variables = 6;
        let folding_factor = 2;
        let polynomial = CoefficientList::new((0..1 << num_variables).map(WF::from).collect());

        // Initial stuff
        let ood_point = MultilinearPoint::expand_from_univariate(WF::from(42), num_variables);
        let statement_point = MultilinearPoint::expand_from_univariate(WF::from(97), num_variables);

        // All the randomness
        let [epsilon_1, epsilon_2] = [WF::from(15), WF::from(32)];
        let folding_randomness_1 = MultilinearPoint(vec![WF::from(11), WF::from(31)]);
        let folding_randomness_2 = MultilinearPoint(vec![WF::from(97), WF::from(36)]);
        let folding_randomness_3 = MultilinearPoint(vec![WF::from(11297), WF::from(42136)]);
        let fold_point_11 =
            MultilinearPoint(vec![WF::from(31), WF::from(15), WF::from(31), WF::from(15)]);
        let fold_point_12 = MultilinearPoint(vec![
            WF::from(1231),
            WF::from(15),
            WF::from(4231),
            WF::from(15),
        ]);
        let fold_point_2 = MultilinearPoint(vec![WF::from(311), WF::from(115)]);
        let combination_randomness_1 = [WF::from(1289), WF::from(3281), WF::from(10921)];
        let combination_randomness_2 = [WF::from(3281), WF::from(3232)];

        // Prover
        let mut prover = SumcheckCore::new(
            polynomial.clone(),
            &[ood_point.clone(), statement_point.clone()],
            &[epsilon_1, epsilon_2],
        );

        let sumcheck_poly_1 = prover.compute_sumcheck_polynomial(folding_factor);

        let folded_poly_1 = polynomial.fold(&folding_randomness_1.clone());
        prover.compress(
            folding_factor,
            combination_randomness_1[0],
            &folding_randomness_1,
        );
        prover.add_new_equality(
            &[fold_point_11.clone(), fold_point_12.clone()],
            &combination_randomness_1[1..],
        );

        let sumcheck_poly_2 = prover.compute_sumcheck_polynomial(folding_factor);

        let folded_poly_2 = folded_poly_1.fold(&folding_randomness_2.clone());
        prover.compress(
            folding_factor,
            combination_randomness_2[0],
            &folding_randomness_2,
        );
        prover.add_new_equality(&[fold_point_2.clone()], &combination_randomness_2[1..]);

        let sumcheck_poly_3 = prover.compute_sumcheck_polynomial(folding_factor);
        let folded_poly_3 = folded_poly_2.fold(&folding_randomness_3.clone());
        let final_coeff = folded_poly_3.coeffs()[0];

        // Compute all evaluations
        let ood_answer = polynomial.evaluate(&ood_point);
        let statement_answer = polynomial.evaluate(&statement_point);
        let fold_answer_11 = folded_poly_1.evaluate(&fold_point_11);
        let fold_answer_12 = folded_poly_1.evaluate(&fold_point_12);
        let fold_answer_2 = folded_poly_2.evaluate(&fold_point_2);

        let evaluation_idxs = construct_binary_evaluation_idxs(folding_factor);

        verify_whir_sumcheck::<C, WF>(
            &mut builder,
            num_variables,
            folding_factor,
            vec![sumcheck_poly_1, sumcheck_poly_2, sumcheck_poly_3],
            vec![
                ood_point,
                statement_point,
                fold_point_11,
                fold_point_12,
                fold_point_2,
            ],
            vec![
                folding_randomness_1,
                folding_randomness_2,
                folding_randomness_3,
            ],
            vec![
                ood_answer,
                statement_answer,
                fold_answer_11,
                fold_answer_12,
                fold_answer_2,
                final_coeff,
            ],
            vec![
                &[epsilon_1, epsilon_2],
                &combination_randomness_1,
                &combination_randomness_2,
            ],
            evaluation_idxs,
        );

        builder.halt();

        let program: Program<
            p3_monty_31::MontyField31<openvm_stark_sdk::p3_baby_bear::BabyBearParameters>,
        > = builder.compile_isa();
        let mut witness_stream = Vec::new();

        (program, witness_stream)
    }

    #[test]
    fn test_whir_sumcheck() {
        let (program, witness) = build_test_whir_sumcheck();

        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 25) - 100);
        let config = NativeConfig::new(system_config, Native);

        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);
        executor.execute(program, witness).unwrap();
    }
}
