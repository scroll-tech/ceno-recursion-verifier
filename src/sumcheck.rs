use openvm_native_compiler::prelude::*;
use p3_field::TwoAdicField;
use openvm_native_recursion::challenger::ChallengerVariable;

pub fn verify_whir_sumcheck<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
) where 
    C::F: TwoAdicField,
    C::EF: TwoAdicField,
{
    unimplemented!();
}

pub mod tests {
    use openvm_circuit::arch::instructions::program::Program;
    use openvm_native_compiler::asm::{AsmBuilder, AsmConfig};
    use openvm_stark_backend::config::{StarkGenericConfig, Val};
    use openvm_stark_sdk::config::goldilocks_poseidon2::{default_engine, GoldilocksPoseidon2Config};
    use monty_goldilocks::Goldilocks;
    use openvm_circuit::arch::{Streams, SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_recursion::challenger::duplex::DuplexChallengerVariable;
    // use p3_monty_31::MontyField31;
    // use crate::sumcheck::verify_whir_sumcheck;
    // use whir::{
    //     sumcheck::prover_core::SumcheckCore,
    //     poly_utils::{coeffs::CoefficientList, eq_poly_outside, MultilinearPoint}
    // };

    #[allow(dead_code)]
    pub fn build_test_whir_sumcheck() -> (Program<Goldilocks>, Vec<Vec<Goldilocks>>) {
        type SC = GoldilocksPoseidon2Config;
        type F = Val<SC>;
        type EF = <SC as StarkGenericConfig>::Challenge;
        type Challenger = <SC as StarkGenericConfig>::Challenger;
        type ScPcs = <SC as StarkGenericConfig>::Pcs;

        let engine = default_engine();
        let pcs = engine.config.pcs();
        let perm = engine.perm;
        let mut challenger = Challenger::new(perm.clone());

        let mut builder = AsmBuilder::<F, EF>::default();
        let mut challenger = DuplexChallengerVariable::new(&mut builder);

        // // Main e2e: Construct sumcheck instance
        // let num_variables = 6;
        // let folding_factor = 2;
        // let polynomial = CoefficientList::new((0..1 << num_variables).map(F::from).collect());

        // // Initial stuff
        // let ood_point = MultilinearPoint::expand_from_univariate(F::from(42), num_variables);
        // let statement_point = MultilinearPoint::expand_from_univariate(F::from(97), num_variables);

        // // All the randomness
        // let [epsilon_1, epsilon_2] = [F::from(15), F::from(32)];
        // let folding_randomness_1 = MultilinearPoint(vec![F::from(11), F::from(31)]);
        // let folding_randomness_2 = MultilinearPoint(vec![F::from(97), F::from(36)]);
        // let folding_randomness_3 = MultilinearPoint(vec![F::from(11297), F::from(42136)]);
        // let fold_point_11 =
        //     MultilinearPoint(vec![F::from(31), F::from(15), F::from(31), F::from(15)]);
        // let fold_point_12 =
        //     MultilinearPoint(vec![F::from(1231), F::from(15), F::from(4231), F::from(15)]);
        // let fold_point_2 = MultilinearPoint(vec![F::from(311), F::from(115)]);
        // let combination_randomness_1 = [F::from(1289), F::from(3281), F::from(10921)];
        // let combination_randomness_2 = [F::from(3281), F::from(3232)];

        // let mut prover = SumcheckCore::new(
        //     polynomial.clone(),
        //     &[ood_point.clone(), statement_point.clone()],
        //     &[epsilon_1, epsilon_2],
        // );

        // let sumcheck_poly_1 = prover.compute_sumcheck_polynomial(folding_factor);

        // let folded_poly_1 = polynomial.fold(&folding_randomness_1.clone());
        // prover.compress(
        //     folding_factor,
        //     combination_randomness_1[0],
        //     &folding_randomness_1,
        // );
        // prover.add_new_equality(
        //     &[fold_point_11.clone(), fold_point_12.clone()],
        //     &combination_randomness_1[1..],
        // );

        // let sumcheck_poly_2 = prover.compute_sumcheck_polynomial(folding_factor);

        // let folded_poly_2 = folded_poly_1.fold(&folding_randomness_2.clone());
        // prover.compress(
        //     folding_factor,
        //     combination_randomness_2[0],
        //     &folding_randomness_2,
        // );
        // prover.add_new_equality(&[fold_point_2.clone()], &combination_randomness_2[1..]);

        // let sumcheck_poly_3 = prover.compute_sumcheck_polynomial(folding_factor);
        // let final_coeff = folded_poly_2.fold(&folding_randomness_3.clone()).coeffs()[0];

        // // Compute all evaluations
        // let ood_answer = polynomial.evaluate(&ood_point);
        // let statement_answer = polynomial.evaluate(&statement_point);
        // let fold_answer_11 = folded_poly_1.evaluate(&fold_point_11);
        // let fold_answer_12 = folded_poly_1.evaluate(&fold_point_12);
        // let fold_answer_2 = folded_poly_2.evaluate(&fold_point_2);

        // assert_eq!(
        //     sumcheck_poly_1.sum_over_hypercube(),
        //     epsilon_1 * ood_answer + epsilon_2 * statement_answer
        // );

        // assert_eq!(
        //     sumcheck_poly_2.sum_over_hypercube(),
        //     combination_randomness_1[0] * sumcheck_poly_1.evaluate_at_point(&folding_randomness_1)
        //         + combination_randomness_1[1] * fold_answer_11
        //         + combination_randomness_1[2] * fold_answer_12
        // );

        // assert_eq!(
        //     sumcheck_poly_3.sum_over_hypercube(),
        //     combination_randomness_2[0] * sumcheck_poly_2.evaluate_at_point(&folding_randomness_2)
        //         + combination_randomness_2[1] * fold_answer_2
        // );

        // let full_folding = MultilinearPoint(
        //     [
        //         folding_randomness_3.0.clone(),
        //         folding_randomness_2.0.clone(),
        //         folding_randomness_1.0,
        //     ]
        //     .concat(),
        // );

        // assert_eq!(
        //     sumcheck_poly_3.evaluate_at_point(&folding_randomness_3),
        //     final_coeff
        //         * (combination_randomness_2[0]
        //             * (combination_randomness_1[0]
        //                 * (epsilon_1 * eq_poly_outside(&full_folding, &ood_point)
        //                     + epsilon_2 * eq_poly_outside(&full_folding, &statement_point))
        //                 + combination_randomness_1[1]
        //                     * eq_poly_outside(
        //                         &fold_point_11,
        //                         &MultilinearPoint(
        //                             [
        //                                 folding_randomness_3.0.clone(),
        //                                 folding_randomness_2.0.clone()
        //                             ]
        //                             .concat()
        //                         )
        //                     )
        //                 + combination_randomness_1[2]
        //                     * eq_poly_outside(
        //                         &fold_point_12,
        //                         &MultilinearPoint(
        //                             [folding_randomness_3.0.clone(), folding_randomness_2.0]
        //                                 .concat()
        //                         )
        //                     ))
        //             + combination_randomness_2[1]
        //                 * eq_poly_outside(&folding_randomness_3, &fold_point_2))
        // )

        // verify_whir_sumcheck(builder, challenger);

        builder.halt();

        // _debug: PrimeField32 trait bound cannot accommodate Goldilocks
        let program = builder.compile_isa();
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

        // _debug: PrimeField32 trait bound cannot accommodate Goldilocks
        let executor = VmExecutor::<Goldilocks, NativeConfig>::new(config);
        executor.execute(program, witness).unwrap();
    }
}