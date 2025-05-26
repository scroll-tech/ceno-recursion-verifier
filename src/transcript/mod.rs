use ff_ext::{BabyBearExt4, ExtensionField as CenoExtensionField, SmallField};
use openvm_native_compiler::prelude::*;
use openvm_native_recursion::challenger::ChallengerVariable;
use p3_field::FieldAlgebra;

pub fn transcript_observe_label<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut impl ChallengerVariable<C>,
    label: &[u8],
) {
    let label_f = <BabyBearExt4 as CenoExtensionField>::BaseField::bytes_to_field_elements(label);
    for n in label_f {
        let f: Felt<C::F> = builder.constant(C::F::from_canonical_u64(n.to_canonical_u64()));
        challenger.observe(builder, f);
    }
}

#[cfg(test)]
mod tests {
    use ff_ext::BabyBearExt4;
    use openvm_circuit::arch::{SystemConfig, VmExecutor};
    use openvm_native_circuit::{Native, NativeConfig};
    use openvm_native_compiler::conversion::{convert_program, CompilerOptions};
    use openvm_native_compiler::ir::Felt;
    use openvm_native_compiler::prelude::AsmCompiler;
    use openvm_native_compiler::{asm::AsmConfig, ir::Builder};
    use openvm_native_recursion::challenger::FeltChallenger;
    use openvm_native_recursion::challenger::{
        duplex::DuplexChallengerVariable, CanObserveVariable,
    };
    use p3_baby_bear::BabyBear;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::FieldAlgebra;

    #[test]
    fn test_sample_ext() {
        type F = BabyBear;
        type E = BabyBearExt4;
        type EF = BinomialExtensionField<BabyBear, 4>;
        type C = AsmConfig<F, EF>;

        let mut builder = Builder::<C>::default();
        let mut challenger = DuplexChallengerVariable::<C>::new(&mut builder);

        // simple program
        let f: Felt<F> = builder.eval(F::from_canonical_u32(1));
        challenger.observe(&mut builder, f);
        let _ext = challenger.sample_ext(&mut builder);
        builder.halt();

        // get the assembly code
        let options = CompilerOptions::default();
        let mut compiler = AsmCompiler::new(options.word_size);
        compiler.build(builder.operations);
        let asm_code = compiler.code();
        println!("asm code");
        println!("{asm_code}");

        // execute the program
        // get execution result
        let program = convert_program(asm_code, options);
        let system_config = SystemConfig::default()
            .with_public_values(4)
            .with_max_segment_len((1 << 22) - 100);
        let config = NativeConfig::new(system_config, Native);
        let executor = VmExecutor::<BabyBear, NativeConfig>::new(config);

        let input_stream = Vec::new();
        let res = executor
            .execute_and_then(program, input_stream, |_, seg| Ok(seg), |err| err)
            .unwrap();

        for (i, seg) in res.iter().enumerate() {
            #[cfg(feature = "bench-metrics")]
            {
                println!("=> segment {:?} metrics: {:?}", i, seg.metrics);
            }
        }
    }
}
