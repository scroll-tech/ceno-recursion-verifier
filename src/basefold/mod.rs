pub mod binding;
use crate::{arithmetics::join, tower_verifier::binding::PointVariable};
use binding::{BasefoldProofVariable, PointAndEvalsVariable};
use openvm_native_compiler::prelude::*;
use openvm_native_compiler_derive::iter_zip;
use openvm_native_recursion::challenger::duplex::DuplexChallengerVariable;
use ceno_zkvm::scheme::verifier::ZKVMVerifier;
use ff_ext::BabyBearExt4;
use mpcs::{Basefold, BasefoldRSParams};

type E = BabyBearExt4;
type Pcs = Basefold<E, BasefoldRSParams>;

const BASECODE_MSG_SIZE: usize = 7;
const NUM_QUERIES: usize = 200;

pub fn basefold_batch_verify<C: Config>(
    builder: &mut Builder<C>,
    challenger: &mut DuplexChallengerVariable<C>,
    num_instances: Array<C, Array<C, Felt<C::F>>>,
    rt_points: Vec<PointVariable<C>>,
    fixed_commit: Array<C, Felt<C::F>>,
    witin_commit: Array<C, Felt<C::F>>,
    evaluations: Vec<Array<C, Ext<C::F, C::EF>>>,
    circuit_num_polys: &Vec<(usize, usize)>,
    fixed_witin_opening_proof: BasefoldProofVariable<C>,
    cs: &ZKVMVerifier<E, Pcs>,
) {
    builder.assert_usize_eq(num_instances.len(), Usize::from(rt_points.len()));

    let points: Array<C, PointVariable<C>> = builder.dyn_array(rt_points.len());
    for (idx, pt) in rt_points.into_iter().enumerate() {
        builder.set(&points, idx, pt);
    }
    let evals: Array<C, Array<C, Ext<C::F, C::EF>>> = builder.dyn_array(evaluations.len());
    for (idx, es) in evaluations.into_iter().enumerate() {
        builder.set(&evals, idx, es);
    }
    
    iter_zip!(builder, num_instances, points).for_each(|ptr_vec, builder| {
        let circuit_params = builder.iter_ptr_get(&num_instances, ptr_vec[0]);
        let point = builder.iter_ptr_get(&points, ptr_vec[1]);
        let circuit_num_var_f = builder.get(&circuit_params, 2);
        let circuit_num_var = Usize::from(builder.cast_felt_to_var(circuit_num_var_f.clone()));
        builder.assert_usize_eq(circuit_num_var, point.fs.len());
    });


    let trivial_point_evals: Array<C, PointAndEvalsVariable<C>> = builder.dyn_array(fixed_witin_opening_proof.trivial_metas_count.clone());
    let point_evals: Array<C, PointAndEvalsVariable<C>> = builder.dyn_array(fixed_witin_opening_proof.metas_count.clone());

    let trivial_idx: Usize<C::N> = Usize::from(0);
    let sumcheck_idx: Usize<C::N> = Usize::from(0);
    let evals_idx: Usize<C::N> = Usize::from(0);

    builder.range(0, fixed_witin_opening_proof.circuit_metas.len()).for_each(|idx_vec, builder| {
        let metas = builder.get(&fixed_witin_opening_proof.circuit_metas, idx_vec[0]);

        let point = builder.get(&points, idx_vec[0]);
        let es = builder.get(&evals, evals_idx.clone());
        builder.assign(&evals_idx, evals_idx.clone() + Usize::from(1));
        let es_slice = es.slice(builder, 0, metas.witin_num_polys.clone());

        let fixed_es_slice: Array<C, Ext<C::F, C::EF>> = builder.dyn_array(metas.fixed_num_polys.clone());
        builder.if_ne(metas.fixed_num_polys.clone(), Usize::from(0)).then(|builder| {
            let next_es = builder.get(&evals, evals_idx.clone());
            builder.assign(&evals_idx, evals_idx.clone() + Usize::from(1));
            builder.range(0, metas.fixed_num_polys.clone()).for_each(|fixed_idx_vec, builder| {
                let e = builder.get(&next_es, fixed_idx_vec[0]);
                builder.set(&fixed_es_slice, fixed_idx_vec[0], e);
            });
        });

        let es = join(builder, &es_slice, &fixed_es_slice);

        builder.if_eq(metas.is_trivial.clone(), Usize::from(1)).then(|builder| {
            builder.set(&trivial_point_evals, trivial_idx.clone(), PointAndEvalsVariable {
                point: point.clone(),
                evals: es.clone(),
            });
            builder.assign(&trivial_idx, trivial_idx.clone() + Usize::from(1));
        });
        builder.if_ne(metas.is_trivial, Usize::from(1)).then(|builder| {
            builder.set(&point_evals, sumcheck_idx.clone(), PointAndEvalsVariable {
                point: point.clone(),
                evals: es.clone(),
            });
            builder.assign(&sumcheck_idx, sumcheck_idx.clone() + Usize::from(1));
        });
    });

    builder.if_ne(fixed_witin_opening_proof.metas_count.clone(), Usize::from(0)).then(|builder| {
        builder.range(0, fixed_witin_opening_proof.final_message.len()).for_each(|idx_vec, builder| {
            let msg = builder.get(&fixed_witin_opening_proof.final_message, idx_vec[0]);
            builder.assert_usize_eq(msg.len(), Usize::from(BASECODE_MSG_SIZE));
        });
        builder.assert_usize_eq(fixed_witin_opening_proof.query_opening_proofs.len(), Usize::from(NUM_QUERIES));
    });
}
