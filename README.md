## Ceno Recursion Verifier

---
### Ceno Proof Verifier
Full e2e ceno proof verification using a OpenVM's DSL-based VM program
```
RUST_BACKTRACE=1 cargo test --package ceno-recursion-verifier --lib -- tests::test_zkvm_proof_verifier --exact --show-output 2>&1 | tee vm_run_output.log
```
---

### (Subroutine) Ceno TowerProof Verifier
Adapt [Ceno TowerProof verifier program](https://github.com/scroll-tech/ceno/blob/master/ceno_zkvm/src/scheme/verifier.rs) using OpenVM's DSL.
To run the main entry test `test_tower_proof_verifier`:
```
cargo test --package ceno-recursion-verifier --lib -- tower_verifier::program::tests::test_tower_proof_verifier --exact --show-output
```

