## Ceno Recursion Verifier

Repo contains two vm programs (using OpenVM's DSL) for verifying WHIR and Ceno TowerProof. 

---

### WHIR Verifier
Adapt [WHIR verifier program](https://github.com/scroll-tech/whir/blob/main/src/whir/verifier.rs) using OpenVM's DSL. 

To run the main entry test `test_whir_verifier`:
```
cargo test --package ceno-recursion-verifier --lib -- whir::tests::test_whir_verifier --exact --show-output
```

---

### Ceno TowerProof Verifier
Adapt [Ceno TowerProof verifier program](https://github.com/scroll-tech/ceno/blob/master/ceno_zkvm/src/scheme/verifier.rs) using OpenVM's DSL.
To run the main entry test `test_tower_proof_verifier`:
```
cargo test --package ceno-recursion-verifier --lib -- tower_verifier::program::tests::test_tower_proof_verifier --exact --show-output
```
