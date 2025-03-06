### Ceno Recursion Verifier
Adapt [WHIR verifier program](https://github.com/scroll-tech/whir/blob/main/src/whir/verifier.rs) using OpenVM's DSL. 

To run the main entry test `test_whir_verifier`:
```
cargo test --package ceno-recursion-verifier --lib -- whir::tests::test_whir_verifier --exact --show-output
```