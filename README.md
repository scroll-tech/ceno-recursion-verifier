### Ceno Recursion Verifier
Adapt [WHIR sumcheck toy example](https://github.com/scroll-tech/whir/blob/main/src/sumcheck/mod.rs) using OpenVM's DSL. Example: 

To run the main entry test `test_whir_sumcheck`:
```
cargo test --package ceno-recursion-verifier --lib -- sumcheck::tests::test_whir_sumcheck --exact --show-output
```