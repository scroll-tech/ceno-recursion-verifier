## Ceno Recursion Verifier

---
### e2e Ceno Proving

Step 1: Generate `zkvm_proof.bin` and `vk.bin` from within Ceno repo by running its e2e command. Example:
```
cargo run --release --package ceno_zkvm --bin e2e -- --profiling=1 --platform=ceno --hints=10 --public-io=4191 examples/target/riscv32im-ceno-zkvm-elf/release/examples/fibonacci
```
Step 2: Place the exported binary files in the `src/e2e/encoded/` folder.
Step 3: Run proving command:
```
RUST_BACKTRACE=1 cargo test --package ceno-recursion-verifier --lib -- e2e::test_zkvm_proof_verifier_from_bincode_exports --exact --show-output 2>&1 | tee vm_run_output.log
```
