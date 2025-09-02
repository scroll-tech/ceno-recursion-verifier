#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)"

# Clone the ceno repository if it doesn't exist
if [ ! -d "$REPO_ROOT/build/ceno" ] || [ -z "$(ls -A "$REPO_ROOT/build/ceno" 2>/dev/null)" ]; then
    git clone https://github.com/scroll-tech/ceno.git "$REPO_ROOT/build/ceno/"
fi

# Enter the ceno directory
cd $REPO_ROOT/build/ceno && git checkout master && git pull origin master

# Execute the ceno_zkvm e2e test
RUST_LOG=info cargo run --release --package ceno_zkvm --bin e2e -- --platform=ceno \
    examples/target/riscv32im-ceno-zkvm-elf/release/examples/keccak_syscall \
    --field=baby-bear

mkdir -p $REPO_ROOT/src/e2e/encoded

# Copy vk.bin and proof.bin to the src/e2e/encoded directory in the parent directory
cp vk.bin $REPO_ROOT/src/e2e/encoded/
cp proof.bin $REPO_ROOT/src/e2e/encoded/

# Return to the root directory
cd $REPO_ROOT

# Execute the test_zkvm_verifier test
RUST_LOG=info,p3_=warn cargo test --release --lib test_zkvm_verifier -- --nocapture
