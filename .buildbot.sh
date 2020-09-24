#! /bin/sh

set -e

git submodule init
git pull --recurse-submodules

export CARGO_HOME="`pwd`/.cargo"
export RUSTUP_HOME="`pwd`/.rustup"

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh
sh rustup.sh --default-host x86_64-unknown-linux-gnu \
    --default-toolchain nightly \
    --no-modify-path \
    --profile minimal \
    -y
export PATH=`pwd`/.cargo/bin/:$PATH

cargo test
cargo test --release

cargo run -- --cp SOM/Smalltalk SOM/TestSuite/TestHarness.som
cargo run --release -- --cp SOM/Smalltalk SOM/TestSuite/TestHarness.som

rustup toolchain install nightly --allow-downgrade --component rustfmt
cargo +nightly fmt --all -- --check

# Build rustc_boehm
git clone https://github.com/softdevteam/rustc_boehm
mkdir -p rustc_boehm/build/rustc_boehm
(cd rustc_boehm && ./x.py build --config ../.buildbot.config.toml)

rustup toolchain link rustc_boehm rustc_boehm/build/x86_64-unknown-linux-gnu/stage1

cargo clean

cargo +rustc_boehm test --features "rustc_boehm"
cargo +rustc_boehm test --release --features "rustc_boehm"

cargo +rustc_boehm run --features "rustc_boehm" -- --cp SOM/Smalltalk SOM/TestSuite/TestHarness.som
cargo +rustc_boehm run --features "rustc_boehm" --release -- --cp SOM/Smalltalk SOM/TestSuite/TestHarness.som
