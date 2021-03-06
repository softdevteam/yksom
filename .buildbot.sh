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

# Build rustgc
git clone https://github.com/softdevteam/rustgc
mkdir -p rustgc/build/rustgc
(cd rustgc && ./x.py build --config ../.buildbot.config.toml)

rustup toolchain link rustgc rustgc/build/x86_64-unknown-linux-gnu/stage1

cargo clean

cargo +rustgc test --features "rustgc"
cargo +rustgc test --release --features "rustgc"

cargo +rustgc run --features "rustgc" -- --cp SOM/Smalltalk SOM/TestSuite/TestHarness.som
cargo +rustgc run --features "rustgc" --release -- --cp SOM/Smalltalk SOM/TestSuite/TestHarness.som
