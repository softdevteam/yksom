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

rustup toolchain install nightly --allow-downgrade --component rustfmt
cargo +nightly fmt --all -- --check

# Build alloy
git clone https://github.com/softdevteam/alloy
mkdir -p alloy/build/alloy
(cd alloy && ./x.py build --config ../.buildbot.config.toml)

rustup toolchain link alloy alloy/build/x86_64-unknown-linux-gnu/stage1

cargo clean

cargo +alloy test
cargo +alloy test --release

cargo +alloy run  -- --cp SOM/Smalltalk SOM/TestSuite/TestHarness.som
cargo +alloy run --release -- --cp SOM/Smalltalk SOM/TestSuite/TestHarness.som

cargo +alloy run --release -- --cp SOM/Smalltalk:lang_tests hello_world1

cd SOM
cargo +alloy run --release -- \
  --cp Smalltalk:TestSuite:SomSom/src/compiler:SomSom/src/vm:SomSom/src/vmobjects:SomSom/src/interpreter:SomSom/src/primitives \
  SomSom/tests/SomSomTests.som
cargo +alloy run --release -- \
  --cp Smalltalk:Examples/Benchmarks/GraphSearch \
  Examples/Benchmarks/BenchmarkHarness.som GraphSearch 10 4
