#! /bin/sh

set -e

export CARGO_HOME="`pwd`/.cargo"
export RUSTUP_HOME="`pwd`/.rustup"

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh
sh rustup.sh --default-host x86_64-unknown-linux-gnu --default-toolchain nightly -y --no-modify-path

export PATH=`pwd`/.cargo/bin/:$PATH

rustup component add --toolchain nightly rustfmt-preview || cargo +nightly install --force rustfmt-nightly

cargo +nightly fmt --all -- --check
cargo test

if [ "`git branch --show-current`" = "staging" ]; then
    cargo doc --no-deps
    cd target/doc
    git init
    git config user.email "noreply@soft-dev.org"
    git config user.name "buildbot"
    git add .
    git commit -m "Deploy gh-pages"
    git remote add origin git@github.com:softdevteam/yksom.git
    GIT_SSH_COMMAND="/usr/bin/ssh -o StrictHostKeyChecking=no -i /opt/ssh-keys/github_yksom" git push -f git@github.com:softdevteam/yksom.git HEAD:gh-pages
fi
