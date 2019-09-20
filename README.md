# ykSOM

A [SOM](http://som-st.github.io/) VM in Rust. SOM is a cut-down Smalltalk-like
language. yksom is eventually intended to be used with
[Yorick](https://github.com/softdevteam/yk/) to produce a JIT-compiling VM,
though it is currently an entirely stand-alone interpreter. Currently it is
partly a test bed to experiment with good ways of structuring Rust
interpreters, balancing correctness, performance, and readability. The
[internal API documentation](https://softdevteam.github.io/yksom/api/) is
available online.

yksom is intended to be source-compatible with other SOM implementations
although it implements (uncheckable) exceptions, so that (one day...) errors
can cause SOM-level backtraces.
