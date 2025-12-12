# Rust MIR-Level Range Analysis

MIR-level range analysis is implemented in [range_analysis.rs](/compiler/rustc_mir_transform/src/range_analysis.rs). Corresponding tests are located in [/tests/mir-opt/range-analysis](/tests/mir-opt/range-analysis).

All evaluation artifacts are collected in the [evaluation](/evaluation) directory. The fuzzing folder contains Python scripts used to generate test cases for binary operations. The perf_results directory contains performance measurements obtained by running the range analysis on a variety of Rust crates. It can be run by copying one of the db files to `build/tmp/rustc-perf/results` and then running `./x perf compare old new`.

This is a PR for [issue #76579](https://github.com/rust-lang/rust/issues/76579) in the Rust repository.
