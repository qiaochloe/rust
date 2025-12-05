//@ test-mir-pass: RangeAnalysisPass

// EMIT_MIR simple_division.test.RangeAnalysisPass.diff
fn test(x: u8) {
    // CHECK-LABEL: fn test(
    // CHECK: const true
    let b = x / 2;
    let cond = b < 128;
}
