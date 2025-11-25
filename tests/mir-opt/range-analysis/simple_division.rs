//@ test-mir-pass: IntegerRange

// EMIT_MIR simple_division.test.IntegerRange.diff
fn test(x: u8) {
    // CHECK-LABEL: fn test(
    // CHECK: const true
    let b = x / 2;
    let cond = b < 128;
}
