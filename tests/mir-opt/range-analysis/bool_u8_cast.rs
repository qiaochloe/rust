//@ test-mir-pass: IntegerRange

// EMIT_MIR bool_u8_cast.test.IntegerRange.diff
fn test(x: bool) -> &'static str {
    // CHECK-LABEL: fn test(
    match x as u8 {
        0 => "null",
        1 => "one",
        2 => "two",     // Unreachable
        _ => "unknown", // Unreachable
    }
}
