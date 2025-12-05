//@ test-mir-pass: RangeAnalysisPass

// EMIT_MIR switch_int_opt.test.RangeAnalysisPass.diff
fn test(x: u8) -> &'static str {
    // CHECK-LABEL: fn test(
    // x is [0, 10] after the check
    if x <= 10 {
        match x {
            0 => "zero",
            1 => "one",
            5 => "five",
            10 => "ten",
            20 => "twenty",   // Unreachable
            100 => "hundred", // Unreachable
            _ => "other",
        }
    } else {
        "unknown"
    }
}
