//@ test-mir-pass: RangeAnalysisPass

// EMIT_MIR binary_ops.test.RangeAnalysisPass.diff
fn test(x: u8, y: u8, x_signed: i8, y_signed: i8, shift: u8) {
    // CHECK-LABEL: fn test(
    // x is [0, 255], y is [0, 255]

    // Unsigned arithmetic
    let sum = x + y;
    let diff = x - y;
    let prod = x * y;
    let quot = if y != 0 { x / y } else { 0 };

    assert!(sum >= 0 && sum <= 255);
    assert!(prod >= 0 && prod <= 255);
    assert!(quot >= 0 && quot <= 255);
    assert!(diff >= 0 && diff <= 255);

    // Signed arithmetic
    let sum = x_signed + y_signed;
    let diff = x_signed - y_signed;
    let prod = x_signed * y_signed;

    assert!(sum >= -128 && sum <= 127);
    assert!(diff >= -128 && diff <= 127);
    assert!(prod >= -128 && prod <= 127);

    // Unsigned bitwise
    let and_result = x & y;
    let or_result = x | y;
    let xor_result = x ^ y;

    assert!(and_result >= 0 && and_result <= 255);
    assert!(or_result >= 0 && or_result <= 255);
    assert!(xor_result >= 0 && xor_result <= 255);

    // Signed bitwise
    let and_result = x_signed & y_signed;
    let or_result = x_signed | y_signed;
    let xor_result = x_signed ^ y_signed;

    assert!(and_result >= -128 && and_result <= 127);
    assert!(or_result >= -128 && or_result <= 127);
    assert!(xor_result >= -128 && xor_result <= 127);

    // Unsigned shift
    let shl_result = x << shift;
    let shr_result = x >> shift;

    assert!(shl_result >= 0 && shl_result <= 255);
    assert!(shr_result >= 0 && shr_result <= 255);

    // Signed shift
    let shl_result = x_signed << shift;
    let shr_result = x_signed >> shift;

    assert!(shl_result >= -128 && shl_result <= 127);
    assert!(shr_result >= -128 && shr_result <= 127);

    // Unsigned comparison
    let eq_result = (x == y) as u8;
    let ne_result = (x != y) as u8;
    let lt_result = (x < y) as u8;
    let le_result = (x <= y) as u8;
    let gt_result = (x > y) as u8;
    let ge_result = (x >= y) as u8;

    assert!(eq_result >= 0 && eq_result <= 1);
    assert!(ne_result >= 0 && ne_result <= 1);
    assert!(lt_result >= 0 && lt_result <= 1);
    assert!(le_result >= 0 && le_result <= 1);
    assert!(gt_result >= 0 && gt_result <= 1);
    assert!(ge_result >= 0 && ge_result <= 1);

    // Signed comparison
    let eq_result = (x_signed == y_signed) as u8;
    let ne_result = (x_signed != y_signed) as u8;
    let lt_result = (x_signed < y_signed) as u8;
    let le_result = (x_signed <= y_signed) as u8;
    let gt_result = (x_signed > y_signed) as u8;
    let ge_result = (x_signed >= y_signed) as u8;

    assert!(eq_result >= 0 && eq_result <= 1);
    assert!(ne_result >= 0 && ne_result <= 1);
    assert!(lt_result >= 0 && lt_result <= 1);
    assert!(le_result >= 0 && le_result <= 1);
    assert!(gt_result >= 0 && gt_result <= 1);
    assert!(ge_result >= 0 && ge_result <= 1);
}
