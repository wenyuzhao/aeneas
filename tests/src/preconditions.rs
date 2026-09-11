//@ [!lean] skip
//@ [lean] subdir=Preconditions
//@ [lean] aeneas-args=-extract-preconditions

#[no_mangle]
pub fn __aeneas_require(cond: bool) {
    assert!(cond);
}

#[derive(Copy, Clone)]
pub struct ComplexStruct {
    pub x: i32,
}

pub fn bar(b: ComplexStruct) -> bool {
    b.x > 0
}

/// 1. Multiple consecutive `__aeneas_require` statements, including calls to helper functions.
pub fn foo(a: i32, b: ComplexStruct) -> i32 {
    __aeneas_require(a > 12);
    __aeneas_require(bar(b));
    a + b.x
}

/// 2. Compound condition (`&&`) in `__aeneas_require` followed by body and internal assertion.
pub fn left_shift_one(v: i32) -> i32 {
    __aeneas_require(v >= 0 && v < 1024);
    let r = v << 1;
    assert!(r == v * 2);
    r
}

/// 3. Multiple `__aeneas_require` statements on unsigned inputs.
pub fn with_debug_assert(x: u32, y: u32) -> u32 {
    __aeneas_require(x <= 1000);
    __aeneas_require(y <= 1000);
    x + y
}

/// 4. Equality and inequality conditions in `__aeneas_require`.
pub fn with_assert_eq_ne(a: i32, b: i32, c: i32) -> i32 {
    __aeneas_require(a == b);
    __aeneas_require(c != 0);
    a + c
}

/// 5. Partial extraction: `__aeneas_require` is extracted into `Φ'partial_extraction`,
/// while regular `assert!` statements in the body remain in the function body.
pub fn partial_extraction(x: i32) -> i32 {
    __aeneas_require(x > 0);
    let y = x + 1;
    assert!(y < 100);
    y
}

/// 6. No `__aeneas_require`: no `Φ'` function is generated (even if there are `assert!`s).
pub fn no_precondition(x: i32) -> i32 {
    let y = x * 2;
    assert!(y > 0);
    y
}

/// 7. Duplicate function call after `__aeneas_require`: `simplify_duplicate_calls`
/// must not merge the body call with the precondition's internal temporary across `__aeneas_require`,
/// so `Φ'duplicate_call_after_assert` is properly extracted.
pub fn make_val() -> i32 {
    0
}

pub fn duplicate_call_after_assert() {
    __aeneas_require(make_val() == 0);
    let val = make_val();
    assert!(val == 0);
}

/// 8. Multiple `__aeneas_require` calls interleaved with `let` bindings used in the body:
/// extracted into `Φ'with_aeneas_require`, while regular `assert!` statements in the body
/// remain in the function body.
pub fn with_aeneas_require(x: i32, y: i32) -> i32 {
    __aeneas_require(x > 0);
    __aeneas_require(y > 0);
    let sum = x + y;
    __aeneas_require(sum > 10);
    assert!(y > 0);
    sum
}

/// 9. `__aeneas_require` appearing after a regular `assert!` statement:
/// `__aeneas_require(x > 0)` is extracted into `Φ'require_after_assert`,
/// while `assert!(x != 0)` remains in `require_after_assert`.
pub fn require_after_assert(x: i32) -> i32 {
    assert!(x != 0);
    __aeneas_require(x > 0);
    x
}
