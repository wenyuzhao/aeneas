//@ [!lean] skip
//@ [lean] subdir=Preconditions
//@ [lean] aeneas-args=-extract-preconditions

#[derive(Copy, Clone)]
pub struct ComplexStruct {
    pub x: i32,
}

pub fn bar(b: ComplexStruct) -> bool {
    b.x > 0
}

/// 1. Multiple consecutive `assert!` statements, including calls to helper functions.
pub fn foo(a: i32, b: ComplexStruct) -> i32 {
    assert!(a > 12);
    assert!(bar(b));
    a + b.x
}

/// 2. Compound condition (`&&`) in leading `assert!` followed by body and internal assertion.
pub fn left_shift_one(v: i32) -> i32 {
    assert!(v >= 0 && v < 1024);
    let r = v << 1;
    assert!(r == v * 2);
    r
}

/// 3. Leading `debug_assert!` statements.
pub fn with_debug_assert(x: u32, y: u32) -> u32 {
    debug_assert!(x <= 1000);
    debug_assert!(y <= 1000);
    x + y
}

/// 4. `assert_eq!`, `assert_ne!`, `debug_assert_eq!`, `debug_assert_ne!` variants.
pub fn with_assert_eq_ne(a: i32, b: i32, c: i32) -> i32 {
    assert_eq!(a, b);
    debug_assert_ne!(c, 0);
    a + c
}

/// 5. Partial extraction: only leading assertions whose temporary bindings are not used
/// in the main body continuation are extracted into `Φ'partial_extraction`.
pub fn partial_extraction(x: i32) -> i32 {
    assert!(x > 0);
    let y = x + 1;
    assert!(y < 100);
    y
}

/// 6. No leading assertions: no `Φ'` function is generated.
pub fn no_precondition(x: i32) -> i32 {
    let y = x * 2;
    assert!(y > 0);
    y
}

/// 7. Duplicate function call after leading assertion: `simplify_duplicate_calls`
/// must not merge the body call with the assertion's internal temporary across `massert`,
/// so `Φ'duplicate_call_after_assert` is properly extracted.
pub fn make_val() -> i32 {
    0
}

pub fn duplicate_call_after_assert() {
    assert_eq!(make_val(), 0);
    let val = make_val();
    assert!(val == 0);
}

/// 8. Explicit `#[no_mangle] fn __aeneas_require` precondition markers:
/// multiple `__aeneas_require` calls (even interleaved with `let` bindings used in the body)
/// are extracted into `Φ'with_aeneas_require`, while regular `assert!` statements in the body
/// remain in the function body.
#[no_mangle]
pub fn __aeneas_require(cond: bool) {
    assert!(cond);
}

pub fn with_aeneas_require(x: i32, y: i32) -> i32 {
    __aeneas_require(x > 0);
    __aeneas_require(y > 0);
    let sum = x + y;
    __aeneas_require(sum > 10);
    assert!(y > 0);
    sum
}
