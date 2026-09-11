//@ [lean] aeneas-args=-extract-preconditions
//@ [lean] known-failure
//@ [!lean] skip

#[no_mangle]
pub fn __aeneas_require(cond: bool) {
    assert!(cond);
}

pub fn require_in_branch(x: i32) -> i32 {
    if x > 0 {
        __aeneas_require(x > 10);
    }
    x
}
