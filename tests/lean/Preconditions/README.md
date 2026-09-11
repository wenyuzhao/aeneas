# Precondition Extraction (`-extract-preconditions`)

When Aeneas is invoked with the `-extract-preconditions` CLI flag, it extracts precondition assertions marked with `#[no_mangle] fn __aeneas_require` from Rust functions into standalone Lean definitions returning `Result Unit`.

## What Format is Identified as a Precondition

A prefix of statements at the very beginning of a Rust function body is identified as a precondition if it contains calls to a marker function:
```rust
#[no_mangle]
pub fn __aeneas_require(cond: bool) {
    assert!(cond);
}
```
1. **Precondition Markers**: One or more `__aeneas_require(...)` calls appearing in the top-level statement prefix of the function body.
2. **Supporting Temporary Bindings**: Any intermediate `let` bindings computed between or before `__aeneas_require(...)` calls. Bindings needed by `__aeneas_require(...)` are included in the precondition definition `Φ'<fn_name>`, while regular `assert!` statements and bindings needed by the function body continuation are preserved in `<fn_name>`.

### Examples of What Is / Is Not Extracted

- **Extracted**:
  - Single or consecutive `__aeneas_require(...)` statements on function parameters.
  - Helper function calls or sub-expressions inside `__aeneas_require(...)` (e.g., `__aeneas_require(bar(b))`).
  - `__aeneas_require(...)` statements appearing after or interleaved with regular `assert!` statements (only the `__aeneas_require` assertions and their dependencies are extracted into `Φ'<fn_name>`).
- **Partially Extracted**:
  - In `partial_extraction`:
    ```rust
    pub fn partial_extraction(x: i32) -> i32 {
        __aeneas_require(x > 0); // Extracted into Φ'partial_extraction
        let y = x + 1;           // Kept in `partial_extraction` body
        assert!(y < 100);        // Kept in `partial_extraction` body
        y
    }
    ```
    Only `__aeneas_require(x > 0)` is extracted into `Φ'partial_extraction`, while regular `assert!` statements remain in the function body.
- **Not Extracted**:
  - Functions without `__aeneas_require` calls (e.g., `no_precondition`). Regular `assert!` statements are never treated as preconditions.
  - `__aeneas_require` calls placed inside branches or loops are rejected with an error.

## Naming Convention and Generated Definition

For a Rust function named `<fn_name>`, Aeneas generates:

1. **Precondition Definition (`Φ'<fn_name>`)**:
   - **Name**: `Φ'<fn_name>` (prefixed with `Φ'`, representing the Hoare logic precondition $\Phi$).
   - **Parameters**: Identical parameter list and types (including generics) as `<fn_name>`.
   - **Return Type**: `Result Unit`.
   - **Body**: A `do` block containing each extracted `massert` (and any local temporary bindings needed by those assertions), ending with `ok ()`.

2. **Main Function (`<fn_name>`)**:
   - Calls `Φ'<fn_name> <args>` at the start of its `do` block before executing the remaining body.

### Example Translation

From `tests/src/preconditions.rs`:
```rust
pub fn left_shift_one(v: i32) -> i32 {
    __aeneas_require(v >= 0 && v < 1024);
    let r = v << 1;
    assert!(r == v * 2);
    r
}
```

Generated Lean code in `Preconditions.lean`:
```lean
def Φ'left_shift_one (v : Std.I32) : Result Unit := do
  massert (v >= 0#i32)
  massert (v < 1024#i32)
  ok ()

def left_shift_one (v : Std.I32) : Result Std.I32 := do
  Φ'left_shift_one v
  let r ← v <<< 1#i32
  let i ← v * 2#i32
  massert (r = i)
  ok r
```

## Using Preconditions in Verification Theorems

In verification theorems (see `Properties.lean`), you can assume `h : Φ'<fn_name> args = ok ()` as a hypothesis:

```lean
theorem left_shift_one_verify (v : Std.I32) (h : Φ'left_shift_one v = ok ()) :
    left_shift_one v ⦃ _ => True ⦄ := by
  ...
```
