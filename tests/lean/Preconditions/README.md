# Precondition Extraction (`-extract-preconditions`)

When Aeneas is invoked with the `-extract-preconditions` CLI flag, it automatically extracts leading precondition assertions from Rust functions into standalone Lean definitions returning `Result Unit`.

## What Format is Identified as a Precondition

A prefix of statements at the very beginning of a Rust function body is identified as a precondition if it consists of:
1. **Assertions**: One or more consecutive `assert!(...)`, `debug_assert!(...)`, `assert_eq!(...)`, `assert_ne!(...)`, `debug_assert_eq!(...)`, or `debug_assert_ne!(...)` calls (including compound conditions such as `assert!(a && b)` that lower to multiple assertions).
2. **Supporting Temporary Bindings**: Any intermediate `let` bindings computed solely to evaluate those assertions (for example, `let b1 ← bar b` inside `assert!(bar(b))`), provided that **none** of those temporary variables are referenced in the remainder of the function body after the assertion prefix.

### Examples of What Is / Is Not Extracted

- **Extracted**:
  - Single or consecutive leading `assert!` / `debug_assert!` / `assert_eq!` / `assert_ne!` / `debug_assert_eq!` / `debug_assert_ne!` statements on function parameters.
  - Helper function calls or sub-expressions inside leading assertions (e.g., `assert!(bar(b))`).
- **Partially Extracted**:
  - In `partial_extraction`:
    ```rust
    pub fn partial_extraction(x: i32) -> i32 {
        assert!(x > 0);      // Extracted into Φ'partial_extraction
        let y = x + 1;       // `y` is used in the return value below
        assert!(y < 100);    // Kept in `partial_extraction` body
        y
    }
    ```
    Only `assert!(x > 0)` is extracted into `Φ'partial_extraction`, because `let y = x + 1` produces a variable `y` used in the function's return value.
- **Not Extracted**:
  - Assertions that appear after a computation whose result is used later in the function body (e.g., `no_precondition`).

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
    assert!(v >= 0 && v < 1024);
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
