import Aeneas
import Preconditions.Preconditions
open Aeneas Std Result

namespace preconditions

theorem left_shift_one_verify (v : Std.I32) (h : Φ'left_shift_one v = ok ()) :
    left_shift_one v ⦃ _ => True ⦄ := by
  unfold left_shift_one
  rw [h]
  unfold Φ'left_shift_one massert at h
  simp only [bind_tc_ok] at h ⊢
  split at h <;> try contradiction
  rename_i h0
  split at h <;> try contradiction
  rename_i h1
  step*
  have : i.bv = v.bv * 2#32 := by
    have h_eq := congrArg (BitVec.ofInt 32) i_post
    simp only [IScalar.val, BitVec.ofInt_toInt, BitVec.ofInt_mul] at h_eq
    exact h_eq
  bv_tac 32


theorem duplicate_call_after_assert_verify (h : Φ'duplicate_call_after_assert = ok ()) :
    duplicate_call_after_assert ⦃ _ => True ⦄ := by
  unfold duplicate_call_after_assert make_val
  rw [h]
  step*


theorem with_aeneas_require_verify (x y : Std.I32) (h : Φ'with_aeneas_require x y = ok ()) :
    with_aeneas_require x y ⦃ _ => True ⦄ := by
  unfold with_aeneas_require
  rw [h]
  unfold Φ'with_aeneas_require massert at h
  simp only [bind_tc_ok] at h ⊢
  split at h <;> try contradiction
  split at h <;> try contradiction
  rcases h_sum : (x + y) with ⟨sum⟩ | _ | _ <;> simp_all

end preconditions
