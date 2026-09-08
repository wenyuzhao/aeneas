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

end preconditions
