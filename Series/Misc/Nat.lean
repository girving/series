import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Cases

/-!
# `ℕ` facts
-/

@[bound] lemma Nat.log2_mono (s t : ℕ) (st : s ≤ t) : Nat.log2 s ≤ Nat.log2 t := by
  induction' s using Nat.strong_induction_on with s h generalizing t
  simp only [Nat.log2_def s, Nat.log2_def t]
  split_ifs
  · apply add_le_add_right
    apply h <;> omega
  all_goals omega

lemma Nat.two_pow_min (a b : ℕ) : 2 ^ min a b = min (2 ^ a) (2 ^ b) := by
  rcases Nat.le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Nat.pow_le_pow_right (by omega) h)]
  · rw [min_eq_right h, min_eq_right (Nat.pow_le_pow_right (by omega) h)]
