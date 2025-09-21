import Mathlib.Data.ENat.Lattice

/-!
# ENat machinery: computable defs and lemmas

Some Mathlib `ℕ∞` stuff is noncomputable, so we have to roll our own.
-/

open scoped ENat

/-!
### Make `min` computable
-/

/-- Make sure `min` is computable.
See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ENat.20is.20noncomputable/near/540108227. -/
instance : Lattice ENat := LinearOrder.toLattice

/-!
### The minimum of an `ℕ∞` and `ℕ`
-/

/-- `min` on `ℕ∞` and `ℕ` produces `ℕ` -/
def ENat.min_coe (x : ℕ∞) (y : ℕ) : ℕ := match x with
  | some x => min x y
  | ⊤ => y

@[simp] lemma ENat.top_min_coe (x : ℕ) : (⊤ : ℕ∞).min_coe x = x := by
  simp only [min_coe]

@[simp] lemma ENat.coe_min_coe (x y : ℕ) : (x : ℕ∞).min_coe y = min x y := by
  simp only [min_coe]

@[simp] lemma ENat.min_coe_le_left (x : ℕ∞) (y : ℕ) : x.min_coe y ≤ x := by
  induction' x with x
  · simp only [le_top]
  · simp only [min_coe, Nat.cast_le, inf_le_left]

@[simp] lemma ENat.min_min_coe_right (x : ℕ∞) (y : ℕ) : min (x.min_coe y) y = x.min_coe y := by
  induction' x with x
  · simp only [top_min_coe, min_self]
  · simp only [min_coe, inf_le_right, inf_of_le_left]

@[simp] lemma ENat.min_min_coe_left (x : ℕ∞) (y : ℕ) : min y (x.min_coe y) = x.min_coe y := by
  induction' x with x
  · simp only [top_min_coe, min_self]
  · simp only [min_coe, inf_le_right, inf_of_le_right]

@[simp] lemma ENat.min_min_coe_le_left (x : ℕ∞) (y : ℕ) : min (x.min_coe y) y ≤ x := by
  induction' x with x
  · simp only [le_top]
  · simp only [min_coe, inf_le_right, inf_of_le_left, Nat.cast_le, inf_le_left]

@[simp] lemma ENat.lt_min_coe_iff (x : ℕ) (y : ℕ∞) (z : ℕ) : x < y.min_coe z ↔ x < y ∧ x < z := by
  induction' y with y
  all_goals simp [min_coe]

@[simp] lemma ENat.min_coe_eq_zero_iff (x : ℕ∞) (y : ℕ) : x.min_coe y = 0 ↔ x = 0 ∨ y = 0 := by
  induction' x with x
  all_goals simp [min_coe]

@[simp] lemma ENat.zero_min_coe (y : ℕ) : (0 : ℕ∞).min_coe y = 0 := by simp [min_coe]

@[simp] lemma ENat.min_coe_zero (x : ℕ∞) : x.min_coe 0 = 0 := by
  induction' x with x
  all_goals simp [min_coe]

lemma ENat.coe_lt_min_coe_iff (x : ℕ) (y : ℕ∞) (z : ℕ) : x < y.min_coe z ↔ x < y ∧ x < z := by
  induction' y with y
  all_goals simp [min_coe]

@[simp] lemma ENat.min_coe_le_iff (x : ℕ∞) (y z : ℕ) : x.min_coe y ≤ z ↔ x ≤ z ∨ y ≤ z := by
  induction' x with x
  all_goals simp [min_coe]

@[simp] lemma ENat.min_coe_coe (x y : ℕ) : min (x : ℕ∞) y = min x y := by
  simp only [min_def, Nat.cast_le, Nat.cast_ite]

@[simp] lemma ENat.min_coe_min_coe {x y : ℕ∞} {z : ℕ} :
    x.min_coe (y.min_coe z) = (min x y).min_coe z := by
  induction' x with x
  all_goals induction' y with y
  all_goals simp [min_coe]
