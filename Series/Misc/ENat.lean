import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENat.Lattice

/-!
# ENat machinery: computable defs and lemmas

Some Mathlib `ℕ∞` stuff is noncomputable, so we have to roll our own.
-/

open scoped ContDiff ENat
variable {α : Type}

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

lemma ENat.min_coe_eq_right {x : ℕ∞} {y : ℕ} (le : y ≤ x) : x.min_coe y = y := by
  induction' x with x
  all_goals simp_all

/-!
### Order lemmas
-/

lemma ENat.lt_coe_iff_succ_le_coe (x : ℕ∞) (y : ℕ) : x < y ↔ x + 1 ≤ y := by
  induction' x with x
  · simp
  · norm_cast

@[simp] lemma WithTop_ENat.add_one_le_add_one (x y : WithTop ℕ∞) : x + 1 ≤ y + 1 ↔ x ≤ y := by
  induction' x with x; · simp
  induction' y with y; · simp
  norm_cast
  rw [WithTop.add_le_add_iff_right]
  simp

@[simp] lemma ENat.cast_max (x y : ℕ) : ((max x y : ℕ) : ℕ∞) = max ↑x ↑y := by
  apply le_antisymm
  all_goals simp [Nat.le_total]

@[simp] lemma WithTop.cast_max (x y : ℕ∞) : ((max x y : ℕ∞) : WithTop ℕ∞) = max (↑x) (↑y) := by
  apply le_antisymm
  all_goals simp

@[simp] lemma WithTopENat.cast_max (x y : ℕ) : ((max x y : ℕ) : WithTop ℕ∞) = max (↑x) (↑y) := by
  apply le_antisymm
  all_goals simp [Nat.le_total]

/-!
### `WithTop ℕ∞` lemmas
-/

@[simp] lemma WithTopENat.coe_top : ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ := rfl

@[simp] lemma WithTopENat.infty_sub_one : (∞ - 1 : WithTop ℕ∞) = ∞ := rfl

/-- Via Eric Wieser at https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Can.20norm_cast.20be.20made.20to.20work.20on.20n.20-.201.20.2B.201.3F/with/543936551 -/
@[norm_cast] lemma WithTop.some_natCast [AddMonoidWithOne α] {n : ℕ} :
    (n : α) = (n : WithTop α) := rfl

@[norm_cast] lemma WithTopENat.natCast_sub (n k : ℕ) : (n : WithTop ℕ∞) - k = (n - k : ℕ) := by
  norm_cast

@[norm_cast] lemma WithTopENat.natCast_sub_ofNat (n k : ℕ) [k.AtLeastTwo] :
    (n : WithTop ℕ∞) - OfNat.ofNat k = (n - k : ℕ) := by
  norm_cast

@[norm_cast] lemma WithTopENat.natCast_sub_one (n : ℕ) : (n : WithTop ℕ∞) - 1 = (n - 1 : ℕ) := by
  norm_cast

lemma WithTopENat.sub_add_one_le {m : WithTop ℕ∞} (m0 : m ≠ 0) : m - 1 + 1 ≤ m := by
  induction' m with m; · rfl
  induction' m with m; · rfl
  norm_cast at m0 ⊢
  omega
