import Interval.Approx.Approx
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Cases

/-!
# List facts
-/

variable {α β γ : Type}

/-!
### Approx instances for lists
-/

section Approx

variable [Approx α β]

instance : Approx (List α) (List β) where
  approx f f' := List.Forall₂ approx f f'

@[approx] lemma List.approx_nil : approx ([] : List α) ([] : List β) := by
  simp only [approx, forall₂_nil_right_iff]

@[simp] lemma List.approx_cons_iff {x : α} {x' : β} {f : List α} {f' : List β} :
    approx (x :: f) (x' :: f') ↔ approx x x' ∧ approx f f' := by
  simp only [approx, forall₂_cons]

@[approx] lemma List.approx_cons {x : α} {x' : β} {f : List α} {f' : List β} (a : approx x x')
    (b : approx f f') : approx (x :: f) (x' :: f') := by
  simp only [approx, forall₂_cons]
  exact ⟨a, b⟩

@[approx] lemma List.approx_getElem {f : List α} {f' : List β} {n : ℕ} {h : n < f.length}
    {h' : n < f'.length} (a : approx f f') : approx (f[n]'h) (f'[n]'h') := by
  induction' a with x x' f f' xa fa t generalizing n
  · simp only [length_nil, not_lt_zero'] at h
  · simp only [getElem_cons]
    split_ifs with n0
    · exact xa
    · apply t

end Approx
