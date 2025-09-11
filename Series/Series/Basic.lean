import Interval.Approx
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Efficient truncated formal power series computations
-/

open Polynomial (X)
open Set
open scoped Polynomial Topology

variable {α β : Type}
variable {G : Type} [AddCommGroup G]
variable {S : Type} [Semiring S]
variable {R : Type} [Ring R]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- A truncated power series is an array of known coefficients for `1, z, z^2, ...`.
Any coefficients beyond are considered unknown. -/
structure Series (α : Type) : Type where
  c : Array α

namespace Series

/-- The number of known coefficients -/
def n (f : Series α) : ℕ :=
  f.c.size

/-- The polynomial approximation corresponding to a `Series` -/
noncomputable def poly (f : Series S) : S[X] :=
  (f.c.mapIdx fun k a ↦ a • X ^ k).sum

/-- The function approximation corresponding to a `Series` -/
noncomputable def f (f : Series S) : S → S :=
  f.poly.eval

/-- Series approximate the first `n` derivatives of functions -/
instance [Approx α 𝕜] : Approx (Series α) (𝕜 → 𝕜) where
  approx f f' := ∀ n (h : n < f.n), ContDiffAt 𝕜 n f' 0 ∧ approx (f.c[n]'h) (iteratedDeriv n f' 0)

@[simp] lemma n_mk (c : Array α) : (⟨c⟩ : Series α).n = c.size := rfl

/-!
### `nan`, the empty series, could be anything
-/

instance : Nan (Series α) where
  nan := ⟨#[]⟩

@[simp] lemma n_nan : (nan : Series α).n = 0 := rfl

instance [Approx α 𝕜] : ApproxNan (Series α) (𝕜 → 𝕜) where
  approx_nan f' := by simp [approx, n_nan]
