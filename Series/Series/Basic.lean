import Interval.Approx
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Series.Array
import Series.Analysis.Coeff
import Series.Polynomial

/-!
# Efficient truncated formal power series computations
-/

open Polynomial (X)
open Set
open scoped Polynomial Topology

variable {α β : Type}
variable {S : Type} [Semiring S]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
### Formal truncated power series
-/

/-- A truncated power series is an array of known coefficients for `1, z, z^2, ...`.
Any coefficients beyond are considered unknown. -/
structure Series (α : Type) : Type where
  c : Array α

namespace Series

/-- The number of known coefficients -/
def n (f : Series α) : ℕ :=
  f.c.size

noncomputable def poly (f : Series S) : S[X] := f.c.poly
lemma poly_def (f : Series S) : f.poly = f.c.poly := rfl

/-- The function approximation corresponding to a `Series` -/
noncomputable def f (f : Series S) : S → S :=
  f.poly.eval

/-- Series approximate the first `n` derivatives of functions -/
instance [Approx α E] : Approx (Series α) (𝕜 → E) where
  approx f f' := ∀ n (h : n < f.n),
    ContDiffAt 𝕜 n f' 0 ∧ approx (f.c[n]'h) (series_coeff n f' 0)

@[simp] lemma n_mk (c : Array α) : (⟨c⟩ : Series α).n = c.size := rfl

@[ext] lemma ext [Zero α] (f g : Series α) (n : f.n = g.n)
    (c : ∀ i < f.n, f.c.extend i = g.c.extend i) : f = g := by
  induction f
  induction g
  aesop

/-!
### `nan`, the empty series, could be anything
-/

instance : Nan (Series α) where
  nan := ⟨#[]⟩

@[simp] lemma n_nan : (nan : Series α).n = 0 := rfl

instance [Approx α 𝕜] : ApproxNan (Series α) (𝕜 → 𝕜) where
  approx_nan f' := by simp [approx, n_nan]

/-!
### Alternate characterisation of `Approx` via exact series
-/

noncomputable def exact (f : 𝕜 → E) (n : ℕ) : Series E :=
  ⟨.ofFn fun i : Fin n ↦ series_coeff i f 0⟩

@[simp] lemma n_exact (f : 𝕜 → E) (n : ℕ) : (exact f n).n = n := by
  simp only [exact, n_mk, Array.size_ofFn]

lemma approx_exact {f : 𝕜 → E} {n : ℕ} (d : ∀ i < n, ContDiffAt 𝕜 i f 0) :
    approx (Series.exact f n) f := by
  intro i lt
  simp only [n_exact] at lt
  exact ⟨d i lt, by simp only [approx, exact, Array.getElem_ofFn]⟩

/-- Series approximate series term by term -/
instance [Approx α β] : Approx (Series α) (Series β) where
  approx f f' := approx f.c f'.c

lemma approx_def [Approx α β] {f : Series α} {f' : Series β} :
    approx f f' ↔ approx f.c f'.c := by rfl

lemma approx_iff_exact [Approx α E] {f : Series α} {f' : 𝕜 → E} : approx f f' ↔
    (∀ i, i < f.n → ContDiffAt 𝕜 i f' 0) ∧ approx f (exact f' f.n) := by
  simp only [approx, exact]
  constructor
  · intro a
    refine ⟨fun i lt ↦ (a i lt).1, ?_, fun i lt ↦ ?_⟩
    · simp only [n, Array.size_ofFn]
    · simp only [Array.getElem_ofFn, a i lt]
  · intro ⟨fc,⟨e,a⟩⟩ i lt
    exact ⟨fc i lt, by simpa only [Array.getElem_ofFn] using a i lt⟩

/-!
### Adjust the length of a series
-/

/-- Up to the first `n` coefficients of a `Series` -/
def take (f : Series α) (n : ℕ) : Series α :=
  ⟨f.c.take n⟩

@[simp] lemma n_take (f : Series α) (k : ℕ) : (f.take k).n = min f.n k := by
  simp only [n, take, Array.take_eq_extract, Array.size_extract, tsub_zero, min_comm]
