import Interval.Approx
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Series.Array
import Series.Analysis.Coeff
import Series.Polynomial
import Series.ENat

/-!
# Efficient truncated formal power series computations
-/

open Polynomial (X)
open Set
open scoped Polynomial Topology

variable {α β : Type} [Zero α] [Zero β]
variable {S : Type} [Semiring S]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
### Formal truncated power series
-/

/-- A truncated power series is an array of explicit coefficients for `1, z, z^2, ...`,
padded with zeros up to `O(z ^ order)`. Any coefficients beyond are considered unknown. -/
structure Series (α : Type) [Zero α] : Type where
  /-- Explicit coefficients -/
  c : Array α
  /-- The approximation is valid up to `O(z ^ order)`, which might be `O(z ^ ∞)`. -/
  order : ℕ∞
  /-- We don't have any meaningless explicit coefficients -/
  le : c.size ≤ order

namespace Series

/-- Coefficient indexing, including zero padding -/
def extend (f : Series α) (n : ℕ) : α := f.c.extend n

lemma extend_def (f : Series α) : f.extend = f.c.extend := rfl

noncomputable def poly (f : Series S) : S[X] := f.c.poly
lemma poly_def (f : Series S) : f.poly = f.c.poly := rfl

/-- The function approximation corresponding to a `Series` -/
noncomputable def f (f : Series S) : S → S :=
  f.poly.eval

/-- Series approximate the first `n` derivatives of functions -/
instance instApprox [Approx α E] : Approx (Series α) (𝕜 → E) where
  approx f f' := ∀ (n : ℕ), n < f.order →
    ContDiffAt 𝕜 n f' 0 ∧ approx (f.extend n) (series_coeff n f' 0)

@[ext] lemma ext (f g : Series α) (o : f.order = g.order) (s : f.c.size = g.c.size)
    (c : ∀ i < f.c.size, f.c.extend i = g.c.extend i) : f = g := by
  induction' f with fc fo fle
  induction' g with gc go gle
  simp only at o c s
  have e : fc = gc := by
    ext i lt
    · exact s
    · simp only [Array.eq_extend, c i lt]
  simp only [e, o]

/-!
### `nan`, the empty series, could be anything
-/

instance : Nan (Series α) where
  nan := ⟨#[], 0, le_refl _⟩

@[simp] lemma order_nan : (nan : Series α).order = 0 := rfl

instance [Approx α 𝕜] : ApproxNan (Series α) (𝕜 → 𝕜) where
  approx_nan f' := by simp [approx, order_nan]

/-!
### Alternate characterisation of `Approx` via exact series
-/

noncomputable def exact (f : 𝕜 → E) (order : ℕ∞) (n : ℕ) : Series E :=
  ⟨.ofFn fun i : Fin (order.min_coe n) ↦ series_coeff i f 0, order,
   by simp only [Array.size_ofFn, ENat.min_coe_le_left]⟩

@[simp] lemma order_exact (f : 𝕜 → E) (order : ℕ∞) (n : ℕ) : (exact f order n).order = order := by
  simp only [exact]

@[simp] lemma size_exact (f : 𝕜 → E) (order : ℕ∞) (n : ℕ) :
    (exact f order n).c.size = order.min_coe n := by
  simp only [exact, Array.size_ofFn]

@[simp] lemma extend_exact (f : 𝕜 → E) (order : ℕ∞) (n i : ℕ) :
    (exact f order n).extend i = if i < order.min_coe n then series_coeff i f 0 else 0 := by
  simp only [exact, extend_def, Array.extend_ofFn, ENat.lt_min_coe_iff, dite_eq_ite]

/-- Implicitly approximated terms are zero -/
lemma series_coeff_eq_zero [Approx α E] [ApproxZero α E] [ApproxZeroIff α E] {f : Series α}
    {f' : 𝕜 → E} (fa : approx f f') :
    ∀ i, f.c.size ≤ i → i < f.order → series_coeff i f' 0 = 0 := by
  intro i le lt
  obtain ⟨c,a⟩ := fa i lt
  simpa only [extend_def, Array.extend_def, not_lt.mpr le, dite_false, approx_zero_iff] using a

/-- If a series approximates a function, it approximates the exact series of matching length -/
lemma approx_exact [Approx α E] [ApproxZero α E] [ApproxZeroIff α E] {f : Series α} {f' : 𝕜 → E}
    (fa : approx f f') : approx (Series.exact f' f.order f.c.size) f' := by
  intro i lt
  obtain ⟨c,a⟩ := fa i lt
  refine ⟨c, ?_⟩
  simp only [extend_def, order_exact, approx, extend_exact, ENat.lt_min_coe_iff, ite_eq_left_iff,
    not_and, not_lt] at a lt ⊢
  simp only [lt, forall_const]
  intro le
  rw [series_coeff_eq_zero fa _ le lt]

/-- Series approximate series term by term -/
instance instApproxSeries [Approx α β] : Approx (Series α) (Series β) where
  approx f f' := ∀ i : ℕ, i < min f.order f'.order → approx (f.extend i) (f'.extend i)

lemma approx_def [Approx α β] {f : Series α} {f' : Series β} :
    approx f f' ↔ ∀ i : ℕ, i < min f.order f'.order → approx (f.extend i) (f'.extend i) := by rfl

/-- Recover function approximation from exact series approximation -/
lemma approx_of_exact [Approx α E] [ApproxZero α E] {f : Series α} {f' : 𝕜 → E}
    (fc : ∀ i : ℕ, i < f.order → ContDiffAt 𝕜 i f' 0)
    (f0 : ∀ i : ℕ, f.c.size ≤ i → i < f.order → series_coeff i f' 0 = 0)
    (fa : approx f (exact f' f.order f.c.size)) :
    approx f f' := by
  intro i lt
  refine ⟨fc i lt, ?_⟩
  by_cases fi : i < f.c.size
  · specialize fa i ?_
    · simp only [order_exact, min_self, lt]
    · simpa only [extend_exact, ENat.lt_min_coe_iff, lt, fi, and_self, ↓reduceIte] using fa
  · simp only [not_lt] at fi
    simp only [extend_def, Array.extend_of_le fi, f0 i fi lt, approx_zero]

/-!
### Adjust the order of approximation (up or down)
-/

/-- Change `order` (up or down) -/
@[irreducible] def withOrder (f : Series α) (order : ℕ∞) : Series α :=
  ⟨f.c.take (order.min_coe f.c.size), order, by simp⟩

@[simp] lemma order_withOrder (f : Series α) (order : ℕ∞) : (f.withOrder order).order = order := by
  rw [withOrder.eq_def]

/-!
### Map all explicit coefficients
-/

@[irreducible] def map (f : α → β) (g : Series α) : Series β :=
  ⟨g.c.map f, g.order, by simp only [Array.size_map, g.le]⟩

@[simp] lemma order_map (f : α → β) (g : Series α) : (g.map f).order = g.order := by
  simp only [map]

lemma getElem_map {f : α → β} {g : Series α} {n : ℕ} (f0 : f 0 = 0) :
    (g.map f).extend n = f (g.extend n) := by
  simp only [f0, map, extend_def, Array.extend_def, Array.size_map, Array.getElem_map, apply_dite f]

lemma coeff_poly {f : Series S} {n : ℕ} : f.poly.coeff n = f.extend n := by
  simp only [poly, ← Array.extend_eq_coeff_poly, extend_def]
