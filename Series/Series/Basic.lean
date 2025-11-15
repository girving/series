import Interval.Approx.Approx
import Interval.Unbundled
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Series.Analysis.Coeff
import Series.Analysis.Trunc
import Series.Misc.Array
import Series.Misc.Polynomial
import Series.Misc.ENat

/-!
# Efficient truncated formal power series computations
-/

open Polynomial (X)
open Set
open scoped ContDiff Polynomial Topology

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
  /-- The approximation is valid up to `O(z ^ order)`. -/
  order : ℕ
  /-- We don't have any meaningless explicit coefficients -/
  le : c.size ≤ order

/-- Typeclass that pulls in everything we need to define ring operations -/
class SeriesScalar (α : Type) extends Zero α, One α, Neg α, Add α,
  Sub α, Mul α, NatCast α, AddZeroClass' α, SubZeroClass α where

/-- Typeclass that pulls in everything we need for ring operations to be conservative -/
class ApproxSeries (α 𝕜 : Type) [SeriesScalar α] [NontriviallyNormedField 𝕜] extends Approx α 𝕜,
  ApproxZero α 𝕜, ApproxOne α 𝕜, ApproxZeroIff α 𝕜, ApproxAdd α 𝕜, ApproxSub α 𝕜, ApproxMul α 𝕜,
  ApproxNatCast α 𝕜 where

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

lemma congr_right [Approx α E] {f : Series α} {g g' : 𝕜 → E} (a : approx f g) {n : ℕ}
    (e : g' =ˢ[n] g) (le : f.order ≤ n) : approx f g' := by
  intro i lt
  obtain ⟨c,a⟩ := a i lt
  have lt' : i < n := by simpa only [Nat.cast_lt] using lt_of_lt_of_le lt le
  exact ⟨e.df i lt', e.eq i lt' ▸ a⟩

lemma congr_right_of_eventuallyEq [Approx α E] {f : Series α} {g g' : 𝕜 → E} (a : approx f g)
    (e : g' =ᶠ[𝓝 0] g) : approx f g' := by
  intro i lt
  obtain ⟨c,a⟩ := a i lt
  exact ⟨c.congr_of_eventuallyEq e, by rwa [e.series_coeff_eq]⟩

lemma extend_of_le {f : Series α} {i : ℕ} (le : f.order ≤ i) : f.extend i = 0 := by
  rw [extend_def, Array.extend_of_le]
  simpa only [Nat.cast_le] using le_trans f.le le

lemma contDiffAt_of_approx [Approx α E] {f : Series α} {f' : 𝕜 → E} (a : approx f f')
    (f0 : f.order ≠ 0) : ContDiffAt 𝕜 (f.order - 1) f' 0 := by
  simp only [approx] at a
  generalize f.order = o at a f0
  specialize a (o - 1) (by omega)
  norm_cast
  exact a.1

lemma approx_of_order_eq_zero [Approx α E] {f : Series α} {f' : 𝕜 → E} (o0 : f.order = 0) :
    approx f f' := by
  intro i lt
  simp only [o0, not_lt_zero'] at lt

/-!
### `nan`, the empty series, could be anything
-/

instance : Nan (Series α) where
  nan := ⟨#[], 0, le_refl _⟩

@[simp] lemma order_nan : (nan : Series α).order = 0 := rfl
@[simp] lemma c_nan : (nan : Series α).c = #[] := rfl
@[simp] lemma extend_nan (i : ℕ) : (nan : Series α).extend i = 0 := by simp [nan, extend_def]
@[simp] lemma extend_c_nan (i : ℕ) : (nan : Series α).c.extend i = 0 := by simp [nan]

instance [Approx α 𝕜] : ApproxNan (Series α) (𝕜 → 𝕜) where
  approx_nan f' := by simp [approx, order_nan]

/-!
### Alternate characterisation of `Approx` via exact series
-/

noncomputable def exact (f : 𝕜 → E) (order : ℕ) (n : ℕ) : Series E :=
  ⟨.ofFn fun i : Fin (min order n) ↦ series_coeff i f 0, order,
   by simp only [Array.size_ofFn, inf_le_left]⟩

@[simp] lemma order_exact (f : 𝕜 → E) (order : ℕ) (n : ℕ) : (exact f order n).order = order := by
  simp only [exact]

@[simp] lemma size_exact (f : 𝕜 → E) (order : ℕ) (n : ℕ) :
    (exact f order n).c.size = min order n := by
  simp only [exact, Array.size_ofFn]

@[simp] lemma extend_exact (f : 𝕜 → E) (order : ℕ) (n i : ℕ) :
    (exact f order n).extend i = if i < min order n then series_coeff i f 0 else 0 := by
  simp only [exact, extend_def, Array.extend_ofFn, dite_eq_ite]

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
  simp only [extend_def, order_exact, approx, extend_exact, lt_min_iff, ite_eq_left_iff,
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
    · simpa only [extend_exact, lt_min_iff, lt, fi, and_self, ↓reduceIte] using fa
  · simp only [not_lt] at fi
    simp only [extend_def, Array.extend_of_le fi, f0 i fi lt, approx_zero]

/-!
### Adjust the order of approximation (up or down)
-/

/-- Change `order` (up or down) -/
@[irreducible] def withOrder (f : Series α) (order : ℕ) : Series α :=
  ⟨f.c.take (min order f.c.size), order, by simp⟩

@[simp] lemma order_withOrder (f : Series α) (order : ℕ) : (f.withOrder order).order = order := by
  rw [withOrder.eq_def]

@[simp] lemma extend_withOrder (f : Series α) (order : ℕ) (i : ℕ) :
    (f.withOrder order).extend i = if i < order then f.extend i else 0 := by
  simp only [withOrder, extend_def, Array.extend_take, lt_min_iff]
  split_ifs with h0 h1 h2
  · rfl
  · simp only [h1, false_and] at h0
  · simp only [h2, true_and, not_lt] at h0
    rw [Array.extend_of_le h0]
  · rfl

lemma approx_withOrder [Approx α E] {f : Series α} {f' : 𝕜 → E} (fa : approx f f') {order : ℕ}
    (le : order ≤ f.order) : approx (f.withOrder order) f' := by
  intro i lt
  simp only [order_withOrder] at lt
  simp only [extend_withOrder, lt, ↓reduceIte]
  exact fa i (lt_of_lt_of_le lt le)

/-- Zero extensions approximate truncated series -/
@[approx] lemma approx_withOrder_seriesTrunc [CharZero 𝕜] [Approx α 𝕜] [ApproxZero α 𝕜]
    {f : Series α} {f' : 𝕜 → 𝕜} (fa : approx f f') {n : ℕ} :
    approx (f.withOrder n) (seriesTrunc f' (min f.order n) 0) := by
  intro i lt
  simp only [order_withOrder] at lt
  refine ⟨by fun_prop, ?_⟩
  simp only [extend_withOrder, lt, ↓reduceIte, series_coeff_seriesTrunc, lt_min_iff, and_true]
  split_ifs with fi
  · exact (fa i fi).2
  · simp only [not_lt] at fi
    simp only [extend_of_le fi, approx_zero]

/-- Zero extensions approximate truncated series -/
@[approx] lemma approx_withOrder_seriesTrunc' [CharZero 𝕜] [Approx α 𝕜] [ApproxZero α 𝕜]
    {f : Series α} {f' : 𝕜 → 𝕜} (fa : approx f f') {n : ℕ} (le : n ≤ f.order) :
    approx (f.withOrder n) (seriesTrunc f' n 0) := by
  simpa only [min_eq_right le] using approx_withOrder_seriesTrunc fa (n := n)

/-!
### Map all explicit coefficients
-/

@[irreducible] def map (f : α → β) (g : Series α) : Series β :=
  ⟨g.c.map f, g.order, by simp only [Array.size_map, g.le]⟩

@[simp] lemma order_map (f : α → β) (g : Series α) : (g.map f).order = g.order := by
  simp only [map]

@[simp] lemma size_map (f : α → β) (g : Series α) : (g.map f).c.size = g.c.size := by
  simp only [map, Array.size_map]

lemma extend_map {f : α → β} {g : Series α} {n : ℕ} (f0 : f 0 = 0) :
    (g.map f).extend n = f (g.extend n) := by
  simp only [f0, map, extend_def, Array.extend_def, Array.size_map, Array.getElem_map, apply_dite f]

lemma coeff_poly {f : Series S} {n : ℕ} : f.poly.coeff n = f.extend n := by
  simp only [poly, ← Array.extend_eq_coeff_poly, extend_def]
