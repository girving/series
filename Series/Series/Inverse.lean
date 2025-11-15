import Mathlib.Analysis.Calculus.Deriv.Inv
import Series.Series.Module
import Series.Series.Mul
import Series.Series.Newton

/-!
# Power series inverses using Newton's method

Inverses are given by

  `f x = 1/x - y`
  `f' x = -1/x^2`
  `x - f x / f' x = x - (1/x - y) / (-1/x^2) = x + (x - x^2 y) = x (2 - x y)`

We mostly care about the monic case, but pass in an arbitrary "inverse of the constant term" for
generality.
-/

open Set
open scoped ContDiff Topology

variable {α 𝕜 : Type} [SeriesScalar α] [RCLike 𝕜] [ApproxSeries α 𝕜]

/-- Newton iteration for series inversion -/
def inv_newton (y : Series α) (i : α) : Newton α where
  order := y.order
  start := i
  step x := x * (.const 2 x.order - x * y)
  order_step f le := by simp [le]

/-- Newton iteration for series inversion is correct -/
lemma valid_inv_newton {y : Series α} {y' : 𝕜 → 𝕜} (ay : approx y y') {i : α}
    (yo : y.order ≠ 0) (y0 : y' 0 ≠ 0) (ai : approx i (y' 0)⁻¹) :
    (inv_newton y i).Valid (fun _ x ↦ 1 / x) y' (y' 0)⁻¹ where
  df := by
    simp only [inv_newton, one_div, Function.uncurry_def]
    exact ContDiffAt.inv (by fun_prop) (by simp [y0])
  dy := by
    simp only [inv_newton]
    exact Series.contDiffAt_of_approx ay yo
  fc := by simp
  f0 := by simp [y0]
  start := by simp [inv_newton, ai]
  step := by
    intro x x' xy ax o0 ole
    unfold newton_step_fun
    simp only [inv_newton, one_div, deriv_inv', div_neg, div_inv_eq_mul, sub_mul, neg_sub]
    have e : (x' * (2 - x' * y')) =ᶠ[𝓝 0]
        fun z ↦ x' z - (y' z * x' z ^ 2 - (x' z)⁻¹ * x' z ^ 2) := by
      filter_upwards with z
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.ofNat_apply, mul_sub, ← mul_assoc, pow_two,
        inv_mul_mul_self]
      ring
    refine Series.congr_right_of_eventuallyEq ?_ e.symm
    approx

/-- Series inversion using Newton's method. We allow passing in an arbitrary constant term to
support `ℕ` series in the monic case. -/
def Series.inv (y : Series α) (i : α) : Series α :=
  (inv_newton y i).solve y.order

/-- Series inversion is conservative -/
lemma Series.approx_inv {y : Series α} {y' : 𝕜 → 𝕜} {i : α} (ay : approx y y')
    (ai : approx i (y' 0)⁻¹) (y0 : y' 0 ≠ 0) : approx (Series.inv y i) y'⁻¹ := by
  by_cases yo : y.order = 0
  · apply Series.approx_of_order_eq_zero
    rw [inv, Newton.order_solve, yo]
    simp only [yo, zero_le]
  have dy := Series.contDiffAt_of_approx ay yo
  have dy' : ∀ i < y.order, ContDiffAt 𝕜 i y' 0 := by
    intro i lt
    exact dy.of_le (by norm_cast; omega)
  have dyi : ∀ i < y.order, ContDiffAt 𝕜 i y'⁻¹ 0 := fun i lt ↦ (dy' i lt).inv y0
  apply (valid_inv_newton ay yo y0 ai).approx_exact
  · simp only [inv_newton, le_refl]
  · simp
  · exact dyi
  · simp only [Pi.inv_apply, div_inv_eq_mul, one_mul]
    exact SeriesEq.refl dy'

@[simp] lemma Series.order_inv (y : Series α) (i : α) : (y.inv i).order = y.order := by
  rw [inv, Newton.order_solve]
  simp only [inv_newton, le_refl]
