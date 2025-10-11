import Series.Series.Div2
import Series.Series.Inverse
import Series.Sqrt

/-!
# Power series square roots using Newton's method

Square roots are given by

  `f x = x^2 - y`
  `f' x = 2x`
  `x - f x / f' x = x - (x^2 - y) / 2x = x - (x/2 - y/2x) = (x - y/x) / 2`

We restrict to the monic case for simplicity.
-/

open Set
open scoped ContDiff Topology

variable {α : Type} [SeriesScalar α] [ApproxSeries α ℂ] [Div2 α] [ApproxDiv2 α ℂ]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- Newton iteration for monic series square root -/
def sqrt_newton (y : Series α) : Newton α where
  order := y.order.toNat
  start := 1
  step x := div2 (x + y * x.inv 1)
  order_step f le := by
    simp only [Series.order_div2, Series.order_add, Series.order_mul, Series.order_inv, inf_eq_left,
      le_inf_iff]
    generalize f.order = o at le
    induction' o with o
    · simp only [← not_lt, ENat.coe_lt_top, not_true_eq_false] at le
    · norm_cast at le
      simp only [ENat.toNat_coe, le_refl, and_true]
      trans ↑y.order.toNat
      · simpa
      · apply ENat.coe_toNat_le_self

@[simp] lemma pow_two_div_self {x : 𝕜} : x ^ 2 / x = x := by
  simp only [pow_two, mul_self_div_self]

/-- Newton iteration for series inversion is correct -/
lemma valid_sqrt_newton {y : Series α} {y' : ℂ → ℂ} (ay : approx y y')
    (yo : y.order ≠ 0) (y0 : y' 0 = 1) :
    (sqrt_newton y).Valid (fun _ x ↦ x ^ 2) y' 1 where
  df := by
    simp only [sqrt_newton, Function.uncurry_def]
    fun_prop
  dy := by
    simp only [sqrt_newton]
    apply (Series.contDiffAt_of_approx ay yo).of_le
    apply tsub_le_tsub_right
    norm_cast
    apply ENat.coe_toNat_le_self
  fc := by simp [y0]
  f0 := by simp
  start := by simp [sqrt_newton]
  step := by
    intro x x' xy ax o0 ole
    unfold newton_step_fun
    simp only [sqrt_newton, differentiableAt_fun_id, deriv_fun_pow, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one, mul_comm (2 : ℂ), deriv_id'', mul_one, sub_div _ _ (_ * _),
      ← div_div _ _ (2 : ℂ), pow_two_div_self, ← sub_add]
    ring_nf
    simp only [one_div, mul_comm _ (2⁻¹ : ℂ), ← mul_add]
    simp only [← div2_eq_mul]
    refine approx_div2 (approx_add ax (approx_mul ay ?_))
    exact Series.approx_inv ax (by simp [xy]) (by simp [xy])

/-- Monic series square root using Newton's method -/
def Series.sqrt (y : Series α) : Series α :=
  (sqrt_newton y).solve y.order.toNat

/-- Series inversion is conservative -/
lemma Series.approx_sqrt {y : Series α} {y' : ℂ → ℂ} (ay : approx y y')
    (y0 : y' 0 = 1) : approx y.sqrt (Complex.sqrt ∘ y') := by
  by_cases yo : y.order = 0
  · apply Series.approx_of_order_eq_zero
    rw [sqrt, Newton.order_solve, yo, ENat.toNat_zero, CharP.cast_eq_zero]
    simp only [yo, ENat.toNat_zero, CharP.cast_eq_zero, zero_le]
  have dy := Series.contDiffAt_of_approx ay yo
  have dy' : ∀ i < y.order.toNat, ContDiffAt ℂ i y' 0 := by
    intro i lt
    apply dy.of_le
    trans ↑y.order.toNat - 1
    · norm_cast; omega
    · apply tsub_le_tsub_right; norm_cast; apply ENat.coe_toNat_le_self
  have dyi : ∀ i < y.order.toNat, ContDiffAt ℂ i y'⁻¹ 0 := fun i lt ↦ (dy' i lt).inv (by simp [y0])
  apply (valid_sqrt_newton ay yo y0).approx_exact
  · simp only [sqrt_newton, le_refl]
  · simp only [Function.comp_apply, y0, Complex.sqrt_one]
  · intro i lt
    refine (ContDiffAt.csqrt ?_).comp _ (dy' i lt)
    simp only [y0, Complex.one_mem_slitPlane]
  · simp only [Function.comp_apply, Complex.sq_sqrt]
    exact SeriesEq.refl dy'
