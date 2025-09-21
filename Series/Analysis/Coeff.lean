import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Power series coefficients of functions
-/

open Finset (antidiagonal)
open Set
open scoped Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The `n`th coefficient of the power series of `f` -/
noncomputable def series_coeff (n : ℕ) (f : 𝕜 → E) (x : 𝕜) : E :=
  (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f x

lemma series_coeff_succ {f : 𝕜 → E} {x : 𝕜} {n : ℕ} :
    series_coeff (n + 1) f x = (n + 1 : 𝕜)⁻¹ • deriv (series_coeff n f) x:= by
  unfold series_coeff
  simp only [← iteratedDeriv_succ, deriv_fun_const_smul', smul_smul]
  refine congr_arg₂ _ ?_ rfl
  rw [← mul_inv, inv_inj, ← Nat.cast_add_one, ← Nat.cast_mul, Nat.factorial_succ]

lemma ContDiffAt.deriv {f : 𝕜 → E} {x : 𝕜} {n m : ℕ} (df : ContDiffAt 𝕜 n f x)
    (le : m + 1 ≤ n) : ContDiffAt 𝕜 m (deriv f) x := by
  have e : _root_.deriv f = fun x ↦ ContinuousLinearMap.apply 𝕜 E 1 (fderiv 𝕜 f x) := by
    ext x
    simp only [ContinuousLinearMap.apply_apply, fderiv_eq_smul_deriv, one_smul]
  rw [e]
  refine (df.fderiv_right ?_).continuousLinearMap_comp _
  norm_cast

lemma ContDiffAt.iteratedDeriv {f : 𝕜 → E} {x : 𝕜} {n m k : ℕ} (df : ContDiffAt 𝕜 n f x)
    (le : m + k ≤ n) : ContDiffAt 𝕜 m (iteratedDeriv k f) x := by
  induction' k with k h generalizing m
  · simp only [add_zero] at le
    simp only [iteratedDeriv_zero]
    exact df.of_le (by simpa)
  · simp only [iteratedDeriv_succ]
    refine (h (m := m + 1) ?_).deriv ?_
    all_goals omega

lemma ContDiffAt.series_coeff {f : 𝕜 → E} {x : 𝕜} {n m k : ℕ} (df : ContDiffAt 𝕜 n f x)
    (le : m + k ≤ n) : ContDiffAt 𝕜 m (_root_.series_coeff k f) x :=
  (df.iteratedDeriv le).const_smul _

/-- Prove a `series_coeff` is differentiable -/
macro "differentiable_series_coeff" : tactic =>
  `(tactic|exact (ContDiffAt.series_coeff (m := 1) (by assumption) (by omega)).differentiableAt
      (by simp only [Nat.cast_one, le_refl]))

lemma deriv_series_coeff [CharZero 𝕜] {f : 𝕜 → E} {x : 𝕜} {k : ℕ} :
    deriv (series_coeff k f) x = (k + 1 : 𝕜) • series_coeff (k + 1) f x := by
  simp only [series_coeff_succ, smul_smul]
  rw [mul_inv_cancel₀ (by norm_cast), one_smul]

/-- Power series multiply by convolution (i.e., as polynomials) -/
lemma series_coeff_mul [CharZero 𝕜] {f g : 𝕜 → 𝕜} {x : 𝕜} {n : ℕ} (df : ContDiffAt 𝕜 n f x)
    (dg : ContDiffAt 𝕜 n g x) :
    series_coeff n (f * g) x =
      ∑ p ∈ antidiagonal n, series_coeff p.1 f x * series_coeff p.2 g x := by
  induction' n with n h generalizing x
  · simp [series_coeff]
  · have e : series_coeff n (f * g) =ᶠ[𝓝 x] fun y ↦
        ∑ p ∈ antidiagonal n, series_coeff p.1 f y * series_coeff p.2 g y := by
      filter_upwards [df.eventually (by simp), dg.eventually (by simp)] with y df dg
      specialize h (df.of_le (by simp)) (dg.of_le (by simp))
      rw [← h, series_coeff]
    simp only [series_coeff_succ, e.deriv_eq]
    rw [deriv_fun_sum]
    · simp only [Finset.smul_sum]
      generalize ht : (fun (i j : ℕ) ↦ series_coeff i f x * series_coeff j g x) = t
      have ht' : ∀ i j, series_coeff i f x * series_coeff j g x = t i j := by simp [← ht]
      simp only [smul_eq_mul, ht']
      trans ∑ p ∈ antidiagonal n, (n + 1 : 𝕜)⁻¹ * (
        (p.1 + 1) * (t (p.1 + 1) p.2) + (p.2 + 1) * (t p.1 (p.2 + 1)))
      · refine Finset.sum_congr rfl fun p m ↦ congr_arg₂ _ rfl ?_
        simp only [Finset.mem_antidiagonal] at m
        rw [deriv_fun_mul (by differentiable_series_coeff) (by differentiable_series_coeff)]
        simp only [deriv_series_coeff, smul_eq_mul, ← ht]
        ring
      · trans ∑ p ∈ antidiagonal (n + 1), (n + 1 : 𝕜)⁻¹ * (p.1 + p.2) * t p.1 p.2
        · simp only [← Finset.mul_sum, mul_assoc]
          refine congr_arg₂ _ rfl ?_
          simp only [add_mul ((_ : ℕ) : 𝕜) ((_ : ℕ) : 𝕜), Finset.sum_add_distrib]
          apply congr_arg₂
          · simp [Finset.Nat.antidiagonal_succ]
          · simp [Finset.Nat.antidiagonal_succ']
        · refine Finset.sum_congr rfl fun p m ↦ ?_
          simp only [Finset.mem_antidiagonal] at m
          norm_cast
          rw [m, inv_mul_cancel₀, one_mul]
          norm_cast
    · intro i m
      simp only [Finset.mem_antidiagonal] at m
      apply DifferentiableAt.mul <;> differentiable_series_coeff

lemma series_coeff_const {x : 𝕜} {s : E} {n : ℕ} :
    series_coeff n (fun _ ↦ s) x = if n = 0 then s else 0 := by
  induction' n with n h generalizing x
  · simp only [series_coeff, Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero,
      one_smul, ↓reduceIte]
  · have e : series_coeff n (fun x ↦ s) (𝕜 := 𝕜) = fun _ ↦ if n = 0 then s else 0 := by
      ext x; simp only [h]
    simp only [series_coeff_succ, e, deriv_const', smul_zero, Nat.add_eq_zero, one_ne_zero,
      and_false, ↓reduceIte]
