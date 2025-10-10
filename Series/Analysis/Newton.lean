import Mathlib.Analysis.Calculus.DSlope
import Series.Analysis.Coeff

/-!
# Newton's method for power series

Newton's method for scalar equations `f x = 0` is

  `x ← x - f x / f' x`

Here we prove the necessary approximate result in a purely exact setting. `Series.Series.Newton`
then uses this for computational purposes.
-/

open Function (uncurry)
open scoped Topology

variable {𝕜 : Type} [RCLike 𝕜]
variable {f : 𝕜 → 𝕜 → 𝕜}
variable {x y : 𝕜 → 𝕜} {m n k : ℕ}

noncomputable def newton_step_fun (f : 𝕜 → 𝕜 → 𝕜) (y x : 𝕜 → 𝕜) : 𝕜 → 𝕜 :=
  fun z ↦ x z - (f z (x z) - y z) / deriv (f z) (x z)

/-- Newton steps are smooth -/
lemma ContDiffAt.newton_step {m n : WithTop ℕ∞} (df : ContDiffAt 𝕜 m (uncurry f) (0, x 0))
    (df0 : _root_.deriv (f 0) (x 0) ≠ 0) (dx : ContDiffAt 𝕜 n x 0) (dy : ContDiffAt 𝕜 n y 0)
    (nm : n + 1 ≤ m) : ContDiffAt 𝕜 n (newton_step_fun f y x) 0 := by
  refine dx.sub (ContDiffAt.div ?_ ?_ df0)
  · refine ContDiffAt.sub ?_ dy
    apply ContDiffAt.comp (g := uncurry f) (f := fun z ↦ (z, x z))
    · exact df.of_le (le_trans (by simp) nm)
    · fun_prop
  · exact (df.deriv_param nm).comp (f := fun z ↦ (z, x z)) _ (by fun_prop)

/-- First-order Taylor expansion with second-order error -/
lemma first_order_taylor (f : 𝕜 → 𝕜) (c x : 𝕜) :
    f x = f c + (x - c) * deriv f c + (x - c) ^ 2 * dslope (dslope f c) c x := by
  have e0 := sub_smul_dslope f c x
  have e1 := sub_smul_dslope (dslope f c) c x
  generalize x - c = y at e0 e1
  simp only [smul_eq_mul, dslope_same] at e0 e1
  simp only [pow_two, mul_assoc, e1, mul_sub, e0]
  ring

/-- Newton steps on power series converge quadratically -/
lemma newton_step_quadratic {m : WithTop ℕ∞} (df : ContDiffAt 𝕜 m (uncurry f) (0, x 0))
    (df0 : deriv (f 0) (x 0) ≠ 0) (dx : ContDiffAt 𝕜 (n - 1) x 0) (dy : ContDiffAt 𝕜 (n - 1) y 0)
    (fx : (fun z ↦ f z (x z)) =ˢ[k] y) (nm : n + 1 ≤ m) (nk : n ≤ 2 * k) :
    (fun z ↦ f z (newton_step_fun f y x z)) =ˢ[n] y := by
  by_cases n0 : n = 0
  · simp only [n0, SeriesEq.zero]
  have k0 : 0 < k := by omega
  have s0 : newton_step_fun f y x 0 = x 0 := by
    specialize fx 0 (by omega)
    simp only [series_coeff_zero'] at fx
    simp [newton_step_fun, fx]
  have n1 : Sub.sub n 1 = n - 1 := rfl
  have dn : ContDiffAt 𝕜 (n - 1) (newton_step_fun f y x) 0 :=
    df.newton_step df0 dx dy (by refine le_trans (add_le_add_right ?_ _) nm; norm_cast; simp)
  have dfx : ContDiffAt 𝕜 (n - 1) (fun z ↦ f z (x z)) 0 := by
    apply ContDiffAt.comp (g := uncurry f) (f := fun z ↦ (z, x z))
    · exact df.of_le (le_trans (by simp; norm_cast; omega) nm)
    · fun_prop
  have df0' : ∀ᶠ z in 𝓝 0, deriv (f z) (x z) ≠ 0 := by
    apply ContinuousAt.eventually_ne
    · exact (df.deriv_param nm).continuousAt.comp (f := fun z ↦ (z, x z)) (by fun_prop)
    · exact df0
  set g : 𝕜 → 𝕜 := fun z ↦ dslope (dslope (f z) (x z)) (x z) (newton_step_fun f y x z) /
    deriv (f z) (x z) ^ 2
  have dg : ContDiffAt 𝕜 (n - 1) g 0 := by
    apply ContDiffAt.div
    · apply ContDiffAt.comp
        (g := fun p : (𝕜 × 𝕜) × 𝕜 × 𝕜 ↦ dslope (dslope (f p.1.1) p.1.2) p.2.1 p.2.2)
        (f := fun z ↦ ((z, x z), x z, newton_step_fun f y x z))
      · simp only [s0]
        refine ContDiffAt.dslope_param_diag (f := fun p : (𝕜 × 𝕜) × 𝕜 ↦ dslope (f p.1.1) p.1.2 p.2)
          (n := n) ?_ (by norm_cast; omega)
        apply ContDiffAt.comp (g := fun p : 𝕜 × 𝕜 × 𝕜 ↦ dslope (f p.1) p.2.1 p.2.2)
          (f := fun p : (𝕜 × 𝕜) × 𝕜 ↦ (p.1.1, p.1.2, p.2))
        · exact (df.of_le (by simpa)).dslope_param_diag (n := n + 1) (by omega)
        · fun_prop
      · fun_prop
    · apply ContDiffAt.pow
      apply ContDiffAt.comp (g := fun p : 𝕜 × 𝕜 ↦ deriv (f p.1) p.2) (f := fun z ↦ (z, x z))
      · exact df.deriv_param (le_trans (add_le_add_right (by simp) _) nm)
      · fun_prop
    · simp [df0]
  have e : (fun z ↦ f z (newton_step_fun f y x z) - y z) =ᶠ[𝓝 0]
      (fun z ↦ g z * (f z (x z) - y z) ^ 2) := by
    filter_upwards [df0'] with z df0'
    have d : newton_step_fun f y x z - x z = -(f z (x z) - y z) / deriv (f z) (x z) := by
      simp [newton_step_fun]; ring_nf
    simp only [first_order_taylor (f z) (x z) (newton_step_fun _ _ _ _), d, div_mul_cancel₀ _ df0',
      ← sub_eq_add_neg, div_pow, neg_sq, div_mul_comm, g]
    ring
  replace fx : (fun z ↦ f z (x z)) =ˢ[min n k] y := fx.mono (by omega)
  rw [← seriesEq_sub_eq_zero_iff dy (by norm_cast; omega), Pi.sub_def] at fx
  rw [← seriesEq_sub_eq_zero_iff dy (by norm_cast; omega), Pi.sub_def]
  rw [seriesEq_congr_left e]
  refine SeriesEq.mul_zero dg ((dfx.sub dy).pow _) ?_ (by norm_cast; omega)
  exact fx.zero_pow (dfx.sub dy) (by norm_cast; omega) (by omega)
