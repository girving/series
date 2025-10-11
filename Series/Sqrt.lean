import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The principle branch of the complex square root
-/

open Complex (slitPlane)
open Set
open scoped ContDiff Topology

variable {z : ℂ}

noncomputable def Complex.sqrt (z : ℂ) : ℂ :=
  if z = 0 then 0 else exp (log z / 2)

lemma Complex.sqrt_def (z : ℂ) : Complex.sqrt z = if z = 0 then 0 else exp (log z / 2) := rfl

/-- Away from zero, we can remove the if -/
lemma Complex.sqrt_eventuallyEq (z0 : z ≠ 0) : sqrt =ᶠ[𝓝 z] fun z ↦ exp (log z / 2) := by
  filter_upwards [eventually_ne_nhds z0] with z z0
  simp only [sqrt_def, z0, ↓reduceIte]

/-- `sqrt` is analytic -/
lemma ContDiffAt.csqrt (m : z ∈ slitPlane) {n : WithTop ℕ∞} : ContDiffAt ℂ n Complex.sqrt z := by
  have z0 : z ≠ 0 := Complex.slitPlane_ne_zero m
  refine ContDiffAt.congr_of_eventuallyEq ?_ (Complex.sqrt_eventuallyEq z0)
  exact ((Complex.contDiffAt_log m).div_const _).cexp

@[simp] lemma Complex.sqrt_zero : sqrt 0 = 0 := by simp [sqrt_def]
@[simp] lemma Complex.sqrt_one : sqrt 1 = 1 := by simp [sqrt_def]

@[simp] lemma Complex.sq_sqrt : sqrt z ^ 2 = z := by
  by_cases z0 : z = 0
  · simp [z0]
  · simp only [sqrt_def, z0, ↓reduceIte, ← exp_nat_mul, Nat.cast_ofNat]
    ring_nf
    simp only [exp_log z0]
