import Series.Analysis.Coeff

/-!
# Truncate a function to low-order terms
-/

open Set
open scoped ContDiff Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {n : ℕ} {c : 𝕜}

/-- Truncate a function to low-order terms -/
noncomputable def seriesTrunc (f : 𝕜 → E) (n : ℕ) (c : 𝕜) : 𝕜 → E :=
  fun x ↦ ∑ i ∈ Finset.range n, (x - c) ^ i • series_coeff i f c

/-- Truncation is analytic -/
@[fun_prop] lemma ContDiffAt.seriesTrunc {f : 𝕜 → E} {m : WithTop ℕ∞} :
    ContDiffAt 𝕜 m (seriesTrunc f n c) c :=
  ContDiffAt.sum fun i _ ↦ by fun_prop

/-- This only works for functions into the field `𝕜`, to avoid zero divisors. Otherwise it would
require a smoothness assumption, which we prefer to leave out for now. -/
@[simp] lemma series_coeff_seriesTrunc [CharZero 𝕜] {f : 𝕜 → 𝕜} {i : ℕ} :
    series_coeff i (seriesTrunc f n c) c = if i < n then series_coeff i f c else 0 := by
  unfold seriesTrunc
  simp only [series_coeff]
  split_ifs with lt
  · apply congr_arg₂ _ rfl ?_
    rw [iteratedDeriv_sum (by fun_prop), Finset.sum_eq_single i]
    · simp only [smul_eq_mul, ← mul_assoc, iteratedDeriv_mul_const, iteratedDeriv_monomial,
        Nat.descFactorial_self, sub_self, tsub_self, pow_zero, mul_one]
      rw [mul_inv_cancel₀, one_mul]
      simp only [ne_eq, Nat.cast_eq_zero, Nat.factorial_ne_zero, not_false_eq_true]
    · intro j jn ji
      simp [iteratedDeriv_mul_const, iteratedDeriv_monomial]
      omega
    · intro m
      simp at m
      omega
  · simp only [smul_eq_mul, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero, Nat.factorial_ne_zero,
      false_or]
    rw [iteratedDeriv_sum (by fun_prop), Finset.sum_eq_zero]
    intro j m
    simp only [Finset.mem_range] at m
    simp [iteratedDeriv_mul_const, iteratedDeriv_monomial]
    omega

/-- Truncation approximates the function -/
lemma SeriesEq.trunc [CharZero 𝕜] {f : 𝕜 → 𝕜} (df : ∀ i < n, ContDiffAt 𝕜 i f 0) :
    seriesTrunc f n 0 =ˢ[n] f := by
  intro i lt
  refine ⟨ContDiffAt.seriesTrunc, df i lt, ?_⟩
  simp only [series_coeff_seriesTrunc, lt, ↓reduceIte]

lemma seriesTrunc_const [CharZero 𝕜] {f : 𝕜 → 𝕜} (n1 : 1 ≤ n) : seriesTrunc f n c c = f c := by
  have h := series_coeff_seriesTrunc (f := f) (i := 0) (n := n) (c := c)
  rwa [series_coeff_zero', if_pos (by omega), series_coeff_zero'] at h
