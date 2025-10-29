import Mathlib.Analysis.Calculus.Taylor
import Series.Analysis.RCLike

/-!
# Low-order derivative zeros from smallness bounds
-/

open Set
open scoped ContDiff Topology

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type} [NormedAddCommGroup E]
variable {n k : ℕ}

/-- If a smooth function is small, its low-order derivatives are zero (`ℝ` version) -/
lemma Real.iteratedDeriv_eq_zero_of_small [NormedSpace ℝ E] {f : ℝ → E} {c : ℝ}
    (df : ContDiffAt ℝ n f c) (small : f =O[𝓝 c] fun x ↦ ‖x - c‖ ^ n) (kn : k < n) :
    iteratedDeriv k f c = 0 := by
  induction' k using Nat.strong_induction_on with k low
  obtain ⟨u,un,df'⟩ := df.contDiffOn (le_refl _) (by simp)
  obtain ⟨e,e0,sub⟩ := (nhds_basis_Icc_pos c).mem_iff.mp un
  have sub' : Icc c (c + e) ⊆ Icc (c - e) (c + e) := Icc_subset_Icc (by linarith) (by rfl)
  replace df' := df'.mono (sub'.trans sub)
  clear u un sub sub'
  obtain ⟨b',tay⟩ := exists_taylor_mean_remainder_bound (f := f) (n := k) (by linarith)
    (df'.of_le (by norm_cast))
  generalize hb : max 0 b' = b
  have b0 : 0 ≤ b := by simp [← hb]
  replace tay : ∀ x ∈ Icc c (c + e), ‖f x - taylorWithinEval f k (Icc c (c + e)) c x‖ ≤
      b * (x - c) ^ (k + 1) := fun x m ↦ le_trans (tay x m) (by simp at m; bound)
  clear hb b'
  have te : ∀ x, taylorWithinEval f k (Icc c (c + e)) c x =
      (x - c) ^ k • (k.factorial : ℝ)⁻¹ • iteratedDeriv k f c := by
    intro x
    rw [taylor_within_apply, Finset.sum_eq_single (a := k)]
    · rw [smul_smul, mul_comm _ _⁻¹, iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (by linarith)) (df.of_le (by norm_cast; omega)) (by simp [e0.le])]
    · intro j jk ne
      simp only [Finset.mem_range] at jk
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
        (df.of_le (by norm_cast; omega)) (by simp [e0.le]), low _ (by omega) (by omega), smul_zero]
    · simp
  simp only [te] at tay
  suffices h : (k.factorial : ℝ)⁻¹ • iteratedDeriv k f c = 0 by
    simpa [Nat.factorial_ne_zero] using h
  generalize (k.factorial : ℝ)⁻¹ • iteratedDeriv k f c = a at tay
  clear te df' df low
  replace tay : ∃ᶠ x in 𝓝 c, x ≠ c ∧ ‖f x - (x - c) ^ k • a‖ ≤ b * |x - c| ^ (k + 1) := by
    refine frequently_nhds_iff.mpr fun u cu uo ↦ ?_
    obtain ⟨d,d0,sub⟩ := Metric.isOpen_iff.mp uo c cu
    refine ⟨c + min (e / 2) (d / 2), sub ?_, ?_, ?_⟩
    · simp only [Metric.mem_ball, dist_self_add_left, norm_eq_abs]
      rw [abs_of_nonneg (by bound), min_lt_iff]
      right
      bound
    · apply ne_of_gt (by simp; bound)
    · rw [abs_of_pos (by simp; bound)]
      apply tay
      simp [e0.le]
      bound
  obtain ⟨d,d0,small'⟩ := Asymptotics.isBigO_iff'.mp small
  replace tay := tay.and_eventually small'
  clear small small' e0 e
  contrapose tay
  simp only [← norm_pos_iff] at tay
  simp only [ne_eq, norm_eq_abs, norm_pow, abs_abs, Filter.not_frequently, not_and, not_le, and_imp]
  filter_upwards [eventually_norm_sub_lt c (ε := ‖a‖ / (b + d)) (by bound),
    eventually_norm_sub_lt c (ε := 1) (by norm_num)] with x lt y1 xc le
  simp only [norm_eq_abs] at lt y1
  replace le : ‖a‖ * |x - c| ^ k - b * |x - c| ^ (k + 1) ≤ ‖f x‖ := by
    calc ‖f x‖
      _ = ‖(x - c) ^ k • a + (f x - (x - c) ^ k • a)‖ := by rw [add_sub_cancel]
      _ ≥ ‖(x - c) ^ k • a‖ - ‖f x - (x - c) ^ k • a‖ := by bound
      _ ≥ ‖(x - c) ^ k • a‖ - b * |x - c| ^ (k + 1) := by bound
      _ = ‖a‖ * |x - c| ^ k - b * |x - c| ^ (k + 1) := by simp [norm_smul, mul_comm]
  refine lt_of_lt_of_le ?_ le
  generalize hy : |x - c| = y at lt le y1
  have y0 : 0 < y := by simp only [← hy, abs_pos, ne_eq]; simpa [sub_eq_zero]
  clear hy xc x le f
  rw [lt_sub_iff_add_lt]
  have ple : y ^ (n - k) ≤ y := pow_le_of_le_one y0.le y1.le (by omega)
  calc d * y ^ n + b * y ^ (k + 1)
    _ = (d * y ^ (n - k) + b * y) * y ^ k := by
        simp only [add_mul, mul_assoc, ← pow_succ', ← pow_add]
        rw [Nat.sub_add_cancel (by omega)]
    _ ≤ (d * y + b * y) * y ^ k := by bound
    _ = (b + d) * y * y ^ k := by ring
    _ < (b + d) * (‖a‖ / (b + d)) * y ^ k := by bound
    _ = ‖a‖ * y ^ k := by rw [mul_div_cancel₀]; positivity

/-- If a smooth function is small, its low-order derivatives are zero (`RCLike` version) -/
lemma iteratedDeriv_eq_zero_of_small [NormedSpace ℝ E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {c : 𝕜 }
    (df : ContDiffAt 𝕜 n f c) (small : f =O[𝓝 c] fun x ↦ ‖x - c‖ ^ n) (kn : k < n) :
    iteratedDeriv k f c = 0 := by
  rw [iteratedDeriv_eq_iteratedDeriv_real (df.of_le (by norm_cast; omega))]
  refine Real.iteratedDeriv_eq_zero_of_small ?_ ?_ kn
  · exact (df.restrict_scalars ℝ).comp_of_eq _ (by fun_prop) (by simp)
  · have cont : ContinuousAt (fun t : ℝ ↦ c + t) 0 := by fun_prop
    simp only [ContinuousAt, map_zero, add_zero] at cont
    simpa [Function.comp_def] using small.comp_tendsto cont
