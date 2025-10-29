import Series.Analysis.ContDiff

/-!
# `RCLike` facts
-/

open Set
open scoped ContDiff

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
variable {m : WithTop ℕ∞} {n k : ℕ} {x : ℝ}

/-- `RCLike.ofReal` is smooth -/
@[fun_prop] lemma RCLike.contDiffAt_ofReal : ContDiffAt ℝ m (RCLike.ofReal : ℝ → 𝕜) x := by
  simpa using (RCLike.ofRealCLM (K := 𝕜)).contDiff.contDiffAt (x := x)

/-- `RCLike.ofReal` is differentiable -/
@[fun_prop] lemma RCLike.differentiableAt_ofReal : DifferentiableAt ℝ (RCLike.ofReal : ℝ → 𝕜) x :=
  RCLike.contDiffAt_ofReal.differentiableAt (le_refl _)

/- `RCLike.ofReal` has derivative `1` -/
lemma RCLike.hasDerivAt_ofReal : HasDerivAt (RCLike.ofReal : ℝ → 𝕜) (1 : 𝕜) x := by
  simpa using (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt (x := x)

/- `RCLike.ofReal` has derivative `1` -/
@[simp] lemma RCLike.deriv_ofReal : deriv (RCLike.ofReal : ℝ → 𝕜) x = 1 :=
  RCLike.hasDerivAt_ofReal.deriv

/-- Express `RCLike` iterated derivatives as `ℝ` iterated derivatives -/
lemma iteratedDeriv_eq_iteratedDeriv_real {f : 𝕜 → E} {c : 𝕜} (df : ContDiffAt 𝕜 n f c) :
    iteratedDeriv n f c = iteratedDeriv n (fun t : ℝ ↦ f (c + t)) 0 := by
  induction' n with n h generalizing f
  · simp only [iteratedDeriv_zero, map_zero, add_zero]
  · simp only [iteratedDeriv_succ']
    refine Eq.trans (h (df.deriv (by norm_cast))) ?_
    apply Filter.EventuallyEq.iteratedDeriv_eq
    have cont : ContinuousAt (fun t : ℝ ↦ c + t) 0 := by fun_prop
    simp only [ContinuousAt, map_zero, add_zero] at cont
    filter_upwards [cont.eventually (df.eventually (by simp))] with t df
    have e : (fun t : ℝ ↦ f (c + t)) = f ∘ fun t : ℝ ↦ (c + t) := rfl
    rw [e, deriv.scomp]
    · simp only [deriv_const_add', RCLike.deriv_ofReal, one_smul]
    · exact df.differentiableAt (by norm_cast; omega)
    · fun_prop
