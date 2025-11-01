import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.RCLike.TangentCone
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Cases
import Series.Misc.Bound

/-!
# Continuous differentiability facts

For lemmas about series coefficients, see `Coeff.lean`.
-/

open Classical
open Finset (antidiagonal)
open Function (uncurry)
open MeasureTheory
open Metric (closedBall ball)
open Set
open scoped ContDiff Topology

/-!
### Smoothness of derivatives
-/

section Deriv

variable {α : Type}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

lemma iteratedDeriv_const {n : ℕ} {x : 𝕜} {c : F} :
    iteratedDeriv n (fun _ ↦ c) x = if n = 0 then c else 0 := by
  induction' n with n h generalizing c
  · simp only [iteratedDeriv_zero, ↓reduceIte]
  · simp only [iteratedDeriv_succ', deriv_const', h, ite_self, Nat.add_eq_zero, one_ne_zero,
      and_false, ↓reduceIte]

lemma ContDiffAt.comp_of_eq {f : E → F} {g : F → G} {n : WithTop ℕ∞} (x : E) {y : F}
    (hg : ContDiffAt 𝕜 n g y) (hf : ContDiffAt 𝕜 n f x) (yf : f x = y) :
    ContDiffAt 𝕜 n (g ∘ f) x := by
  rw [← yf] at hg
  exact hg.comp x hf

lemma ContDiffAt.comp_param {f : E → F} {g : E → F → G} {n : WithTop ℕ∞} (x : E)
    (hg : ContDiffAt 𝕜 n (uncurry g) (x, f x)) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun z ↦ g z (f z)) x := by
  have e : (fun z ↦ g z (f z)) = uncurry g ∘ fun z ↦ (z, f z) := rfl
  rw [e]
  exact hg.comp_of_eq _ (by fun_prop) (by rfl)

/-- Fully parameterised `deriv` is smooth. TODO: Use this in more places. -/
lemma ContDiffAt.deriv' {f : F → 𝕜 → G} {g : E → F} {h : E → 𝕜} {a : E} {n m : WithTop ℕ∞}
    (df : ContDiffAt 𝕜 n (uncurry f) (g a, h a)) (dg : ContDiffAt 𝕜 n g a) (dh : ContDiffAt 𝕜 m h a)
    (le : m + 1 ≤ n) : ContDiffAt 𝕜 m (fun p : E ↦ _root_.deriv (f (g p)) (h p)) a := by
  simp only [← fderiv_deriv]
  refine ContDiffAt.clm_apply ?_ (by fun_prop)
  refine ContDiffAt.fderiv ?_ dh le
  have e : (uncurry fun x ↦ f (g x)) = uncurry f ∘ fun p ↦ (g p.1, p.2) := rfl
  rw [e]
  apply df.comp_of_eq _ (by fun_prop) (by simp)

@[fun_prop] lemma ContDiffAt.swap {n : WithTop ℕ∞} (p : E × F) : ContDiffAt 𝕜 n Prod.swap p := by
  have e : (Prod.swap : E × F → F × E) = fun p ↦ (p.2, p.1) := rfl
  rw [e]
  fun_prop

@[fun_prop] lemma ContDiffAt.flip {n : WithTop ℕ∞} {f : E → F → G} {p : F × E}
    (df : ContDiffAt 𝕜 n (uncurry f) p.swap) : ContDiffAt 𝕜 n (uncurry (flip f)) p := by
  have e : uncurry (_root_.flip f) = uncurry f ∘ Prod.swap := rfl
  rw [e]
  fun_prop

lemma ContDiffAt.deriv {f : 𝕜 → E} {x : 𝕜} {n m : WithTop ℕ∞} (df : ContDiffAt 𝕜 n f x)
    (le : m + 1 ≤ n) : ContDiffAt 𝕜 m (deriv f) x := by
  have e : _root_.deriv f = fun x ↦ ContinuousLinearMap.apply 𝕜 E 1 (fderiv 𝕜 f x) := by
    ext x
    simp only [ContinuousLinearMap.apply_apply, fderiv_eq_smul_deriv, one_smul]
  rw [e]
  refine (df.fderiv_right ?_).continuousLinearMap_comp _
  norm_cast

/-- Technically lemma that lets us work with `ContDiffAt` orders that aren't `∞`, since `∞`
behaves poorly w.r.t. neighborhoods (it doesn't satisfy `ContDiffAt.eventually`). -/
lemma contDiffAt_iff_ne_infty {f : E → F} {x : E} {n : WithTop ℕ∞} :
    ContDiffAt 𝕜 n f x ↔ ∀ k : WithTop ℕ∞, k ≤ n → k ≠ ∞ → ContDiffAt 𝕜 k f x := by
  constructor
  · intro df k kn ne
    exact df.of_le kn
  · induction' n with n
    · intro h
      exact h _ (by rfl) (by simp)
    · intro h
      induction' n with n
      · simp only [ne_eq, ContDiffAt, ContDiffWithinAt, mem_univ, insert_eq_of_mem,
          nhdsWithin_univ, le_top, forall_const] at h ⊢
        exact fun i ↦ h i (by norm_cast; simp) (by simp) i (by rfl)
      · exact h _ (by rfl) (by simp)

lemma ContDiffAt.deriv_param {f : E × 𝕜 → F} {a : E × 𝕜} {n m : WithTop ℕ∞}
    (df : ContDiffAt 𝕜 n f a) (le : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun p : E × 𝕜 ↦ _root_.deriv (fun x ↦ f (p.1,x)) p.2) a := by
  rw [contDiffAt_iff_ne_infty]
  intro k km ki
  replace df : ContDiffAt 𝕜 (k + 1) f a := df.of_le (le_trans (add_le_add_right km 1) le)
  have e : (fun p : E × 𝕜 ↦ _root_.deriv (fun x ↦ f (p.1,x)) p.2) =ᶠ[𝓝 a]
      fun p ↦ ContinuousLinearMap.apply 𝕜 F (0,1) (fderiv 𝕜 f p) := by
    filter_upwards [df.eventually (by simp [ki])] with b df
    have e : (fun x ↦ f (b.1, x)) = f ∘ (fun x ↦ (b.1, x)) := rfl
    rw [← fderiv_deriv, e, fderiv_comp]
    · simp [(hasFDerivAt_prodMk_right (𝕜 := 𝕜) b.1 b.2).fderiv]
    · exact df.differentiableAt le_add_self
    · fun_prop
  apply ContDiffAt.congr_of_eventuallyEq ?_ e
  apply ContDiffAt.comp
  · fun_prop
  · exact df.fderiv_right (by norm_cast)

lemma ContDiffAt.iteratedDeriv {f : 𝕜 → E} {x : 𝕜} {n m : WithTop ℕ∞} {k : ℕ}
    (df : ContDiffAt 𝕜 n f x) (le : m + k ≤ n) : ContDiffAt 𝕜 m (iteratedDeriv k f) x := by
  induction' k with k h generalizing m
  · simp only [CharP.cast_eq_zero, add_zero] at le
    simp only [iteratedDeriv_zero]
    exact df.of_le (by simpa)
  · simp only [add_comm _ 1, Nat.cast_add, Nat.cast_add_one, CharP.cast_eq_zero, zero_add,
    ← add_assoc] at le
    simpa only [iteratedDeriv_succ] using (h (m := m + 1) le).deriv (m := m) (by rfl)

@[simp] lemma iteratedDeriv_pi_zero {x : 𝕜} {n : ℕ} : iteratedDeriv n (0 : 𝕜 → E) x = 0 := by
  induction' n with n h
  · simp only [iteratedDeriv_zero, Pi.zero_apply]
  · simp only [iteratedDeriv_succ', deriv_zero, h]

@[simp] lemma iteratedDerivWithin_pi_zero {t : Set 𝕜} {x : 𝕜} {n : ℕ} :
    iteratedDerivWithin n (0 : 𝕜 → E) t x = 0 := by
  induction' n with n h
  · simp only [iteratedDerivWithin_zero, Pi.zero_apply]
  · simp only [iteratedDerivWithin_succ', derivWithin_zero, h]

@[simp] lemma iteratedDeriv_fun_zero {x : 𝕜} {n : ℕ} :
    iteratedDeriv n (fun _ : 𝕜 ↦ (0 : E)) x = 0 := by
  apply iteratedDeriv_pi_zero

@[simp] lemma iteratedDerivWithin_fun_zero {t : Set 𝕜} {x : 𝕜} {n : ℕ} :
    iteratedDerivWithin n (fun _ : 𝕜 ↦ (0 : E)) t x = 0 := by
  apply iteratedDerivWithin_pi_zero

@[simp] lemma iteratedDerivWithin_sum {f : α → 𝕜 → E} {s : Finset α} {t : Set 𝕜} {x : 𝕜} {n : ℕ}
    (df : ∀ i ∈ s, ContDiffWithinAt 𝕜 n (f i) t x) (xt : x ∈ t) (ut : UniqueDiffOn 𝕜 t) :
    iteratedDerivWithin n (fun x ↦ ∑ i ∈ s, f i x) t x =
      ∑ i ∈ s, iteratedDerivWithin n (f i) t x := by
  induction' s using Finset.induction with i s m h
  · simp only [Finset.sum_empty, iteratedDerivWithin_fun_zero]
  · simp only [Finset.sum_insert m]
    simp only [Finset.mem_insert, forall_eq_or_imp] at df
    rw [iteratedDerivWithin_fun_add xt ut df.1 (ContDiffWithinAt.sum df.2), h df.2]

@[simp] lemma iteratedDeriv_sum {f : α → 𝕜 → E} {s : Finset α} {x : 𝕜} {n : ℕ}
    (df : ∀ i ∈ s, ContDiffAt 𝕜 n (f i) x) :
    iteratedDeriv n (fun x ↦ ∑ i ∈ s, f i x) x = ∑ i ∈ s, iteratedDeriv n (f i) x := by
  simp only [← iteratedDerivWithin_univ]
  apply iteratedDerivWithin_sum
  · simpa only [contDiffWithinAt_univ]
  · exact mem_univ _
  · exact uniqueDiffOn_univ

/-- Note that this requires the multiplier to be a field element, to avoid zero divisors -/
lemma iteratedDeriv_mul_const {f : 𝕜 → 𝕜} {c : 𝕜} {a : 𝕜} {n : ℕ} :
    iteratedDeriv n (fun x ↦ f x * a) c = iteratedDeriv n f c * a := by
  induction' n with n h generalizing c
  · simp only [iteratedDeriv_zero]
  · have e : iteratedDeriv n (fun x ↦ f x * a) = fun x ↦ iteratedDeriv n f x * a := by
      ext y; apply h
    rw [iteratedDeriv_succ, e, deriv_mul_const_field, ← iteratedDeriv_succ]

/-- Note that this requires the multiplier to be a field element, to avoid zero divisors -/
lemma iteratedDeriv_const_mul' {f : 𝕜 → 𝕜} {c : 𝕜} {a : 𝕜} {n : ℕ} :
    iteratedDeriv n (fun x ↦ a * f x) c = a * iteratedDeriv n f c := by
  simp only [mul_comm a, iteratedDeriv_mul_const]

lemma iteratedDeriv_monomial {x c : 𝕜} {n p : ℕ} :
    iteratedDeriv n (fun x ↦ (x - c) ^ p) x = p.descFactorial n * (x - c) ^ (p - n) := by
  induction' n with n h generalizing x
  · simp
  · have e : iteratedDeriv n (fun x ↦ (x - c) ^ p) =
        fun x ↦ p.descFactorial n * (x - c) ^ (p - n) := by
      ext y; apply h
    simp only [iteratedDeriv_succ, e, deriv_const_mul_field']
    rw [deriv_fun_pow, deriv_sub_const_fun, deriv_id'', mul_one, ← mul_assoc]
    · simp only [Nat.descFactorial_succ, Nat.cast_mul, Nat.sub_add_eq]
      ring
    · fun_prop

lemma hasDerivAt_iteratedDeriv {f : 𝕜 → E} {x : 𝕜} {n : ℕ} {m : WithTop ℕ∞}
    (df : ContDiffAt 𝕜 m f x) (le : n + 1 ≤ m) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x := by
  simp only [iteratedDeriv_succ]
  apply DifferentiableAt.hasDerivAt
  exact (df.iteratedDeriv (m := 1) (by simpa [add_comm] using le)).differentiableAt (by rfl)

end Deriv

/-!
### Smoothness of integrals
-/

section SetIntegral

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SecondCountableTopology F]
variable [MeasureSpace F] [OpensMeasurableSpace F] {μ : Measure F}
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G]

/-- Transitivity for membership in closed balls -/
lemma mem_closedBall_trans {X : Type} [MetricSpace X] {x y z : X} {r : ℝ}
    (xr : x ∈ closedBall y (r / 2)) (yr : y ∈ closedBall z (r / 2)) : x ∈ closedBall z r := by
  simp only [Metric.mem_closedBall] at xr yr ⊢
  calc dist x z
    _ ≤ dist x y + dist y z := by bound
    _ ≤ r := by linarith

omit [SecondCountableTopology F] [NormedSpace ℝ G] in
lemma ContinuousOn.integrableOn_of_compact_finite {f : F → G} {t : Set F} (fc : ContinuousOn f t)
    (tc : IsCompact t) (tm : μ t ≠ ⊤) : IntegrableOn f t μ := by
  refine ⟨?_, ?_⟩
  · exact fc.aestronglyMeasurable_of_isCompact tc tc.measurableSet
  · simp only [hasFiniteIntegral_def]
    obtain ⟨b,fb⟩ := tc.exists_bound_of_continuousOn fc
    refine lt_of_le_of_lt (setLIntegral_mono_ae (g := fun _ ↦ .ofReal b) ?_ ?_) ?_
    · simp
    · filter_upwards with x m
      rw [← ofReal_norm_eq_enorm]
      bound
    · simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
      finiteness

/-- Smoothness of integrals via differentiation under the integral sign -/
lemma ContDiffAt.setIntegral {f : E × F → G} {n : ℕ} {x : E} {t : Set F} {r : ℝ} (r0 : 0 < r)
    (df : ∀ z ∈ closedBall x r, ∀ y ∈ t, ContDiffAt 𝕜 n f (z,y)) (tc : IsCompact t) (tm : μ t ≠ ⊤) :
    ContDiffAt 𝕜 n (fun x ↦ ∫ y in t, f (x,y) ∂μ) x := by
  induction' n with n h generalizing f x G
  · simp only [CharP.cast_eq_zero, contDiffAt_zero] at df ⊢
    have fc : ContinuousOn f (closedBall x r ×ˢ t) := by
      intro ⟨z,y⟩ ⟨zr,yt⟩
      obtain ⟨u,m,fc⟩ := df z zr y yt
      exact (fc.continuousAt m).continuousWithinAt
    obtain ⟨b,fb⟩ := ((isCompact_closedBall _ _).prod tc).exists_bound_of_continuousOn fc
    refine ⟨closedBall x r, Metric.closedBall_mem_nhds _ (by bound), fun z zr ↦ ?_⟩
    simp only [mem_prod, Prod.forall] at fb
    apply MeasureTheory.continuousWithinAt_of_dominated (bound := fun _ ↦ b)
    · simp only [eventually_nhdsWithin_iff]
      filter_upwards with z zr
      apply ContinuousOn.aestronglyMeasurable_of_isCompact ?_ tc tc.measurableSet
      intro y yt
      obtain ⟨u,m,fc⟩ := df z zr y yt
      exact ((fc.continuousAt m).comp (by fun_prop)).continuousWithinAt
    · simp only [eventually_nhdsWithin_iff]
      filter_upwards with z zr
      exact ae_restrict_of_forall_mem tc.measurableSet fun y yt ↦ fb _ _ ⟨zr,yt⟩
    · exact (integrableOn_const tm).integrable
    · refine ae_restrict_of_forall_mem tc.measurableSet fun y yt ↦ ?_
      obtain ⟨u,m,fc⟩ := df z zr y yt
      exact ((fc.continuousAt m).comp_of_eq (Continuous.prodMk_left y).continuousAt
        rfl).continuousWithinAt
  · simp only [Nat.cast_add, Nat.cast_one, contDiffAt_succ_iff_hasFDerivAt] at df ⊢
    set f' : E × F → E →L[𝕜] G := fun p ↦ fderiv 𝕜 (fun x ↦ f (x,p.2)) p.1
    set d1 := fun f' : E × F →L[𝕜] G ↦ f'.comp ((ContinuousLinearMap.id 𝕜 E).prod 0)
    have df' : ContDiffOn 𝕜 n f' (closedBall x r ×ˢ t) := by
      intro ⟨z,y⟩ ⟨zr,yt⟩
      apply ContDiffAt.contDiffWithinAt
      simp only [f']
      obtain ⟨f',⟨u,m,df⟩,c⟩ := df z zr y yt
      have e : (fun p ↦ fderiv 𝕜 (fun x ↦ f (x, p.2)) p.1) =ᶠ[𝓝 (z,y)] (fun p ↦ d1 (f' p)) := by
        filter_upwards [m] with p pu
        exact ((df p pu).comp _ (by fun_prop)).fderiv
      refine ContDiffAt.congr_of_eventuallyEq ?_ e
      refine ContDiffAt.comp (g := d1) _ ?_ c
      fun_prop
    obtain ⟨b,fb⟩ := ((isCompact_closedBall _ _).prod tc).exists_bound_of_continuousOn
      df'.continuousOn
    set F' : E → E →L[𝕜] G := fun x ↦ ∫ y in t, f' (x,y) ∂μ
    refine ⟨F', ⟨closedBall x (r / 2), Metric.closedBall_mem_nhds _ (by bound), ?_⟩, ?_⟩
    · intro z zr
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ b) (ε := r / 2)
        (F := fun x y ↦ f (x,y)) (F' := fun x y ↦ f' (x,y)) (μ := μ.restrict t) (by bound)
      · filter_upwards [Metric.closedBall_mem_nhds z (ε := r / 2) (by bound)] with w wr
        apply ContinuousOn.aestronglyMeasurable _ tc.measurableSet
        intro y yt
        obtain ⟨g,⟨u,m,fg⟩,gc⟩ := df w (mem_closedBall_trans wr zr) y yt
        exact ((fg _ (mem_of_mem_nhds m)).continuousAt.comp (by fun_prop)).continuousWithinAt
      · refine ContinuousOn.integrableOn_of_compact_finite ?_ tc tm
        intro y yt
        obtain ⟨g,⟨u,m,fg⟩,gc⟩ := df z (Metric.closedBall_subset_closedBall (by bound) zr) y yt
        exact ((fg _ (mem_of_mem_nhds m)).continuousAt.comp (by fun_prop)).continuousWithinAt
      · refine ContinuousOn.aestronglyMeasurable_of_isCompact ?_ tc tc.measurableSet
        intro y yt
        refine (df'.continuousOn (z,y) ⟨?_,yt⟩).comp ?_ ?_
        · exact (Metric.closedBall_subset_closedBall (by bound) zr)
        · apply ContinuousAt.continuousWithinAt
          fun_prop
        · intro y yt
          exact ⟨Metric.closedBall_subset_closedBall (by bound) zr,yt⟩
      · refine ae_restrict_of_forall_mem tc.measurableSet fun y yt w wz ↦ ?_
        exact fb _ ⟨mem_closedBall_trans (Metric.ball_subset_closedBall wz) zr,yt⟩
      · exact integrableOn_const tm
      · refine ae_restrict_of_forall_mem tc.measurableSet fun y yt w wz ↦ ?_
        simp only [f']
        apply DifferentiableAt.hasFDerivAt
        obtain ⟨g,⟨u,m,fg⟩,gc⟩ :=
          df w (mem_closedBall_trans (Metric.ball_subset_closedBall wz) zr) y yt
        exact (fg (w,y) (mem_of_mem_nhds m)).differentiableAt.comp w (by fun_prop)
    · apply h
      intro z zr y yt
      obtain ⟨g,⟨u,m,fg⟩,gc⟩ := df z zr y yt
      have e : f' =ᶠ[𝓝 (z,y)] d1 ∘ g := by
        filter_upwards [m] with p pu
        exact ((fg p pu).comp _ (by fun_prop)).fderiv
      refine ContDiffAt.congr_of_eventuallyEq ?_ e
      fun_prop

end SetIntegral
section IntervalIntegral

/-- Smoothness of interval integrals via differentiation under the integral sign. This is
fiddly, since we need move integration over `ℝ` to integration over `𝕜`. -/
lemma ContDiffAt.intervalIntegral {𝕜 E G : Type} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [ProperSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] {f : E × 𝕜 → G} {n : ℕ} {x : E}
    {a b r : ℝ} (ab : a ≤ b) (r0 : 0 < r) :
    (∀ z ∈ closedBall x r, ∀ y ∈ Icc a b, ContDiffAt 𝕜 n f (z,y)) →
    ContDiffAt 𝕜 n (fun x ↦ ∫ y in a..b, f (x,y)) x := by
  intro df
  simp only [intervalIntegral.integral_of_le ab, ← integral_Icc_eq_integral_Ioc]
  set t : Set 𝕜 := RCLike.ofReal '' Icc a b
  have tc : IsCompact t := isCompact_Icc.image RCLike.continuous_ofReal
  have et : Icc a b = RCLike.ofReal ⁻¹' t := by simp only [RCLike.ofReal_injective.preimage_image, t]
  have tm : MeasurableSet t := tc.measurableSet
  have tf : volume.map RCLike.ofReal t ≠ ⊤ := by
    simp only [Measure.map_apply RCLike.measurable_ofReal tm, ← et, Real.volume_Icc, ne_eq,
      ENNReal.ofReal_ne_top, not_false_eq_true]
  have fm : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (fun y ↦ f (z,y))
      ((volume.restrict (Icc a b)).map RCLike.ofReal) := by
    filter_upwards [Metric.closedBall_mem_nhds x r0] with z zx
    rw [et, ← Measure.restrict_map RCLike.continuous_ofReal.measurable tm]
    refine ContinuousOn.aestronglyMeasurable_of_isCompact ?_ tc tc.measurableSet
    intro y ⟨u,m,uy⟩
    exact ((df z zx u m).continuousAt.comp_of_eq (by fun_prop) (by rw [uy])).continuousWithinAt
  have ei : (fun x ↦ ∫ y in Icc a b, f (x, y)) =ᶠ[𝓝 x]
      fun x ↦ ∫ y in t, f (x, y) ∂volume.map RCLike.ofReal := by
    filter_upwards [fm] with z m
    rw [← integral_map (RCLike.continuous_ofReal.aemeasurable) m,
      Measure.restrict_map RCLike.continuous_ofReal.measurable tm, et]
  refine ContDiffAt.congr_of_eventuallyEq ?_ ei
  refine ContDiffAt.setIntegral (𝕜 := 𝕜) (E := E) (F := 𝕜) (G := G) (n := n)
    (t := t) r0 ?_ tc tf
  intro z zx y ⟨u,m,uy⟩
  exact uy ▸ df z zx u m

end IntervalIntegral

/-!
### Joint smoothness of `dslope`
-/

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [ProperSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]

/-- Alternate route to `dslope` using integration -/
noncomputable def aslope (f : 𝕜 → F) (x s : 𝕜) : F :=
  ∫ t in 0..1, deriv f (x + t • s)

omit [ProperSpace E] [NormedSpace ℝ E] in
/-- `aslope` is `dslope` in a neighborhood of smooth points -/
lemma aslope_eq_dslope [CompleteSpace F] {f : E × 𝕜 → F} {a : E × 𝕜} (df : ContDiffAt 𝕜 1 f a) :
    (fun p : E × 𝕜 × 𝕜 ↦ aslope (fun x ↦ f (p.1,x)) p.2.1 p.2.2) =ᶠ[𝓝 (a.1,a.2,0)]
      (fun p ↦ dslope (fun x ↦ f (p.1,x)) p.2.1 (p.2.1 + p.2.2)) := by
  obtain ⟨e,e0,df⟩ := Metric.eventually_nhds_iff_ball.mp (df.eventually (by simp))
  refine Metric.eventually_nhds_iff_ball.mpr ⟨e/4, by bound, fun ⟨b,y,z⟩ m ↦ ?_⟩
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero, Prod.norm_mk, sup_lt_iff, Prod.sub_def] at m
  simp only
  by_cases z0 : z = 0
  · simp [aslope, z0]
  · rw [dslope_of_ne _ (by simp [z0]), aslope, slope]
    set fb : 𝕜 → F := fun x ↦ f (b, x)
    set g : ℝ → F := fun t ↦ z⁻¹ • fb (y + t • z)
    have hfb : ∀ y, f (b,y) = fb y := by intro; rfl
    simp only [add_sub_cancel_left, vsub_eq_sub, hfb]
    have ft : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt 𝕜 1 fb (y + t • z) := by
      intro t ⟨t0,t1⟩
      refine (df (b, y + t • z) ?_).comp _ (by fun_prop)
      simp only [Metric.mem_ball, dist_eq_norm, Prod.sub_def, Prod.norm_mk, sup_lt_iff]
      refine ⟨by bound, ?_⟩
      calc ‖y + t • z - a.2‖
        _ = ‖y - a.2 + t • z‖ := by ring_nf
        _ ≤ ‖y - a.2‖ + ‖t • z‖ := by bound
        _ = ‖y - a.2‖ + t * ‖z‖ := by simp [norm_smul, t0]
        _ ≤ e / 4 + t * ‖z‖ := by bound
        _ ≤ e / 4 + ‖z‖ := by bound
        _ ≤ e / 4 + e / 4 := by bound
        _ < e := by linarith
    have dg : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (z⁻¹ • ((1 : ℝ) • z) • deriv fb (y + t • z)) t := by
      intro t m
      apply HasDerivAt.const_smul
      apply HasDerivAt.scomp (g₁ := fb) (h := fun t ↦ y + t • z)
      · specialize ft t (Ioo_subset_Icc_self m)
        exact (ft.differentiableAt (by rfl)).hasDerivAt
      · exact ((hasDerivAt_id _).smul_const _).const_add _
    simp only [one_smul, smul_smul, inv_mul_cancel₀ z0] at dg
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by simp) _ dg]
    · simp only [one_smul, zero_smul, add_zero, smul_sub, g]
    · apply ContinuousOn.intervalIntegrable
      intro t m
      simp only [zero_le_one, uIcc_of_le] at m
      apply ContinuousAt.continuousWithinAt
      refine ContinuousAt.comp (g := deriv fb) ?_ (by fun_prop)
      exact ((ft t m).deriv (m := 0) (by rfl)).continuousAt
    · intro t m
      refine ContinuousAt.continuousWithinAt (ContinuousAt.const_smul ?_ _)
      refine ContinuousAt.comp (g := fb) ?_ (by fun_prop)
      exact (ft t m).continuousAt

/-- Smoothness of `aslope`, with `f` parameterised -/
lemma ContDiffAt.aslope_param {f : E × 𝕜 → F} {a : E × 𝕜} {n m : ℕ} (df : ContDiffAt 𝕜 n f a)
    (le : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun p : E × 𝕜 × 𝕜 ↦ aslope (fun x ↦ f (p.1,x)) p.2.1 p.2.2) (a.1,a.2,0) := by
  obtain ⟨e,e0,df⟩ := Metric.eventually_nhds_iff_ball.mp (df.eventually (by simp))
  simp only [_root_.aslope, RCLike.real_smul_eq_coe_mul]
  apply ContDiffAt.intervalIntegral (r := e / 4) (ab := zero_le_one) (r0 := by bound)
    (f := fun p : (E × 𝕜 × 𝕜) × 𝕜 ↦ _root_.deriv (fun x ↦ f (p.1.1,x)) (p.1.2.1 + p.2 * p.1.2.2))
  intro ⟨b,z,w⟩ zw t tm
  refine ContDiffAt.comp (g := fun p : E × 𝕜 ↦ _root_.deriv (fun x ↦ f (p.1,x)) p.2)
    (f := fun p : (E × 𝕜 × 𝕜) × 𝕜 ↦ (p.1.1, (p.1.2.1 + p.2 * p.1.2.2))) _ ?_ (by fun_prop)
  refine (df _ ?_).deriv_param (by norm_cast)
  simp only [Metric.mem_closedBall, dist_eq_norm, Prod.sub_def, sub_zero, Prod.norm_mk,
    sup_le_iff, mem_Icc, Metric.mem_ball, sup_lt_iff] at zw tm ⊢
  refine ⟨by bound, ?_⟩
  calc ‖z + t * w - a.2‖
    _ = ‖z - a.2 + t * w‖ := by ring_nf
    _ ≤ ‖z - a.2‖ + ‖t * w‖ := by bound
    _ = ‖z - a.2‖ + t * ‖w‖ := by simp [tm]
    _ ≤ e / 4 + 1 * (e / 4) := by bound
    _ < e := by linarith

/-- Smoothness of `dslope`, with `f` parameterised -/
lemma ContDiffAt.dslope_param [CompleteSpace F] {f : E × 𝕜 → F} {p : E × 𝕜 × 𝕜} {n m : ℕ}
    (d1 : ContDiffAt 𝕜 n f (p.1,p.2.1)) (d2 : ContDiffAt 𝕜 n f (p.1,p.2.2)) (le : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun p : E × 𝕜 × 𝕜 ↦ dslope (fun x ↦ f (p.1,x)) p.2.1 p.2.2) p := by
  obtain ⟨a,x,y⟩ := p
  by_cases xy : x = y
  · simp only [← xy] at d1 d2 ⊢
    clear xy y d2
    have e := aslope_eq_dslope (d1.of_le (by simp; omega))
    have es : (fun p ↦ _root_.dslope (fun x ↦ f (p.1,x)) p.2.1 p.2.2) =ᶠ[𝓝 (a,x,x)]
        fun p ↦ _root_.aslope (fun x ↦ f (p.1,x)) p.2.1 (p.2.2 - p.2.1) := by
      have gc : ContinuousAt (fun p ↦ (p.1, p.2.1, p.2.2 - p.2.1)) (a,x,x) := by fun_prop
      simp only [ContinuousAt, sub_self] at gc
      filter_upwards [e.comp_tendsto gc] with p e
      simp only [Function.comp_apply, add_sub_cancel] at e
      exact e.symm
    apply ContDiffAt.congr_of_eventuallyEq ?_ es
    exact (d1.aslope_param le).comp_of_eq (f := fun p : E × 𝕜 × 𝕜 ↦ (p.1, p.2.1, p.2.2 - p.2.1)) _
      (by fun_prop) (by simp)
  · have e : (fun p ↦ _root_.dslope (fun x ↦ f (p.1,x)) p.2.1 p.2.2) =ᶠ[𝓝 (a,x,y)]
        fun p ↦ slope (fun x ↦ f (p.1,x)) p.2.1 p.2.2 := by
      have ne : ∀ᶠ p in 𝓝 (a,x,y), p.2.1 ≠ p.2.2 := by
        rw [← ContinuousAt.ne_iff_eventually_ne (by fun_prop) (by fun_prop)]
        exact xy
      filter_upwards [ne] with p ne
      simp only [dslope_of_ne _ ne.symm]
    apply ContDiffAt.congr_of_eventuallyEq ?_ e
    simp only [slope_def_module]
    apply ContDiffAt.smul
    · apply ContDiffAt.inv (by fun_prop)
      simp only [ne_eq, sub_eq_zero, Ne.symm xy, not_false_eq_true]
    · apply ContDiffAt.sub
      · exact (d2.of_le (by simp; omega)).comp (f := fun p : E × 𝕜 × 𝕜 ↦ (p.1, p.2.2)) _
          (by fun_prop)
      · exact (d1.of_le (by simp; omega)).comp (f := fun p : E × 𝕜 × 𝕜 ↦ (p.1, p.2.1)) _
          (by fun_prop)

/-- Smoothness of `dslope`, parameterised diagonal version -/
lemma ContDiffAt.dslope_param_diag [CompleteSpace F] {f : E × 𝕜 → F} {a : E} {x : 𝕜} {n m : ℕ}
    (df : ContDiffAt 𝕜 n f (a,x)) (le : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun p : E × 𝕜 × 𝕜 ↦ _root_.dslope (fun x ↦ f (p.1,x)) p.2.1 p.2.2) (a,x,x) := by
  apply ContDiffAt.dslope_param df df le

/-- Smoothness of `dslope`, unparameterised version -/
lemma ContDiffAt.dslope [CompleteSpace F] {f : 𝕜 → F} {p : 𝕜 × 𝕜} {n m : ℕ} (d1 : ContDiffAt 𝕜 n f p.1)
    (d2 : ContDiffAt 𝕜 n f p.2) (le : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun p : 𝕜 × 𝕜 ↦ dslope f p.1 p.2) p := by
  set g : Unit × 𝕜 → F := fun p ↦ f p.2
  have d := ContDiffAt.dslope_param (f := g) (p := ((),p.1,p.2)) ?_ ?_ le
  · exact d.comp _ (by fun_prop)
  · exact d1.comp (f := Prod.snd) _ (by fun_prop)
  · exact d2.comp_of_eq (f := Prod.snd) _ (by fun_prop) (by rfl)

/-- Smoothness of `dslope`, unparameterised diagonal version -/
lemma ContDiffAt.dslope_diag [CompleteSpace F] {f : 𝕜 → F} {x : 𝕜} {n m : ℕ}
    (df : ContDiffAt 𝕜 n f x) (le : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun p : 𝕜 × 𝕜 ↦ _root_.dslope f p.1 p.2) (x,x) := by
  exact ContDiffAt.dslope df df le
