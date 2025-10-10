import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Series.Analysis.ContDiff

/-!
# Power series coefficients of functions
-/

open Finset (antidiagonal)
open Set
open scoped ContDiff Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {n : ℕ}

/-- The `n`th coefficient of the power series of `f` -/
noncomputable def series_coeff (n : ℕ) (f : 𝕜 → E) (x : 𝕜) : E :=
  (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f x

@[simp] lemma series_coeff_zero {x : 𝕜} : series_coeff n (0 : 𝕜 → E) x = 0 := by
  simp only [series_coeff, iteratedDeriv_pi_zero, smul_zero]

@[simp] lemma series_coeff_zero' {f : 𝕜 → E} {x : 𝕜} : series_coeff 0 f x = f x := by
  simp only [series_coeff, Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_smul]

lemma series_coeff_succ {f : 𝕜 → E} {x : 𝕜} {n : ℕ} :
    series_coeff (n + 1) f x = (n + 1 : 𝕜)⁻¹ • deriv (series_coeff n f) x:= by
  unfold series_coeff
  simp only [← iteratedDeriv_succ, deriv_fun_const_smul', smul_smul]
  refine congr_arg₂ _ ?_ rfl
  rw [← mul_inv, inv_inj, ← Nat.cast_add_one, ← Nat.cast_mul, Nat.factorial_succ]

lemma ContDiffAt.series_coeff {f : 𝕜 → E} {x : 𝕜} {n m k : ℕ} (df : ContDiffAt 𝕜 n f x)
    (le : m + k ≤ n) : ContDiffAt 𝕜 m (_root_.series_coeff k f) x :=
  (df.iteratedDeriv (by norm_cast)).const_smul _

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

/-- `series_coeff` is local -/
lemma Filter.EventuallyEq.series_coeff_eq {f g : 𝕜 → E} {x : 𝕜} {n : ℕ} (e : f =ᶠ[𝓝 x] g) :
    series_coeff n f x = series_coeff n g x := by
  simp only [series_coeff, e.iteratedDeriv_eq]

/-!
### Machinery and notation for low-order series equality
-/

variable {f f' h g g' h' : 𝕜 → E} {c : 𝕜} {n m a b : ℕ}

/-- Notation for two functions to match on low-order terms -/
def SeriesEq (f g : 𝕜 → E) (n : ℕ) (c : 𝕜) : Prop :=
  ∀ i < n, ContDiffAt 𝕜 i f c ∧ ContDiffAt 𝕜 i g c ∧ series_coeff i f c = series_coeff i g c

notation:50 f " =ˢ[" n "," c "] " g => SeriesEq f g n c
notation:50 f " =ˢ[" n "] " g => SeriesEq f g n 0

-- Accessors
lemma SeriesEq.df (e : f =ˢ[n,c] g) (i : ℕ) (lt : i < n) : ContDiffAt 𝕜 i f c := (e i lt).1
lemma SeriesEq.dg (e : f =ˢ[n,c] g) (i : ℕ) (lt : i < n) : ContDiffAt 𝕜 i g c := (e i lt).2.1
lemma SeriesEq.eq (e : f =ˢ[n,c] g) (i : ℕ) (lt : i < n) : series_coeff i f c = series_coeff i g c :=
  (e i lt).2.2
lemma SeriesEq.iteratedDeriv_eq [CharZero 𝕜] (e : f =ˢ[n,c] g) (i : ℕ) (lt : i < n) :
    iteratedDeriv i f c = iteratedDeriv i g c := by
  have h := e.eq i lt
  rwa [series_coeff, series_coeff, IsUnit.smul_left_cancel] at h
  simp [Nat.factorial_ne_zero]

/-- `SeriesEq` is reflexive for smooth functions -/
lemma SeriesEq.refl (df : ∀ i < n, ContDiffAt 𝕜 i f c) : f =ˢ[n,c] f := by
  intro i lt
  exact ⟨df i lt, df i lt, rfl⟩

/-- `n = 0` is trivial -/
@[simp] lemma SeriesEq.zero (f g : 𝕜 → E) : f =ˢ[0,c] g := by
  simp only [SeriesEq, not_lt_zero', IsEmpty.forall_iff, implies_true]

/-- `n = 0` is trivial -/
lemma SeriesEq.succ (f g : 𝕜 → E) : (f =ˢ[n + 1,c] g) ↔ (f =ˢ[n,c] g) ∧ ContDiffAt 𝕜 n f c ∧
    ContDiffAt 𝕜 n g c ∧ series_coeff n f c = series_coeff n g c := by
  simp only [SeriesEq, Nat.forall_lt_succ_right]

lemma SeriesEq.mono {f g : 𝕜 → E} {a b : ℕ} (lt : a ≤ b) (h : f =ˢ[b,c] g) : f =ˢ[a,c] g := by
  intro i lt
  exact h _ (by omega)

/-- `SeriesEq` is local on the left -/
lemma SeriesEq.congr_left (h : f =ˢ[n,c] g) (e : f =ᶠ[𝓝 c] f') : f' =ˢ[n,c] g := by
  intro i lt
  obtain ⟨df,dg,ce⟩ := h i lt
  exact ⟨df.congr_of_eventuallyEq e.symm, dg, e.series_coeff_eq ▸ ce⟩

/-- `SeriesEq` is local on the left -/
lemma seriesEq_congr_left (e : f =ᶠ[𝓝 c] f') : (f =ˢ[n,c] g) ↔ (f' =ˢ[n,c] g) :=
  ⟨fun h ↦ h.congr_left e, fun h ↦ h.congr_left e.symm⟩

/-- Switching `SeriesEq` between `f = g` and `f - g = 0` -/
lemma seriesEq_sub_eq_zero_iff (dg : ContDiffAt 𝕜 m g c) (nm : n ≤ m + 1) :
    (f - g =ˢ[n,c] 0) ↔ (f =ˢ[n,c] g) := by
  refine forall₂_congr fun i lt ↦ ?_
  have dg : ContDiffAt 𝕜 i g c := dg.of_le (by simp; omega)
  simp only [series_coeff_zero, dg, true_and]
  constructor
  · intro ⟨ds,_,si⟩
    have e : f = f - g + g := by simp
    have df : ContDiffAt 𝕜 i f c := by
      exact e ▸ ds.add dg
    simp only [df, true_and, series_coeff] at si ⊢
    simpa only [iteratedDeriv_sub df dg, smul_sub, sub_eq_zero] using si
  · intro ⟨df,fgi⟩
    refine ⟨df.sub dg, contDiffAt_const, ?_⟩
    simpa only [series_coeff, iteratedDeriv_sub df dg, smul_sub, sub_eq_zero]

/-- Zero orders add under multiplication -/
lemma SeriesEq.zero_mul_zero [CharZero 𝕜] {f g : 𝕜 → 𝕜} (df : ContDiffAt 𝕜 m f c)
    (dg : ContDiffAt 𝕜 m g c) (f0 : f =ˢ[a,c] 0) (g0 : g =ˢ[b,c] 0) (nm : n ≤ m + 1)
    (ab : n ≤ a + b) :
    f * g =ˢ[n,c] 0 := by
  intro i lt
  simp only [series_coeff_zero]
  refine ⟨(df.mul dg).of_le (by simp; omega), contDiffAt_const, ?_⟩
  --refine ⟨(df.mul dg).of_le (by norm_cast; simp; omega), contDiffAt_const, ?_⟩
  rw [series_coeff_mul]
  · apply Finset.sum_eq_zero fun p s ↦ ?_
    simp only [Finset.mem_antidiagonal] at s
    have o : p.1 < a ∨ p.2 < b := by omega
    rcases o with o | o
    · rw [f0.eq p.1 (by omega), series_coeff_zero, MulZeroClass.zero_mul]
    · rw [g0.eq p.2 (by omega), series_coeff_zero, MulZeroClass.mul_zero]
  · exact df.of_le (by simp; omega)
  · exact dg.of_le (by simp; omega)

/-- Zero orders multiply under powers -/
lemma SeriesEq.zero_pow [CharZero 𝕜] {f : 𝕜 → 𝕜} (df : ContDiffAt 𝕜 m f c) (f0 : f =ˢ[a,c] 0)
    (nm : n ≤ m + 1) (ab : n ≤ a * b) : f ^ b =ˢ[n,c] 0 := by
  induction' b with b h generalizing n
  · simp only [mul_zero, nonpos_iff_eq_zero] at ab
    simp only [pow_zero, ab, zero]
  · simp only [pow_succ]
    refine zero_mul_zero (df.pow _) df (h (n := n - a) (by omega) ?_) f0 nm (by omega)
    simpa [← mul_add_one]

lemma SeriesEq.zero_mul [CharZero 𝕜] {f g : 𝕜 → 𝕜} (df : ContDiffAt 𝕜 m f c)
    (dg : ContDiffAt 𝕜 m g c) (h : f =ˢ[n,c] 0) (nm : n ≤ m + 1) : f * g =ˢ[n,c] 0 :=
  SeriesEq.zero_mul_zero df dg h (b := 0) (by simp) nm (by simp)

lemma SeriesEq.mul_zero [CharZero 𝕜] {f g : 𝕜 → 𝕜} (df : ContDiffAt 𝕜 m f c)
    (dg : ContDiffAt 𝕜 m g c) (h : g =ˢ[n,c] 0) (nm : n ≤ m + 1) : f * g =ˢ[n,c] 0 := by
  rw [mul_comm]
  exact h.zero_mul dg df nm

lemma SeriesEq.trans (fg : f =ˢ[n,c] g) (gh : g =ˢ[n,c] h) : f =ˢ[n,c] h := by
  intro i lt
  exact ⟨(fg i lt).1, (gh i lt).2.1, (fg i lt).2.2.trans (gh i lt).2.2⟩
