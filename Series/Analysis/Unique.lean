import Mathlib.Analysis.Calculus.Deriv.Prod
import Series.Analysis.Coeff
import Series.Misc.ENat

/-!
# Nondegenerate power series equations have unique solutions

We use the Faa di Bruno formula to show that nonlinear equations have unique power series solutions.
Most of the work is adding a bit of theory about `OrderedFinpartition`.
-/

open Classical
open Function (uncurry)
open Set
open scoped ContDiff Topology

variable {α : Type}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {f : 𝕜 → 𝕜 → 𝕜} {g x y : 𝕜 → 𝕜} {c gc : 𝕜}
variable {n : ℕ} {m : WithTop ℕ∞}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-!
### Iterated derivatives of `fun z ↦ f z (g z)`

Let the two partial derivatives of `f` be `f_z` and `f_g`. Then

  `∂z (f z (g z)) = f_z z (g z) + f_g z (g z) * (g' z) `

Therefore, the only way to get from `n` derivatives of the composition to `n` derivatives of `g` is
to spend the remaining derivatives on the `g' z` term. We want down the resulting expressions
without bothering to make them efficient, as all we need are these extremal terms.
-/

noncomputable section CompDeriv

lemma deriv_prodMk {f : 𝕜 → E} {g : 𝕜 → F} {c : 𝕜} (df : DifferentiableAt 𝕜 f c)
    (dg : DifferentiableAt 𝕜 g c) : deriv (fun z ↦ (f z, g z)) c = (deriv f c, deriv g c) :=
  (df.hasDerivAt.prodMk dg.hasDerivAt).deriv

/-- The derivative of `fun z ↦ f z (g z)` -/
lemma deriv_comp_param {f : 𝕜 → 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {z : 𝕜}
    (df : DifferentiableAt 𝕜 (uncurry f) (z, g z)) (dg : DifferentiableAt 𝕜 g z) :
    deriv (fun z ↦ f z (g z)) z =
      deriv (fun t ↦ f t (g z)) z + deriv (f z) (g z) * (deriv g z) := by
  have e : (fun z ↦ f z (g z)) = uncurry f ∘ fun z ↦ (z, g z) := by ext z; simp
  have e1 : (fun t ↦ f t (g z)) = uncurry f ∘ fun t ↦ (t, g z) := by ext t; simp
  have e2 : f z = uncurry f ∘ fun g ↦ (z, g) := by ext t; simp
  rw [e, e1, e2, ← fderiv_deriv, ← fderiv_deriv, ← fderiv_deriv, fderiv_comp, fderiv_comp,
    fderiv_comp]
  · simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv,
      deriv_prodMk differentiableAt_fun_id dg, deriv_id'', one_smul,
      deriv_prodMk differentiableAt_fun_id (differentiableAt_const _), deriv_const',
      deriv_prodMk (differentiableAt_const _) differentiableAt_fun_id]
    rw [mul_comm _ (deriv g z), ← smul_eq_mul, ← ContinuousLinearMap.map_smul,
      ← ContinuousLinearMap.map_add]
    simp
  all_goals fun_prop

/-- The derivative of `fun z ↦ f z (g z)` -/
lemma hasDerivAt_comp_param {f : 𝕜 → 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {z : 𝕜}
    (df : DifferentiableAt 𝕜 (uncurry f) (z, g z)) (dg : DifferentiableAt 𝕜 g z) :
    HasDerivAt (fun z ↦ f z (g z))
      (deriv (fun t ↦ f t (g z)) z + deriv (f z) (g z) * (deriv g z)) z := by
  rw [← deriv_comp_param df dg]
  exact DifferentiableAt.hasDerivAt (by fun_prop)

/-- Leading order term of the derivative of `fun z ↦ f z (g z)` -/
def leading (n : ℕ) (f : 𝕜 → 𝕜 → 𝕜) (g : 𝕜 → 𝕜) (z : 𝕜) : 𝕜 :=
  if n = 0 then f z (g z)
  else deriv (f z) (g z) * iteratedDeriv n g z

/-- Differentiating the leading order term bumps it up by one and adds some low-order slop -/
lemma hasDerivAt_leading (df : ContDiffAt 𝕜 m (uncurry f) (c, gc)) (nm : n + 1 ≤ m) :
    ∃ F : 𝕜 × 𝕜 × (Fin (n + 1) → 𝕜) → 𝕜,
      (∀ G, ContDiffAt 𝕜 (m - if n = 0 then 1 else 2) F (c, gc, G)) ∧
      ∀ g : 𝕜 → 𝕜, g c = gc → ContDiffAt 𝕜 (n + 1) g c → ∀ᶠ z in 𝓝 c,
        HasDerivAt (fun z ↦ leading n f g z)
          (leading (n + 1) f g z + F (z, g z, fun i ↦ iteratedDeriv i g z)) z := by
  have m0 : m ≠ 0 := by
    contrapose nm
    simp only [ne_eq, Decidable.not_not] at nm
    simp [nm]
  have m11 : m - 1 + 1 ≤ m := WithTopENat.sub_add_one_le m0
  simp only [leading, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
  by_cases n0 : n = 0
  · simp only [n0, CharP.cast_eq_zero, zero_add, ↓reduceIte, iteratedDeriv_one]
    refine ⟨fun p ↦ deriv (fun t ↦ f t p.2.1) p.1, ?_, ?_⟩
    · intro G
      exact df.flip.deriv' (f := fun x t ↦ f t x) (n := m) (by fun_prop) (by fun_prop) m11
    · intro g ge dg
      have pc : ContinuousAt (fun z ↦ (z, g z)) c := by fun_prop
      simp only [ContinuousAt, ge] at pc
      filter_upwards [
        pc.eventually ((df.of_le (m := 1) (le_trans (by simp) nm)).eventually (by simp)),
        dg.eventually (by simp)] with w df dg
      rw [add_comm (_ * _)]
      apply hasDerivAt_comp_param
      · exact df.differentiableAt (by norm_cast)
      · exact dg.differentiableAt (by rfl)
  · simp only [n0, ↓reduceIte]
    set F : 𝕜 × 𝕜 × (Fin (n + 1) → 𝕜) → 𝕜 := fun p ↦
      (deriv (fun t ↦ deriv (f t) p.2.1) p.1 +
      deriv (deriv (f p.1)) p.2.1 * p.2.2 ⟨1, by omega⟩) * p.2.2 ⟨n, by simp⟩
    refine ⟨F, ?_, ?_⟩
    · intro G
      have ddf : ContDiffAt 𝕜 (m - 1) (uncurry fun x t ↦ deriv (f t) x) (gc, c) :=
        df.deriv' (n := m) (by fun_prop) (by fun_prop) m11
      have m2 : (m : WithTop ℕ∞) - 2 + 1 ≤ m - 1 := by
        have e : m - 2 = m - 1 - 1 := by rw [tsub_tsub]; rfl
        rw [e]
        apply WithTopENat.sub_add_one_le
        contrapose nm
        simp only [ne_eq, tsub_eq_zero_iff_le, not_le, not_lt] at nm ⊢
        exact lt_of_lt_of_le (b := 2) (lt_of_le_of_lt nm (by decide)) (by norm_cast; omega)
      refine ContDiffAt.mul (ContDiffAt.add ?_ ?_) (by fun_prop)
      · exact ddf.deriv' (f := fun x t ↦ deriv (f t) x) (by fun_prop) (by fun_prop) m2
      · refine ContDiffAt.mul ?_ (by fun_prop)
        exact ddf.flip.deriv' (f := fun x t ↦ deriv (f x) t) (by fun_prop) (by fun_prop) m2
    · intro g ge dg
      have pc : ContinuousAt (fun z ↦ (z, g z)) c := by fun_prop
      simp only [ContinuousAt, ge] at pc
      filter_upwards [
        pc.eventually ((df.of_le (m := 2)
          (le_trans (by norm_cast; omega) nm)).eventually (by simp)),
        dg.eventually (by simp)] with w df dg
      simp only [F, add_comm (deriv (f w) (g w) * _), iteratedDeriv_one]
      apply HasDerivAt.mul
      · apply hasDerivAt_comp_param
        · exact ContDiffAt.differentiableAt (n := 1)
            (ContDiffAt.deriv' (n := 2) (df.of_le (by rfl)) (by fun_prop)
            (by fun_prop) (by rfl)) (by rfl)
        · exact dg.differentiableAt (by norm_cast; omega)
      · exact hasDerivAt_iteratedDeriv dg (by rfl)

/-- Everything but the leading order term depends on low-order derivatives of `g` -/
lemma iteratedDeriv_comp_eq_leading_add {n : ℕ} (df : ContDiffAt 𝕜 m (uncurry f) (c, gc))
    (nm : n ≤ m) :
    ∃ F : 𝕜 × 𝕜 × (Fin n → 𝕜) → 𝕜, (n = 0 → F = 0) ∧ (∀ G, ContDiffAt 𝕜 (m - n) F (c, gc, G)) ∧
      ∀ g : 𝕜 → 𝕜, g c = gc → ContDiffAt 𝕜 n g c → iteratedDeriv n (fun z ↦ f z (g z)) =ᶠ[𝓝 c]
        fun z ↦ leading n f g z + F (z, g z, fun i ↦ iteratedDeriv i g z) := by
  -- `n = 0` case: `f z (g z)`  → f_g z (g z) * g' z + f_z z (g z)`
  induction' n with n h
  · refine ⟨0, by simp, fun G ↦ ?_, fun g dg ↦ ?_⟩
    · apply contDiffAt_const
    · simp [leading]
  -- `n ≥ 1` case: `f_g z (g z) * g^(n) z + F ... → f_g z (g z) * g^(n+1) z + F' ...`
  -- In the `n = 1` case, we need `F ... = low n = 0`.
  obtain ⟨F, F0, dF, hF⟩ := h (le_trans (by simp) nm)
  clear h
  obtain ⟨L, dL, hL⟩ := hasDerivAt_leading df nm
  set F' : 𝕜 × 𝕜 × (Fin (n + 1) → 𝕜) → 𝕜 := L + fun p ↦ if n0 : n = 0 then 0 else
    fderiv 𝕜 F (p.1, p.2.1, p.2.2 ∘ Fin.castSucc) ⟨1, p.2.2 ⟨1, by omega⟩, fun i ↦ p.2.2 i.succ⟩
  refine ⟨F', by simp, ?_, fun g ge dg ↦ ?_⟩
  · intro G
    refine ContDiffAt.add ((dL G).of_le ?_) ?_
    · split_ifs with n0
      · simp [n0]
      · trans m - ↑(2 : ℕ)
        · apply tsub_le_tsub_left; norm_cast; omega
        · simp
    · split_ifs with n0
      · apply contDiffAt_const
      · simp only [Nat.cast_add, Nat.cast_one, Function.comp_def]
        refine ContDiffAt.clm_apply ?_ (by fun_prop)
        refine ((dF fun i ↦ G i.castSucc).fderiv_right ?_).comp_of_eq
          (f := fun p : 𝕜 × 𝕜 × (Fin (n + 1) → 𝕜) ↦ (p.1, p.2.1, fun i ↦ p.2.2 i.castSucc)) _ ?_ ?_
        · induction' m with m; · norm_cast
          induction' m with m; · norm_cast
          norm_cast at nm ⊢; omega
        · fun_prop
        · simp
  · specialize hF g ge (dg.of_le (by simp))
    specialize hL g ge (by simpa using dg)
    simp only [iteratedDeriv_succ, leading, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
    refine hF.deriv.trans ?_
    have pc : ContinuousAt (fun z ↦ (z, g z, fun i : Fin n ↦ iteratedDeriv i g z)) c := by
      refine continuousAt_id.prodMk (dg.continuousAt.prodMk (continuousAt_pi' fun i ↦ ?_))
      exact (dg.iteratedDeriv (m := 0) (by norm_cast; omega)).continuousAt
    have mn : 1 ≤ m - n := by
      trans ((n + 1 : ℕ) : WithTop ℕ∞) - n
      · norm_cast; omega
      · apply tsub_le_tsub_right nm
    filter_upwards [hL, pc.eventually ((ge ▸ (dF _).of_le mn).eventually (by simp)),
      dg.eventually (by simp)] with w hL dF dg
    apply HasDerivAt.deriv
    simp only [F', ← iteratedDeriv_succ, Pi.add_def, ← add_assoc, iteratedDeriv_one,
      Function.comp_def, Fin.val_succ, Fin.coe_castSucc]
    apply hL.add
    by_cases n0 : n = 0
    · simp [n0, F0]; apply hasDerivAt_zero
    · simp only [n0, dite_false]
      apply HasFDerivAt.comp_hasDerivAt
      · exact (dF.differentiableAt (by rfl)).hasFDerivAt
      · refine (hasDerivAt_id' _).prodMk (HasDerivAt.prodMk ?_ (hasDerivAt_pi.mpr fun i ↦ ?_))
        · exact (dg.differentiableAt (by norm_cast; omega)).hasDerivAt
        · exact hasDerivAt_iteratedDeriv dg (by norm_cast; omega)

/-- Low-order iterated derivatives of depend on low-order derivatives of `g`. This is a simplified
version of `iteratedDeriv_comp_eq_leading_add` when we don't need the leading term explicitly. -/
lemma iteratedDeriv_comp_eq {n : ℕ} (df : ContDiffAt 𝕜 m (uncurry f) (c, gc)) (nm : n ≤ m) :
    ∃ F : 𝕜 × (Fin (n + 1) → 𝕜) → 𝕜, ∀ g : 𝕜 → 𝕜, g c = gc → ContDiffAt 𝕜 n g c →
      iteratedDeriv n (fun z ↦ f z (g z)) =ᶠ[𝓝 c] fun z ↦ F (z, fun i ↦ iteratedDeriv i g z) := by
  by_cases n0 : n = 0
  · exact ⟨fun p ↦ f p.1 (p.2 0), fun g ge dg ↦ by simp [n0]⟩
  · obtain ⟨F, _, dF, hF⟩ := iteratedDeriv_comp_eq_leading_add df nm
    set F' : 𝕜 × (Fin (n + 1) → 𝕜) → 𝕜 := fun p ↦
      deriv (f p.1) (p.2 0) * p.2 ⟨n, by omega⟩ + F (p.1, p.2 0, p.2 ∘ Fin.castSucc)
    refine ⟨F', fun g ge dg ↦ ?_⟩
    filter_upwards [hF g ge dg] with z hF
    simp [hF, leading, n0, ↓reduceIte, F', Function.comp_def]

/-!
### Uniqueness of solutions via Faa di Bruno
-/

/-- Solutions to an equation are unique if they agree on the constant term -/
lemma solution_unique [CharZero 𝕜] (df : ContDiffAt 𝕜 m (uncurry f) (0, x 0))
    (df0 : deriv (f 0) (x 0) ≠ 0) (dx : ∀ i < n, ContDiffAt 𝕜 i x 0)
    (dy : ∀ i < n, ContDiffAt 𝕜 i y 0) (fx : (fun z ↦ f z (x z)) =ˢ[n] g)
    (fy : (fun z ↦ f z (y z)) =ˢ[n] g) (xy0 : x 0 = y 0) (nm : n ≤ m + 1) :
    x =ˢ[n] y := by
  induction' n with n h
  · simp
  · simp only [SeriesEq.succ] at fx fy ⊢
    obtain ⟨fx, dfx, d0, fx0⟩ := fx
    obtain ⟨fy, dfy, d0', fy0⟩ := fy
    have xy := h (fun i lt ↦ dx _ (by omega)) (fun i lt ↦ dy _ (by omega)) fx fy
      (le_trans (by simp) nm)
    refine ⟨xy, dx _ (by omega), dy _ (by omega), ?_⟩
    clear d0 d0' fx fy h
    by_cases n0 : n = 0
    · simp only [n0, series_coeff_zero', xy0]
    have nm' : n ≤ m := by simpa using nm
    simp only [series_coeff, smul_eq_mul, inv_eq_zero, Nat.cast_eq_zero (R := 𝕜),
      Nat.factorial_ne_zero, mul_eq_mul_left_iff, or_false] at fx0 fy0 ⊢
    obtain ⟨F, F0, dF, hF⟩ := iteratedDeriv_comp_eq_leading_add (df.of_le nm') (le_refl _)
    have Fx := fx0 ▸ (hF x rfl (dx _ (by omega))).self_of_nhds
    have Fy := fy0 ▸ (hF y (by rw [xy0]) (dy _ (by omega))).self_of_nhds
    have e := Fx.symm.trans Fy
    clear Fx Fy hF F0 dF fx0 fy0 nm' dfx dfy nm dx dy df
    have de : (fun i : Fin n ↦ iteratedDeriv i x 0) = fun i : Fin n ↦ iteratedDeriv i y 0 := by
      funext i
      exact xy.iteratedDeriv_eq _ (by simp)
    simpa [← xy0, leading, n0, ← de, df0] using e
