import Interval.Unbundled
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Series.Series.Basic
import Series.Series.Const

/-!
# Module structure on `Series`
-/

open Polynomial (X)
open Set
open scoped Polynomial Topology ENat
namespace Series

variable {α β : Type}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-!
### Definitions
-/

@[irreducible] def neg [Neg α] [Zero α] (f : Series α) : Series α :=
  f.map (-·)

@[irreducible] def add [Add α] [Zero α] (f g : Series α) : Series α :=
  let order := min f.order g.order
  let n := order.min_coe (max f.c.size g.c.size)
  ⟨.ofFn fun i : Fin n ↦ f.extend i + g.extend i, order, by simp [n]⟩

@[irreducible] def sub [Sub α] [Zero α] (f g : Series α) : Series α :=
  let order := min f.order g.order
  let n := order.min_coe (max f.c.size g.c.size)
  ⟨.ofFn fun i : Fin n ↦ f.extend i - g.extend i, order, by simp [n]⟩

@[irreducible] def smul [SMul α β] [Zero β] (s : α) (f : Series β) : Series β :=
  f.map (s • ·)

instance [Neg α] [Zero α] : Neg (Series α) := ⟨neg⟩
instance [Add α] [Zero α] : Add (Series α) := ⟨add⟩
instance [Sub α] [Zero α] : Sub (Series α) := ⟨sub⟩
instance [SMul α β] [Zero β] : SMul α (Series β) := ⟨smul⟩

/-!
### Basic properties
-/

lemma neg_def [Neg α] [Zero α] (f : Series α) : -f = f.neg := rfl
lemma add_def [Add α] [Zero α] (f g : Series α) : f + g = f.add g := rfl
lemma sub_def [Sub α] [Zero α] (f g : Series α) : f - g = f.sub g := rfl
lemma smul_def [SMul α β] [Zero β] (s : α) (f : Series β) : s • f = f.smul s := rfl

@[simp] lemma order_neg [Neg α] [Zero α] (f : Series α) : (-f).order = f.order := by
  rw [neg_def, neg, order_map]
@[simp] lemma order_smul [SMul α β] [Zero β] (s : α) (f : Series β) : (s • f).order = f.order := by
  rw [smul_def, smul, order_map]
@[simp] lemma order_add [Add α] [Zero α] (f g : Series α) :
    (f + g).order = min f.order g.order := by rw [add_def, add]
@[simp] lemma order_sub [Sub α] [Zero α] (f g : Series α) :
    (f - g).order = min f.order g.order := by rw [sub_def, sub]

/-!
### Approx instances
-/

instance instApproxNeg [Zero α] [Neg α] [NegZeroClass' α] [Approx α 𝕜] [ApproxNeg α 𝕜] :
    ApproxNeg (Series α) (𝕜 → 𝕜) where
  approx_neg {f f'} m k lt := by
    simp only [neg_def, neg, order_map, series_coeff, iteratedDeriv_neg, smul_eq_mul,
      mul_neg] at k lt ⊢
    obtain ⟨c, a⟩ := m k lt
    refine ⟨c.neg, ?_⟩
    rw [getElem_map neg_zero']
    approx

instance instApproxAdd [Zero α] [Add α] [AddZeroClass' α] [Approx α 𝕜] [ApproxAdd α 𝕜] :
    ApproxAdd (Series α) (𝕜 → 𝕜) where
  approx_add {f g f' g'} fa ga k lt := by
    simp only [add_def, add, extend_def, lt_min_iff, Array.extend_ofFn, ENat.lt_min_coe_iff,
      lt_sup_iff, dite_eq_ite] at k lt ⊢
    simp only [lt, and_self, true_and]
    obtain ⟨fc, fa⟩ := fa k lt.1
    obtain ⟨gc, ga⟩ := ga k lt.2
    have e : (if k < f.c.size ∨ k < g.c.size then f.c.extend k + g.c.extend k else 0) =
        f.c.extend k + g.c.extend k := by
      split_ifs with h
      · rfl
      · simp only [not_or, not_lt] at h
        simp only [h, Array.extend_of_le, add_zero']
    simp only [iteratedDeriv_add fc gc, smul_add, series_coeff, e]
    exact ⟨fc.add gc, by approx⟩

instance instApproxSub [Zero α] [Neg α] [Sub α] [SubZeroClass α] [Approx α 𝕜] [ApproxSub α 𝕜] :
    ApproxSub (Series α) (𝕜 → 𝕜) where
  approx_sub {f g f' g'} fa ga k lt := by
    simp only [sub_def, sub, extend_def, lt_min_iff, Array.extend_ofFn, ENat.lt_min_coe_iff,
      lt_sup_iff, dite_eq_ite] at k lt ⊢
    simp only [lt, and_self, true_and]
    obtain ⟨fc, fa⟩ := fa k lt.1
    obtain ⟨gc, ga⟩ := ga k lt.2
    have e : (if k < f.c.size ∨ k < g.c.size then f.c.extend k - g.c.extend k else 0) =
        f.c.extend k - g.c.extend k := by
      split_ifs with h
      · rfl
      · simp only [not_or, not_lt] at h
        simp only [h, Array.extend_of_le, sub_zero']
    simp only [iteratedDeriv_sub fc gc, smul_sub, series_coeff, e]
    exact ⟨fc.sub gc, by approx⟩

instance instApproxSMul [Approx β 𝕜] [Zero β] [SMulZeroClass α β] [Approx α 𝕜]
    [ApproxSMul α β 𝕜 𝕜] : ApproxSMul α (Series β) 𝕜 (𝕜 → 𝕜) where
  approx_smul {s f s' f'} sa fa k lt := by
    simp only [smul_def, smul, order_map] at k lt ⊢
    obtain ⟨fc, fa⟩ := fa k lt
    simp only [iteratedDeriv_const_smul fc, smul_comm _ s, series_coeff]
    refine ⟨fc.const_smul s, ?_⟩
    rw [getElem_map (smul_zero _)]
    approx
