import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Series.Series.Basic

/-!
# Module structure on `Series`
-/

open Polynomial (X)
open Set
open scoped Polynomial Topology
namespace Series

variable {α β : Type}
variable {G : Type} [AddCommGroup G]
variable {S : Type} [Semiring S]
variable {R : Type} [Ring R]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-!
### Definitions
-/

@[irreducible] def neg [Neg α] (f : Series α) : Series α :=
  ⟨f.c.map (-·)⟩

@[irreducible] def add [Add α] (f g : Series α) : Series α :=
  let n := min f.n g.n
  ⟨.ofFn fun i : Fin n ↦
    f.c[i]'(lt_of_lt_of_le i.prop (min_le_left _ _)) +
    g.c[i]'(lt_of_lt_of_le i.prop (min_le_right _ _))⟩

@[irreducible] def sub [Sub α] (f g : Series α) : Series α :=
  let n := min f.n g.n
  ⟨.ofFn fun i : Fin n ↦
    f.c[i]'(lt_of_lt_of_le i.prop (min_le_left _ _)) -
    g.c[i]'(lt_of_lt_of_le i.prop (min_le_right _ _))⟩

@[irreducible] def smul [SMul α β] (s : α) (f : Series β) : Series β :=
  ⟨f.c.map (s • ·)⟩

instance [Neg α] : Neg (Series α) := ⟨neg⟩
instance [Add α] : Add (Series α) := ⟨add⟩
instance [Sub α] : Sub (Series α) := ⟨sub⟩
instance [SMul α β] : SMul α (Series β) := ⟨smul⟩

/-!
### Basic properties
-/

lemma neg_def [Neg α] (f : Series α) : -f = f.neg := rfl
lemma add_def [Add α] (f g : Series α) : f + g = f.add g := rfl
lemma sub_def [Sub α] (f g : Series α) : f - g = f.sub g := rfl
lemma smul_def [SMul α β] (s : α) (f : Series β) : s • f = f.smul s := rfl

@[simp] lemma n_neg [Neg α] (f : Series α) : (-f).n = f.n := by
  rw [neg_def, neg]
  simp only [n, Array.size_map]
@[simp] lemma n_smul [SMul α β] (s : α) (f : Series β) : (s • f).n = f.n := by
  rw [smul_def, smul]
  simp only [n, Array.size_map]
@[simp] lemma n_add [Add α] (f g : Series α) : (f + g).n = min f.n g.n := by
  rw [add_def, add]
  simp only [n, Fin.getElem_fin, Array.size_ofFn]
@[simp] lemma n_sub [Sub α] (f g : Series α) : (f - g).n = min f.n g.n := by
  rw [sub_def, sub]
  simp only [n, Fin.getElem_fin, Array.size_ofFn]

/-!
### Approx instances
-/

instance [Approx α 𝕜] [Neg α] [ApproxNeg α 𝕜] : ApproxNeg (Series α) (𝕜 → 𝕜) where
  approx_neg {f f'} m k lt := by
    simp only [neg_def, neg, n_mk, Array.size_map, Array.getElem_map, iteratedDeriv_neg] at k lt ⊢
    obtain ⟨c, a⟩ := m k lt
    exact ⟨c.neg, by approx⟩

instance [Approx α 𝕜] [Add α] [ApproxAdd α 𝕜] : ApproxAdd (Series α) (𝕜 → 𝕜) where
  approx_add {f g f' g'} fa ga k lt := by
    simp only [add_def, add, Fin.getElem_fin, n_mk, Array.size_ofFn, lt_inf_iff,
      Array.getElem_ofFn] at k lt ⊢
    obtain ⟨fc, fa⟩ := fa k lt.1
    obtain ⟨gc, ga⟩ := ga k lt.2
    simp only [iteratedDeriv_add fc gc]
    exact ⟨fc.add gc, by approx⟩

instance [Approx α 𝕜] [Sub α] [ApproxSub α 𝕜] : ApproxSub (Series α) (𝕜 → 𝕜) where
  approx_sub {f g f' g'} fa ga k lt := by
    simp only [sub_def, sub, Fin.getElem_fin, n_mk, Array.size_ofFn, lt_inf_iff,
      Array.getElem_ofFn] at k lt ⊢
    obtain ⟨fc, fa⟩ := fa k lt.1
    obtain ⟨gc, ga⟩ := ga k lt.2
    simp only [iteratedDeriv_sub fc gc]
    exact ⟨fc.sub gc, by approx⟩

instance [Approx α 𝕜] [Approx β 𝕜] [SMul α β] [ApproxSMul α β 𝕜 𝕜] :
    ApproxSMul α (Series β) 𝕜 (𝕜 → 𝕜) where
  approx_smul {s f s' f'} sa fa k lt := by
    simp only [smul_def, smul, n_mk, Array.size_map, Array.getElem_map] at k lt ⊢
    obtain ⟨fc, fa⟩ := fa k lt
    simp only [iteratedDeriv_const_smul fc]
    exact ⟨fc.const_smul s, by approx⟩
