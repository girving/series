import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Series.Analysis.Coeff
import Series.Analysis.Unique

/-!
# Congruence of power series compositions
-/

open Classical
open Finset (antidiagonal)
open Function (uncurry)
open Polynomial (C X)
open Set
open scoped Polynomial Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
variable {f f' g g' : 𝕜 → 𝕜} {n : ℕ} {c : 𝕜}

/-- Power series compositions's low-order terms are determined by low-order inputs -/
lemma SeriesEq.comp (fe : f =ˢ[n,g c] f') (ge : g =ˢ[n,c] g') : f ∘ g =ˢ[n,c] f' ∘ g' := by
  intro i lt
  have df := fe.df i lt
  have dg := ge.df i lt
  have df' := fe.dg i lt
  have dg' := ge.dg i lt
  have gc := ge.eq 0 (by omega)
  simp only [series_coeff_zero'] at gc
  refine ⟨df.comp _ dg, (gc ▸ df').comp _ dg', ?_⟩
  simp only [series_coeff]
  apply congr_arg₂ _ rfl
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition df dg (by rfl),
    iteratedDeriv_scomp_eq_sum_orderedFinpartition (gc ▸ df') dg' (by rfl)]
  refine Finset.sum_congr rfl fun p _ ↦ congr_arg₂ _ (Finset.prod_congr rfl fun i _ ↦ ?_) ?_
  · exact ge.iteratedDeriv_eq _ (lt_of_le_of_lt (p.partSize_le _) lt)
  · simp only [← gc]
    exact fe.iteratedDeriv_eq _ (lt_of_le_of_lt p.length_le lt)

lemma SeriesEq.comp_left (df : ∀ i < n, ContDiffAt 𝕜 i f (g c)) (ge : g =ˢ[n,c] g') :
    f ∘ g =ˢ[n,c] f ∘ g' :=
  SeriesEq.comp (SeriesEq.refl df) ge

lemma SeriesEq.comp_param_left {f : 𝕜 → 𝕜 → 𝕜} (df : ∀ i < n, ContDiffAt 𝕜 i (uncurry f) (c, g c))
    (ge : g =ˢ[n,c] g') : (fun z ↦ f z (g z)) =ˢ[n,c] (fun z ↦ f z (g' z)) := by
  intro i lt
  replace df := df i (by omega)
  have dg := ge.df i (by omega)
  have dg' := ge.dg i (by omega)
  have gc : g c = g' c := by simpa using ge.eq 0 (by omega)
  refine ⟨df.comp_param _ dg, (gc ▸ df).comp_param _ dg', ?_⟩
  obtain ⟨F, hF⟩ := iteratedDeriv_comp_eq df (le_refl _)
  have Fg := (hF g rfl dg).self_of_nhds
  have Fg' := (hF g' gc.symm dg').self_of_nhds
  have de : (fun i : Fin (i + 1) ↦ iteratedDeriv i g c) =
      (fun i : Fin (i + 1) ↦ iteratedDeriv i g' c) := by
    funext k
    exact ge.iteratedDeriv_eq _ (by omega)
  simp only [series_coeff, Fg, Fg', ← de]
