import Interval.Approx.Div2
import Series.Series.Const

/-!
# Division by 2 for series
-/

open Set
open scoped ContDiff Topology

variable {α 𝕜 : Type} [SeriesScalar α] [RCLike 𝕜] [ApproxSeries α 𝕜] [Div2 α]

/-- Division by 2 for series -/
instance : Div2 (Series α) where
  div2 x := x.map Div2.div2

lemma Series.div2_def (x : Series α) : Div2.div2 x = x.map Div2.div2 := rfl

@[simp] lemma Series.order_div2 (x : Series α) : (div2 x).order = x.order := by
  simp only [Series.div2_def, order_map]

instance [Div2Zero α] [ApproxDiv2 α 𝕜] : ApproxDiv2 (Series α) (𝕜 → 𝕜) where
  approx_div2 {x x'} a := by
    intro i lt
    simp only [Series.order_div2] at lt
    specialize a i lt
    simp only [Series.div2_def, div2_eq_smul, Pi.smul_def]
    rw [Series.extend_map]
    · refine ⟨a.1.const_smul _, ?_⟩
      simp only [Rat.smul_def, Rat.cast_inv, Rat.cast_ofNat, series_coeff_const_mul]
      simp only [← div2_eq_mul]
      approx
    · rw [div2_zero]
