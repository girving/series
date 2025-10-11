import Series.Series.Const

/-!
# Division by 2
-/

open Set
open scoped ContDiff Topology

variable {α 𝕜 : Type} [SeriesScalar α] [RCLike 𝕜] [ApproxSeries α 𝕜]

/-- Division by 2 -/
class Div2 α [Zero α] where
  div2 : α → α
  div2_zero : div2 (0 : α) = 0

export Div2 (div2 div2_zero)
attribute [simp] div2_zero

/-- Division by 2 for modules -/
instance {E : Type} [Zero E] [SMulZeroClass 𝕜 E] : Div2 E where
  div2 x := (2⁻¹ : 𝕜) • x
  div2_zero := smul_zero _

lemma div2_eq_smul {E : Type} [Zero E] [SMulZeroClass 𝕜 E] (x : E) : div2 x = (2⁻¹ : 𝕜) • x := rfl
lemma div2_eq_mul (x : 𝕜) : div2 x = 2⁻¹ * x := by simp [div2_eq_smul]

/-- Division by 2 is conservative -/
class ApproxDiv2 (α α' : Type) [Approx α α'] [Zero α] [Zero α'] [Div2 α] [Div2 α'] where
  approx_div2 {x : α} {x' : α'} (a : approx x x') : approx (div2 x) (div2 x')

export ApproxDiv2 (approx_div2)
attribute [approx] approx_div2

variable [Div2 α]

/-- Division by 2 for series -/
instance : Div2 (Series α) where
  div2 x := x.map Div2.div2
  div2_zero := by ext <;> simp [Series.map, Array.extend_def, Series.zero_def, Series.const]

lemma Series.div2_def (x : Series α) : Div2.div2 x = x.map Div2.div2 := rfl

@[simp] lemma Series.order_div2 (x : Series α) : (div2 x).order = x.order := by
  simp only [Series.div2_def, order_map]

instance [ApproxDiv2 α 𝕜] : ApproxDiv2 (Series α) (𝕜 → 𝕜) where
  approx_div2 {x x'} a := by
    intro i lt
    simp only [Series.order_div2] at lt
    specialize a i lt
    simp only [Series.div2_def, div2_eq_smul, Pi.smul_def]
    rw [Series.extend_map]
    · refine ⟨a.1.const_smul _, ?_⟩
      simp only [smul_eq_mul, series_coeff_const_mul]
      simp only [← smul_eq_mul, ← div2_eq_smul]
      approx
    · rw [div2_zero]
