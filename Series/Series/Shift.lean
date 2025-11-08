import Series.Series.Div2
import Series.Series.Inverse
import Series.Misc.Sqrt

/-!
# Multiply a series by a power of `z`

For now we don't keep the newly created high-order derivatives. We could, but it is a more work to
prove (along the lines of the proofs in `Series.Analysis.Small`), and we don't need it yet.
-/

open Set
open scoped ContDiff Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {α : Type} [SeriesScalar α] [ApproxSeries α 𝕜]

/-- Multiply by a power of `z`, discarding new high-order terms -/
def Series.shift (f : Series α) (n : ℕ) : Series α where
  c := .ofFn fun i : Fin (f.order.min_coe (f.c.size + n)) ↦
    if a : i < n then 0 else f.c[i - n]'(by have b := i.prop; simp at b; omega)
  order := f.order
  le := by simp only [Array.size_ofFn, ENat.min_coe_le_left]

instance : HShiftLeft (Series α) ℕ (Series α) where
  hShiftLeft f n := f.shift n

@[simp] lemma Series.order_shift (f : Series α) (n : ℕ) : (f <<< n).order = f.order := rfl

lemma Series.c_shift (f : Series α) (n : ℕ) :
    (f <<< n).c = .ofFn fun i : Fin (f.order.min_coe (f.c.size + n)) ↦
      if a : i < n then 0 else f.c[i - n]'(by have b := i.prop; simp at b; omega) := rfl

lemma Series.extend_shift (f : Series α) (n k : ℕ) :
    (f <<< n).extend k = if k < n ∨ f.order ≤ k then 0 else f.extend (k - n) := by
  simp only [extend_def, c_shift, Array.extend_def, Array.size_ofFn, ENat.lt_min_coe_iff,
    Array.getElem_ofFn]
  grind

variable [CharZero 𝕜]

lemma series_coeff_shift {f : 𝕜 → 𝕜} {m n k : ℕ} (fc : ContDiffAt 𝕜 m f 0) (km : k ≤ m) :
    series_coeff k (fun z ↦ z ^ n * f z) 0 = if k < n then 0 else series_coeff (k - n) f 0 := by
  have mul := series_coeff_mul (f := fun z ↦ z ^ n) (g := f) (n := k) (x := 0) (by fun_prop)
    (fc.of_le (by norm_cast))
  simp only [Pi.mul_def] at mul
  simp only [mul, series_coeff_monomial, ite_mul, one_mul, zero_mul]
  clear mul
  by_cases kn : k < n
  · simp only [kn, ↓reduceIte]
    refine Finset.sum_eq_zero fun ⟨a,b⟩ ab ↦ ?_
    simp only [Finset.mem_antidiagonal, ite_eq_right_iff] at ab ⊢
    omega
  · rw [Finset.sum_eq_single ⟨n, k-n⟩] <;> simp [kn] <;> omega

/-- Series shift approximates multiplication by `z ^ n` -/
@[approx] lemma Series.approx_shift {f : Series α} {f' : 𝕜 → 𝕜} (a : approx f f') (n : ℕ) :
    approx (f <<< n) (fun z ↦ z ^ n * f' z) := by
  intro i lt
  simp only [order_shift] at lt
  have b := a i lt
  have c := a (i - n) (lt_of_le_of_lt (by simp) lt)
  constructor
  · exact (contDiffAt_id.pow _).mul b.1
  · simp only [extend_def] at c
    simp only [extend_shift, not_le.mpr lt, or_false]
    rw [series_coeff_shift b.1 (le_refl _)]
    split_ifs with ni
    · simp only [approx_zero]
    · exact c.2
