import Series.Series.Basic

/-!
# Constants to arbitrary order
-/

namespace Series

variable {α : Type} [Zero α]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A constant accurate to any desired order -/
@[irreducible] def const (s : α) (n : ℕ) : Series α :=
  if h : n = 0 then nan
  else ⟨0, .leaf s, n, by simp, by simp; omega⟩

lemma extend_const (s : α) (n : ℕ) (i : ℕ) :
    (const s n).extend_slow i = if i = 0 ∧ n ≠ 0 then s else 0 := by
  simp only [const, extend_def]
  split_ifs with h
  · aesop
  · rw [dif_neg h]
    simp_all

@[simp] lemma order_const (s : α) (n : ℕ) : (const s n).order = n := by simp [const]; aesop
@[simp] lemma size_const (s : α) (n : ℕ) : (const s n).c.size = min n 1 := by
  unfold const
  split_ifs with h
  · aesop
  · rw [dif_neg h]
    simp_all
    omega

/-- Constants represent constants -/
@[approx] lemma approx_const [Approx α E] [ApproxZero α E] (s : α) (n : ℕ) (s' : E)
    (a : approx s s') : approx (const s n) (fun _ : 𝕜 ↦ s') := by
  intro i lt
  simp only [order_const] at lt
  constructor
  · exact contDiffAt_const
  · simp only [extend_const, series_coeff_const]
    split_ifs
    · approx
    · omega
    · omega
    · approx

/-!
### Conversion from `0, 1, ℕ`
-/

@[approx] lemma approx_zero {o : ℕ} [Approx α 𝕜] [ApproxZero α 𝕜] :
    approx (const (0 : α) o) (0 : 𝕜 → 𝕜) := by
  simp only [Pi.zero_def]
  approx

@[approx] lemma approx_one {o : ℕ} [One α] [Approx α 𝕜] [ApproxZero α 𝕜] [ApproxOne α 𝕜] :
    approx (const (1 : α) o) (1 : 𝕜 → 𝕜) := by
  simp only [Pi.one_def]
  approx

@[approx] lemma approx_ofNat {n o : ℕ} [n.AtLeastTwo] [NatCast α] [Approx α 𝕜] [ApproxZero α 𝕜]
    [ApproxNatCast α 𝕜] :
    approx (const (no_index (OfNat.ofNat n : α)) o) (no_index (OfNat.ofNat n : 𝕜 → 𝕜)) := by
  apply approx_const
  simp only [OfNat.ofNat]
  apply approx_natCast
