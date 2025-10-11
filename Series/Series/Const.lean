import Series.Series.Basic

/-!
# Exact constants
-/

namespace Series

variable {α : Type} [Zero α]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A constant accurate to infinite order -/
@[coe, irreducible] def const (s : α) : Series α :=
  ⟨#[s], ⊤, by simp⟩

instance : CoeTail α (Series α) where
  coe s := const s

lemma extend_const (s : α) (i : ℕ) : (const s).extend i = if i = 0 then s else 0 := by
  simp only [const, extend_def]
  split_ifs with i0
  · rw [Array.extend_of_lt]
    · simp only [i0, List.getElem_toArray, List.getElem_cons_zero]
    · simp only [i0, List.size_toArray, List.length_cons, List.length_nil, zero_add, zero_lt_one]
  · rw [Array.extend_of_le]
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]
    omega

/-- Constants represent constants -/
@[approx] lemma approx_const [Approx α E] [ApproxZero α E] (s : α) (s' : E) (a : approx s s') :
    approx (const s) (fun _ : 𝕜 ↦ s') := by
  intro i lt
  constructor
  · exact contDiffAt_const
  · simp only [extend_const, series_coeff_const]
    split_ifs with i0
    all_goals approx

/-- `0` and `1` are infinite order constants -/
instance : Zero (Series α) where zero := const 0
instance [One α] : One (Series α) where one := const 1
lemma zero_def : (0 : Series α) = const 0 := rfl
lemma one_def [One α] : (1 : Series α) = const 1 := rfl

/-- `0` is conservative -/
instance instApproxZero [Approx α E] [ApproxZero α E] : ApproxZero (Series α) (𝕜 → E) where
  approx_zero := by
    simp [zero_def, Pi.zero_def]
    approx

/-- `1` is conservative -/
instance instApproxOne [One α] [Approx α 𝕜] [ApproxZero α 𝕜] [ApproxOne α 𝕜] :
    ApproxOne (Series α) (𝕜 → 𝕜) where
  approx_one := by
    simp [one_def, Pi.one_def]
    approx

@[simp] lemma order_const (s : α) : (const s).order = ⊤ := by simp only [const]
@[simp] lemma size_const (s : α) : (const s).c.size = 1 := by simp [const]
@[simp] lemma order_zero : (0 : Series α).order = ⊤ := by simp only [zero_def, order_const]
@[simp] lemma size_zero : (0 : Series α).c.size = 1 := by simp only [zero_def, size_const]
@[simp] lemma order_one [One α] : (1 : Series α).order = ⊤ := by simp only [one_def, order_const]
@[simp] lemma size_one [One α] : (1 : Series α).c.size = 1 := by simp only [one_def, size_const]

/-!
### Conversion from `ℕ`
-/

/-- Conversion from `ℕ` values to `Series` -/
instance [NatCast α] : NatCast (Series α) := ⟨fun n ↦ const (n : α)⟩

/-- Conversion from `ℕ` literals to `Series` -/
instance {n : ℕ} [n.AtLeastTwo] [NatCast α] : OfNat (Series α) n := ⟨const (n : α)⟩

lemma natCast_def [NatCast α] (n : ℕ) : (n : Series α) = const (n : α) := rfl
lemma ofNat_def [NatCast α] {n : ℕ} [n.AtLeastTwo] [OfNat α n] :
    (OfNat.ofNat n : Series α) = const (n : α) := rfl

instance [NatCast α] [NatCast E] [Approx α E] [ApproxZero α E] [ApproxNatCast α E] :
    ApproxNatCast (Series α) (𝕜 → E) where
  approx_natCast := by
    intro n
    simp only [natCast_def, Pi.natCast_def]
    apply approx_const
    approx

@[approx] lemma approx_fun_ofNat {n : ℕ} [n.AtLeastTwo] [NatCast α] [Approx α 𝕜] [ApproxZero α 𝕜]
    [ApproxNatCast α 𝕜] :
    approx (no_index (OfNat.ofNat n : Series α)) (fun _ : 𝕜 ↦ no_index (OfNat.ofNat n : 𝕜)) := by
  apply approx_const
  simp only [OfNat.ofNat]
  approx

@[approx] lemma approx_ofNat {n : ℕ} [n.AtLeastTwo] [NatCast α] [Approx α 𝕜] [ApproxZero α 𝕜]
    [ApproxNatCast α 𝕜] :
    approx (no_index (OfNat.ofNat n : Series α)) (no_index (OfNat.ofNat n : 𝕜 → 𝕜)) := by
  apply approx_fun_ofNat

@[simp] lemma order_natCast {n : ℕ} [NatCast α] : (n : Series α).order = ⊤ := by
  simp only [natCast_def, order_const]

@[simp] lemma order_ofNat {n : ℕ} [n.AtLeastTwo] [NatCast α] :
    (no_index (OfNat.ofNat n : Series α)).order = ⊤ := by
  simp only [ofNat_def, order_const]

@[simp] lemma size_natCast {n : ℕ} [NatCast α] : (n : Series α).c.size = 1 := by
  simp only [natCast_def, size_const]

@[simp] lemma size_ofNat {n : ℕ} [n.AtLeastTwo] [NatCast α] :
    (no_index (OfNat.ofNat n : Series α)).c.size = 1 := by
  simp only [ofNat_def, size_const]
