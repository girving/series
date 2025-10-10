import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# `OrderedFinpartition` facts

We write out some facts about the degenerate partition of the internal into a single part.
-/

namespace OrderedFinpartition

variable {n : ℕ} {n0 : n ≠ 0}

/-- The `OrderedFinPartition n` corresponding to the highest inner derivative -/
def whole' (n : ℕ) : { p : OrderedFinpartition n // p.length = min n 1 } :=
  match n with
  | 0 => ⟨.atomic 0, by simp only [atomic_length, zero_le, inf_of_le_left]⟩
  | 1 => ⟨.atomic 1, by simp only [atomic_length, min_self]⟩
  | n + 2 =>
    let p := whole' (n + 1)
    ⟨p.val.extendMiddle ⟨0, by omega⟩, by simp only [extendMiddle_length, p.property]; omega⟩

/-- The `OrderedFinPartition n` corresponding to the highest inner derivative -/
def whole (n : ℕ) : OrderedFinpartition n := (whole' n).val

@[simp] lemma length_whole : (whole n).length = min n 1 :=
  (whole' n).property

lemma sum_partSize (n : ℕ) :
    ∑ m : Fin (whole n).length, (whole n).partSize m = n := by
  have h := (whole n).sum_sigma_eq_sum (v := fun _ ↦ 1)
  simpa using h

lemma partSize_of_length_eq_one (p : OrderedFinpartition n) (l1 : p.length = 1) (i : Fin p.length) :
    p.partSize i = n := by
  have h := p.sum_sigma_eq_sum (v := fun _ ↦ 1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    Finset.sum_fin_eq_sum_range, l1, Finset.range_one, Nat.lt_one_iff, Finset.sum_dite_eq',
    Finset.mem_singleton, ↓reduceIte] at h
  convert h
  have lt := i.prop
  simp only [l1] at lt
  omega

@[simp] lemma partSize_whole (i : Fin (whole n).length) : (whole n).partSize i = n := by
  by_cases n0 : n = 0
  · simp only [length_whole, n0, zero_le, inf_of_le_left] at i
    exact i.elim0
  · apply partSize_of_length_eq_one
    simp only [length_whole, inf_eq_right]
    omega

/-- A strictly monotone self-map on `Fin n` is the identity (proof mostly by GPT-5). -/
theorem strictMono_fin_eq_id {f : Fin n → Fin n} (hf : StrictMono f) : f = id := by
  induction' n with n
  · ext x; exact x.elim0
  have hmono := hf.monotone
  have hsurj : f.Surjective := Finite.injective_iff_surjective.mp hf.injective
  -- First, `f 0 = 0` (least maps to least).
  have h0 : f 0 = 0 := by
    obtain ⟨i, hi⟩ := hsurj 0
    have : f 0 ≤ 0 := by simpa [hi] using hmono (Fin.zero_le i)
    exact le_antisymm this (Fin.zero_le _)
  -- Then `f (i.succ) = i.succ` by surjectivity and monotonicity.
  funext i
  refine Fin.induction ?base ?step i
  · simpa using h0
  · intro i hi
    -- pick `j` with `f j = i.succ`
    obtain ⟨j, hj⟩ := hsurj i.succ
    -- show `i < j` (otherwise monotonicity would give `i.succ ≤ i`)
    have hij : i.val < j := by
      by_contra hle
      have : f j ≤ f i.castSucc := hmono (le_of_not_gt hle)
      have : i.succ ≤ i.val := by simp [hj, hi] at this
      exact (lt_irrefl _) (lt_of_le_of_lt this (Nat.lt_succ_of_lt this))
    -- hence `i.succ ≤ j`, so `f i.succ ≤ f j = i.succ`
    have h₁ : f i.succ ≤ i.succ := by
      have : i.succ ≤ j := hij
      simpa [hj] using hmono this
    -- and `i < f i.succ` by strictness, so `i.succ ≤ f i.succ`
    have h₂ : i.succ ≤ f i.succ := by
      have : i.val < f i.succ := by
        have ii : i.val = (id i.castSucc).val := by simp
        rw [ii, ← hi]
        exact hf (by simp only [Fin.castSucc_lt_succ_iff, le_refl])
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, ge_iff_le]
      omega
    exact le_antisymm h₁ h₂

lemma emb_whole (p : OrderedFinpartition n) {i : Fin p.length} (l : p.partSize i = n) :
    p.emb i = fun j ↦ ⟨j.val, by convert j.prop; rw [l]⟩ := by
  have m := p.emb_strictMono i
  generalize p.emb i = f at m
  generalize p.partSize i = m at l f m
  induction l
  exact strictMono_fin_eq_id m

@[simp] lemma eq_whole {n : ℕ} (p : OrderedFinpartition n) {i : Fin p.length}
    (le : n ≤ p.partSize i) : p = whole n := by
  induction' n with n h
  · apply Unique.uniq
  have l : p.length = 1 := by
    contrapose le
    have le0 : 0 < p.length := p.length_pos (by omega)
    have le2 := p.length_le
    letI non := Fin.nontrivial_iff_two_le.mpr (by omega : 2 ≤ p.length)
    obtain ⟨j, ij⟩ := exists_ne i
    have h := p.sum_sigma_eq_sum (v := fun _ ↦ 1)
    rw [Finset.sum_eq_add_sum_diff_singleton (i := i) (Finset.mem_univ _),
      Finset.sum_eq_add_sum_diff_singleton (i := j) (by aesop)] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    have s0 : 0 ≤ ∑ k ∈ (Finset.univ \ {i}) \ {j}, p.partSize k := by bound
    have j0 := p.partSize_pos j
    omega
  ext
  · simp [l]
  · rw [Fin.heq_fun_iff (by simp [l])]
    intro j
    simp only [p.partSize_of_length_eq_one l, partSize_whole]
  · refine Function.hfunext (by simp [l]) fun i j ij ↦ ?_
    have li := p.partSize_of_length_eq_one l i
    have lj := partSize_whole j
    rw [p.emb_whole li, (whole (n + 1)).emb_whole lj]
    rw [Fin.heq_fun_iff (by simp [li])]
    simp
