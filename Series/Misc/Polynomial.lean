import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Div
import Mathlib.GroupTheory.GroupAction.Ring
import Series.Misc.Array

/-!
# Polynomial facts
-/

variable {α β γ : Type}

open Polynomial (X)
open scoped Polynomial

attribute [bound] Polynomial.degree_mul_le Polynomial.natDegree_mul_le
attribute [grind =] Polynomial.C_add Polynomial.C_neg Polynomial.C_sub Polynomial.C_mul
  Polynomial.coeff_C Polynomial.coeff_zero Polynomial.coeff_mul_X_pow' Polynomial.coeff_add

/-!
### Semiring facts
-/

section Semiring

variable {S : Type} [Semiring S]
variable {f g : Subarray S} {x : S}

-- The polynomial corresponding to an `Array`, `Subarray`, or `Series`
noncomputable def Array.poly (f : Array S) : S[X] := (f.mapIdx fun k a ↦ a • X ^ k).sum
noncomputable def Subarray.poly (f : Subarray S) : S[X] := (f.mapIdx fun k a ↦ a • X ^ k).sum

@[simp] lemma Array.poly_empty : (#[] : Array S).poly = 0 := by simp [poly]

@[simp] lemma Subarray.poly_empty (e : f.size = 0) : f.poly = 0 := by
  rw [poly, Subarray.mapIdx_empty e, Array.sum_empty]

@[simp] lemma Subarray.poly_one (e : f.size = 1) : f.poly = f[0] • 1 := by
  rw [poly, Array.sum_one (by simpa)]
  simp

@[simp] lemma Subarray.poly_two (e : f.size = 2) : f.poly = f[0] • (1 : S[X]) + f[1] • X := by
  rw [poly, Array.sum_two (by simpa)]
  simp

@[simp] lemma Subarray.mul_poly :
    (Array.ofFn fun i : Fin f.size ↦ x * f[(i : ℕ)]).poly = x • f.poly := by
  simp only [Array.poly, Array.sum_eq_range_sum, Array.size_mapIdx, Array.size_ofFn, poly,
    size_mapIdx, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i lt ↦ ?_
  simp only [Array.extend_def, Array.size_mapIdx, Array.size_ofFn, Array.getElem_mapIdx,
    Array.getElem_ofFn, size_mapIdx, getElem_mapIdx, smul_dite, smul_smul, smul_zero]

def Polynomial.coeffLM (n : ℕ) : S[X] →ₗ[S] S where
  toFun f := f.coeff n
  map_add' f g := by simp only [coeff_add]
  map_smul' s f := by simp only [coeff_smul, smul_eq_mul, RingHom.id_apply]

@[simp] lemma Polynomial.coeffLM_apply {f : S[X]} {n : ℕ} :
    (Polynomial.coeffLM n) f = f.coeff n := rfl

lemma Array.extend_eq_coeff_poly {f : Array S} {n : ℕ} : f.extend n = f.poly.coeff n := by
  simp only [extend_def, poly, sum_eq_range_sum, size_mapIdx, getElem_mapIdx,
    ← Polynomial.coeffLM_apply, map_sum]
  simp only [Polynomial.coeffLM_apply, apply_dite (f := fun f : S[X] ↦ f.coeff n),
    Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Polynomial.coeff_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single n]
    · simp [h]
    · intro i m0 m1
      simp only [Ne.symm m1, ↓reduceIte, dite_eq_ite, ite_self]
    · simp [h]
  · rw [Finset.sum_eq_zero]
    intro i m
    simp only [Finset.mem_range] at m
    simp only [m, ↓reduceDIte, ite_eq_right_iff]
    omega

lemma Subarray.extend_eq_coeff_poly {f : Subarray S} {n : ℕ} : f.extend n = f.poly.coeff n := by
  simp only [extend_def, poly, Array.sum_eq_range_sum, size_mapIdx, Array.extend_def,
    getElem_mapIdx, ← Polynomial.coeffLM_apply, map_sum]
  simp only [Polynomial.coeffLM_apply, apply_dite (f := fun f : S[X] ↦ f.coeff n),
    Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Polynomial.coeff_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single n]
    · simp [h]
    · intro i m0 m1
      simp only [Ne.symm m1, ↓reduceIte, dite_eq_ite, ite_self]
    · simp [h]
  · rw [Finset.sum_eq_zero]
    intro i m
    simp only [Finset.mem_range] at m
    simp only [m, ↓reduceDIte, ite_eq_right_iff]
    omega

@[simp] lemma Subarray.split_poly (f : Subarray S) (n : ℕ) :
    (f.take n).poly + (f.drop n).poly * X ^ n = f.poly := by
  ext i
  simp only [Polynomial.coeff_add, ← extend_eq_coeff_poly, extend_take, Polynomial.coeff_mul_X_pow',
    extend_drop]
  split_ifs
  · omega
  · omega
  · simp only [add_zero]
  · rw [zero_add, Nat.sub_add_cancel (by omega)]
  · rw [add_zero, Subarray.extend_of_le (by omega)]
  · omega

lemma Array.poly_toSubarray {f : Array S} {a : ℕ} (h : a = f.size) :
    (f.toSubarray 0 a).poly = f.poly := by
  simp only [Subarray.poly, h, sum_eq_range_sum, Subarray.size_mapIdx, size_toSubarray', min_self,
    tsub_zero, poly, size_mapIdx]
  refine Finset.sum_congr rfl fun i lt ↦ ?_
  simp [extend_def]

@[bound] lemma Subarray.degree_poly_lt (f : Subarray S) : f.poly.degree < f.size := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i le
  simp only [← extend_eq_coeff_poly, extend_def, not_lt.mpr le, ↓reduceDIte]

@[bound] lemma Subarray.degree_poly_le (f : Subarray S) : f.poly.degree ≤ (f.size - 1 : ℕ) := by
  have h := f.degree_poly_lt
  generalize f.poly.degree = n at h
  induction' n with n
  · simp only [bot_le]
  · simp only [← WithBot.coe_natCast (α := ℕ), WithBot.coe_le_coe, WithBot.coe_lt_coe] at h ⊢
    simp only [Nat.cast_id, Nat.cast_tsub, Nat.cast_one, ge_iff_le] at h ⊢
    omega

@[bound] lemma Subarray.natDegree_poly_le (f : Subarray S) : f.poly.natDegree ≤ f.size - 1 := by
  by_cases z : f.poly = 0
  · simp only [z, Polynomial.natDegree_zero, zero_le]
  have h := f.degree_poly_lt
  rw [← Polynomial.natDegree_lt_iff_degree_lt z] at h
  omega

lemma Polynomial.C_eq_smul_one (s : S) : C s = s • 1 := by
  ext i
  simp only [coeff_C, coeff_smul, coeff_one, smul_eq_mul, mul_ite, mul_one, mul_zero]

@[grind =] lemma Polynomial.smul_eq_C_smul {R : Type} [Semiring R] [Module S R]
    [IsScalarTower S R R] (s : S) (x : R[X]) : s • x = C (s • (1 : R)) * x := by
  simp only [ext_iff, coeff_smul, coeff_mul, coeff_C, ite_mul, zero_mul, smul_one_mul]
  intro n
  rw [Finset.sum_eq_single (a := (0,n)) _ (by simp)]
  · simp
  · aesop

end Semiring

/-!
### `CommRing` facts
-/

section CommRing

variable {R : Type} [CommRing R]
variable {f g : Subarray R} {x : R}

@[simp] lemma Subarray.poly_mul :
    (Array.ofFn fun i : Fin f.size ↦ f[(i : ℕ)] * x).poly = x • f.poly := by
  simp only [mul_comm _ x, f.mul_poly]

instance : SMulCommClass R R[X] R[X] where
  smul_comm s x y := by
    ext n
    simp only [smul_eq_mul, Polynomial.coeff_smul, Polynomial.coeff_mul, Finset.mul_sum,
      ← mul_assoc, mul_comm _ s]

variable [Nontrivial R]

lemma Polynomial.monomial_divByMnnic_X_pow (s : R) (a b : ℕ) :
    (s • X ^ a /ₘ X ^ b) = if b ≤ a then (s • X ^ (a - b) : R[X]) else 0 := by
  split_ifs with le
  · refine (Polynomial.div_modByMonic_unique _ 0 (monic_X_pow _) ⟨?_, ?_⟩).1
    · simp only [mul_smul_comm, ← pow_add, Nat.add_sub_cancel' le, zero_add]
    · simp only [degree_zero, degree_X_pow]
      apply WithBot.bot_lt_coe
  · refine (Polynomial.div_modByMonic_unique 0 (s • X ^ a) (monic_X_pow _) ⟨?_, ?_⟩).1
    · ring
    · refine lt_of_le_of_lt (Polynomial.degree_smul_le _ _) ?_
      simp only [degree_X_pow, Nat.cast_lt, not_le.mp le]

lemma Polynomial.monomial_modByMnnic_X_pow (s : R) (a b : ℕ) :
    (s • X ^ a %ₘ X ^ b) = if a < b then (s • X ^ a : R[X]) else 0 := by
  rw [Polynomial.modByMonic_eq_sub_mul_div, Polynomial.monomial_divByMnnic_X_pow]
  split_ifs with le
  · omega
  · simp only [mul_smul_comm, ← pow_add, Nat.add_sub_cancel' le, sub_self]
  · ring
  · omega
  · apply monic_X_pow

lemma Polynomial.const_modByMnnic_X_pow (s : R) (b : ℕ) :
    (C s %ₘ X ^ b) = if 0 < b then (C s : R[X]) else 0 := by
  have e : C s = s • X ^ 0 := by simp [C_eq_smul_one]
  rw [e, Polynomial.monomial_modByMnnic_X_pow]

@[simp] lemma Polynomial.coeff_modByMnnic_X_pow (f : R[X]) (n i : ℕ) :
    (f %ₘ X ^ n).coeff i = if i < n then f.coeff i else 0 := by
  induction' f using Polynomial.induction_on with a p q pc qc a p ac
  · simp only [const_modByMnnic_X_pow, apply_ite, coeff_C]
    split_ifs
    all_goals simp [coeff_C, coeff_zero]; try omega
  · simp only [add_modByMonic, coeff_add, pc, qc]
    aesop
  · simp [C_eq_smul_one, Polynomial.monomial_modByMnnic_X_pow]
    split_ifs
    all_goals simp; try omega


@[simp] lemma Array.poly_take (f : Array R) (n : ℕ) : (f.take n).poly = f.poly %ₘ X ^ n := by
  ext i
  simp only [take_eq_extract, ← extend_eq_coeff_poly, extend_def, size_extract, tsub_zero,
    lt_inf_iff, getElem_extract, zero_add, Polynomial.coeff_modByMnnic_X_pow]
  aesop

lemma Array.poly_toSubarray' (f : Array R) (a : ℕ) : (f.toSubarray 0 a).poly = f.poly %ₘ X ^ a := by
  ext i
  simp only [← Subarray.extend_eq_coeff_poly, extend_toSubarray, tsub_zero, add_zero,
    Polynomial.coeff_modByMnnic_X_pow, ← extend_eq_coeff_poly]

end CommRing

/-!
### Truncation to `ℕ∞` orders
-/

section Truncate

variable {S : Type} [Semiring S]
variable {f g : Subarray S} {x : S}

/-- Truncate a polynomial to order `n : ℕ∞`. For finite orders, this corresponds to `%ₘ X ^ n`. -/
def Polynomial.trunc (f : S[X]) (n : ℕ∞) : S[X] :=
  ⟨f.toFinsupp.filter fun k ↦ k < n⟩

lemma Polynomial.coeff_trunc (f : S[X]) (n : ℕ∞) (i : ℕ) :
    (f.trunc n).coeff i = if i < n then f.coeff i else 0 := by
  simp only [coeff, trunc, Finsupp.filter_apply]

@[simp] lemma Polynomial.trunc_zero (f : S[X]) : f.trunc 0 = 0 := by
  ext i
  simp only [coeff_trunc, ENat.not_lt_zero, ↓reduceIte, coeff_zero]

@[simp] lemma Polynomial.zero_trunc (n : ℕ∞) : (0 : S[X]).trunc n = 0 := by
  ext i
  simp only [coeff_trunc, coeff_zero, ite_self]

@[simp] lemma Array.poly_takeLt (f : Array S) (n : ℕ∞) : (f.takeLt n).poly = f.poly.trunc n := by
  ext i
  simp only [takeLt, ← Subarray.extend_eq_coeff_poly, extend_toSubarray, tsub_zero,
    ENat.lt_min_coe_iff, add_zero, Polynomial.coeff_trunc, ← extend_eq_coeff_poly]
  split_ifs with h0 h1
  all_goals simp_all
