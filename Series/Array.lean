import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Interval.Approx
import Series.List

/-!
# Array facts
-/

variable {α β γ : Type}

/-- Compose `Array.mapIdx` with `Array.map` -/
lemma Array.mapIdx_map (f : ℕ → β → γ) (g : α → β) (a : Array α) :
    (a.map g).mapIdx f = a.mapIdx (fun k x ↦ f k (g x)) := by
  ext k
  · simp only [Array.size_mapIdx, Array.size_map]
  · simp only [Array.getElem_mapIdx, Array.getElem_map]

@[simp] lemma Subarray.size_take (f : Subarray α) (n : ℕ) : (f.take n).size = min f.size n := by
  simp only [Subarray.size, Subarray.stop, Subarray.take, Subarray.start]
  omega

@[simp] lemma Subarray.size_drop (f : Subarray α) (n : ℕ) : (f.drop n).size = f.size - n := by
  simp only [Subarray.size, Subarray.stop, Subarray.drop, Subarray.start]
  omega

@[simp] lemma Subarray.getElem_take {f : Subarray α} {n k : ℕ} (h : k < (f.take n).size) :
    (f.take n)[k]'h = f[k]'(by simp only [size_take, lt_inf_iff] at h; omega) := by
  simp only [size, stop, take, array, start, instGetElemNatLtSize, get]

@[simp] lemma Subarray.getElem_drop {f : Subarray α} {n k : ℕ} (h : k < (f.drop n).size) :
    (f.drop n)[k]'h = f[n + k]'(Nat.add_lt_of_lt_sub' (size_drop _ _ ▸ h)) := by
  simp only [size, stop, drop, array, start, instGetElemNatLtSize, get] at h ⊢
  exact getElem_congr rfl (by omega) _

@[simp] lemma Array.size_toSubarray' (f : Array α) (a b : ℕ) :
    (f.toSubarray a b).size = (min f.size b) - a := by
  simp only [Subarray.size, Subarray.stop, toSubarray, Subarray.start]
  split_ifs
  all_goals simp; omega

@[simp] lemma Array.size_toSubarray (f : Array α) : f.toSubarray.size = f.size := by
  simp only [Subarray.size, Subarray.stop, toSubarray, Nat.le_refl, ↓reduceDIte, Nat.zero_le,
    Subarray.start, Nat.sub_zero]

@[simp] lemma Array.getElem_toSubarray {f : Array α} {a b n : ℕ} (h : n < (f.toSubarray a b).size) :
    (f.toSubarray a b)[n]'h = f[n + a]'(by simp only [size_toSubarray'] at h; omega) := by
  simp only [size_toSubarray'] at h
  simp only [Subarray.size, Subarray.stop, toSubarray, Subarray.start,
    Subarray.instGetElemNatLtSize, Subarray.get, Subarray.array]
  split_ifs with u0 u1 u2
  all_goals simp [add_comm _ n] at *
  all_goals omega

@[simp] lemma Array.size_nil : (#[] : Array α).size = 0 := rfl

/-!
### Mapped `Subarray`s
-/

def Subarray.map (f : Subarray α) (g : α → β) : Array β :=
  .ofFn fun i ↦ g f[i]

def Subarray.mapIdx (f : Subarray α) (g : ℕ → α → β) : Array β :=
  .ofFn fun i ↦ g i f[i]

@[simp] def Subarray.size_map {f : Subarray α} {g : α → β} : (f.map g).size = f.size := by
  simp only [map, Array.size_ofFn]

@[simp] def Subarray.size_mapIdx {f : Subarray α} {g : ℕ → α → β} : (f.mapIdx g).size = f.size := by
  simp only [mapIdx, Array.size_ofFn]

def Subarray.mapIdx_empty {f : Subarray α} {g : ℕ → α → β} (e : f.size = 0) : f.mapIdx g = #[] := by
  ext n _ h
  · simp only [size_mapIdx, e, Array.size_nil]
  · simp only [List.size_toArray, List.length_nil, not_lt_zero'] at h

@[simp] lemma Subarray.getElem_mapIdx {f : Subarray α} {g : ℕ → α → β} {n : ℕ}
    {h : n < (f.mapIdx g).size} : (f.mapIdx g)[n] = g n (f[n]'(size_mapIdx ▸ h)) := by
  simp only [mapIdx, Fin.getElem_fin, Array.getElem_ofFn]

/-!
### Zero-extension of arrays
-/

section Extend

variable [Zero α]

/-- Zero-extend an `Array` to infinity -/
def Array.extend (f : Array α) (n : ℕ) : α := f.getD n 0

/-- Zero-extend a `Subarray` to infinity -/
def Subarray.extend (f : Subarray α) (n : ℕ) : α := f.getD n 0

lemma Array.extend_def {f : Array α} {n : ℕ} :
    f.extend n = if h : n < f.size then f[n] else 0 := rfl

lemma Subarray.extend_def {f : Subarray α} {n : ℕ} :
    f.extend n = if h : n < f.size then f[n] else 0 := rfl

@[simp] lemma Array.extend_of_lt {f : Array α} {n : ℕ} (h : n < f.size) : f.extend n = f[n] := by
  simp only [extend_def, h, ↓reduceDIte]

@[simp] lemma Array.extend_of_le {f : Array α} {n : ℕ} (h : f.size ≤ n) : f.extend n = 0 := by
  simp only [extend_def, dite_eq_right_iff, isEmpty_Prop, not_lt, h, IsEmpty.forall_iff]

@[simp] lemma Subarray.extend_of_lt {f : Subarray α} {n : ℕ} (h : n < f.size) :
    f.extend n = f[n] := by
  simp only [extend_def, h, ↓reduceDIte]

@[simp] lemma Subarray.extend_of_le {f : Subarray α} {n : ℕ} (h : f.size ≤ n) : f.extend n = 0 := by
  simp only [extend_def, dite_eq_right_iff, isEmpty_Prop, not_lt, h, IsEmpty.forall_iff]

@[simp] lemma Array.extend_empty (n : ℕ) : (#[] : Array α).extend n = 0 := by
  simp only [List.size_toArray, List.length_nil, zero_le, extend_of_le]

/-- Empty subarrays extend to zero -/
lemma Subarray.extend_empty {f : Subarray α} (e : f.size = 0) (n : ℕ) : f.extend n = 0 := by
  simp only [extend_def, e, not_lt_zero', ↓reduceDIte]

@[simp] lemma Array.extend_ofFn {n : ℕ} (f : Fin n → α) (k : ℕ) :
    (Array.ofFn f).extend k = if h : k < n then f ⟨k,h⟩ else 0 := by
  split_ifs with h
  ·  try simp at h; simp [h]
  all_goals try simp at h; simp [h]

lemma Array.eq_extend {f : Array α} {n : ℕ} {h : n < f.size} :
    f[n]'h = f.extend n := by simp only [extend_of_lt h]

lemma Subarray.eq_extend {f : Subarray α} {n : ℕ} {h : n < f.size} :
    f[n]'h = f.extend n := by simp only [extend_of_lt h]

@[simp] lemma Subarray.extend_take {f : Subarray α} {n k : ℕ} :
    (f.take k).extend n = if n < k then f.extend n else 0 := by
  simp only [extend, getD, size, stop, take, array, start, instGetElemNatLtSize, get]
  split_ifs with h
  all_goals try rfl
  all_goals omega

@[simp] lemma Subarray.extend_drop {f : Subarray α} {n k : ℕ} :
    (f.drop k).extend n = if n < f.size - k then f.extend (n + k) else 0 := by
  simp only [extend_def, size_drop, getElem_drop, add_comm n]
  split_ifs
  all_goals try rfl
  omega

@[simp] lemma Array.extend_toSubarray {f : Array α} {a b n : ℕ} :
    (f.toSubarray a b).extend n = if n < b - a then f.extend (n + a) else 0 := by
  simp only [Subarray.extend_def, size_toSubarray', getElem_toSubarray, extend_def]
  split_ifs with h0
  all_goals try rfl
  all_goals try omega

@[simp] lemma Array.extend_cons {x : α} {f : List α} {n : ℕ} :
    Array.extend ⟨x :: f⟩ (n + 1) = Array.extend ⟨f⟩ n := by
  simp only [extend_def, List.size_toArray, List.length_cons, add_lt_add_iff_right,
    List.getElem_toArray, List.getElem_cons_succ]

end Extend

/-!
### Sums

We avoid slice machinery, as I am afraid of it. I'm going to mark this as noncomputable since
we want a faster version for computations.
-/

section Sum

variable [AddCommMonoid α]

noncomputable def Subarray.sum (f : Subarray α) : α :=
  (Finset.range f.size).sum f.extend

lemma Array.sum_eq_range_sum {f : Array α} : f.sum = ∑ i ∈ Finset.range f.size, f.extend i := by
  simp only [sum]
  induction' f with g
  simp only [List.size_toArray, List.foldr_toArray']
  induction' g with x g h
  · simp
  · simp [Finset.sum_range_succ', add_comm _ x, h]

lemma Array.sum_one {f : Array α} (h : f.size = 1) : f.sum = f[0] := by
  simp only [sum_eq_range_sum, h, Finset.range_one, Finset.sum_singleton, zero_lt_one, extend_of_lt]

lemma Array.sum_two {f : Array α} (h : f.size = 2) : f.sum = f[0] + f[1] := by
  simp only [sum_eq_range_sum, h, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    zero_lt_two, extend_of_lt, Nat.lt_add_one]

end Sum

/-!
### Approx instances for arrays
-/

section Approx

variable [Approx α β]

instance : Approx (Array α) (Array β) where
  approx f f' := ∃ (h : f.size = f'.size), ∀ n (h : n < f.size), approx f[n] f'[n]

instance : Approx (Subarray α) (Subarray β) where
  approx f f' := ∃ (h : f.size = f'.size), ∀ n (h : n < f.size), approx f[n] f'[n]

instance : Approx (List α) (List β) where
  approx f f' := List.Forall₂ approx f f'

lemma Array.approx_def {f : Array α} {f' : Array β} :
    approx f f' ↔ ∃ (h : f.size = f'.size), ∀ n (h : n < f.size), approx f[n] f'[n] := by
  simp only [approx]

lemma Subarray.approx_def {f : Subarray α} {f' : Subarray β} :
    approx f f' ↔ ∃ (h : f.size = f'.size), ∀ n (h : n < f.size), approx f[n] f'[n] := by
  simp only [approx]

@[approx] lemma Array.approx_getElem {f : Array α} {f' : Array β} {n : ℕ} {h : n < f.size}
    {h' : n < f'.size} (a : approx f f') : approx f[n] f'[n] := a.2 n h

@[approx] lemma Subarray.approx_getElem {f : Subarray α} {f' : Subarray β} {n : ℕ} {h : n < f.size}
    {h' : n < f'.size} (a : approx f f') : approx f[n] f'[n] := a.2 n h

@[approx] lemma Array.approx_extend [Zero α] [Zero β] [ApproxZero α β] {f : Array α} {f' : Array β}
    {n : ℕ} (a : approx f f') : approx (f.extend n) (f'.extend n) := by
  simp only [extend_def]
  by_cases h : n < f.size
  all_goals simp only [h, ↓reduceDIte, a.1 ▸ h]; approx

@[approx] lemma Subarray.approx_extend [Zero α] [Zero β] [ApproxZero α β] {f : Subarray α}
    {f' : Subarray β} {n : ℕ} (a : approx f f') : approx (f.extend n) (f'.extend n) := by
  simp only [extend_def]
  by_cases h : n < f.size
  all_goals simp only [h, ↓reduceDIte, a.1 ▸ h]; approx

@[approx] lemma List.approx_toArray {f : List α} {f' : List β} (a : approx f f') :
    approx (f.toArray) (f'.toArray) := by
  simp only [approx]
  have e : f.toArray.size = f'.toArray.size := by
    simp only [approx] at a
    exact a.length_eq
  refine ⟨e, ?_⟩
  simp only [size_toArray, getElem_toArray]
  approx

@[approx] lemma Array.approx_take {f : Array α} {f' : Array β} {n : ℕ} (a : approx f f') :
    approx (f.take n) (f'.take n) := by
  refine ⟨?_, ?_⟩
  · simp only [take_eq_extract, size_extract, a.1, tsub_zero]
  · intro i lt
    simp only [take_eq_extract, getElem_extract, zero_add]
    approx

@[approx] lemma Subarray.approx_take {f : Subarray α} {f' : Subarray β} {n : ℕ} (a : approx f f') :
    approx (f.take n) (f'.take n) := by
  refine ⟨?_, ?_⟩
  · simp only [size_take, a.1]
  · intro i lt
    simp only [getElem_take]
    approx

@[approx] lemma Subarray.approx_drop {f : Subarray α} {f' : Subarray β} {n : ℕ} (a : approx f f') :
    approx (f.drop n) (f'.drop n) := by
  refine ⟨?_, ?_⟩
  · simp only [size_drop, a.1]
  · intro i lt
    simp only [getElem_drop]
    approx

@[approx] lemma Array.approx_toSubarray {f : Array α} {f' : Array β} {a b : ℕ} (fa : approx f f') :
    approx (f.toSubarray a b) (f'.toSubarray a b) := by
  refine ⟨?_, ?_⟩
  · simp only [size_toSubarray', fa.1]
  · intro i lt
    simp only [getElem_toSubarray]
    approx

end Approx
