import Series.Misc.Polynomial
import Series.Misc.Bound
import Series.Misc.Nat
import Series.Tactic.QSimp

/-!
# Dyadic trees to fit Karatsuba multiplication
-/

open Polynomial (C X)
open scoped Polynomial
namespace Series

variable {α β 𝕜 : Type} {n m : ℕ}

/-!
### Definitions
-/

/-- A dyadic tree, with size at most `2 ^ n` -/
inductive Tree (α : Type) : ℕ → Type where
  | zero : {n : ℕ} → Tree α n
  | leaf : α → Tree α 0
  | left : {n : ℕ} → Tree α n → Tree α (n + 1)
  | both : {n : ℕ} → Tree α n → Tree α n → Tree α (n + 1)

namespace Tree

/-!
### Size (number of possibly nonzero terms)
-/

/-- Number of possibly nonzero terms -/
def size {n : ℕ} (x : Tree α n) : ℕ := match n, x with
  | _, zero => 0
  | 0, leaf _ => 1
  | _ + 1, left x => x.size
  | n + 1, both _ y => 2 ^ n + y.size

@[simp, grind =] lemma size_zero : (zero : Tree α n).size = 0 := by simp only [size]
@[simp, grind =] lemma size_leaf (x : α) : (leaf x).size = 1 := rfl
@[simp, grind =] lemma size_left (x : Tree α n) : (left x).size = x.size := rfl
@[simp, grind =] lemma size_both (x y : Tree α n) : (both x y).size = 2 ^ n + y.size := rfl

/-- Trees have size at most `2 ^ n` -/
@[grind! .] lemma size_le_pow {n : ℕ} (x : Tree α n) : x.size ≤ 2 ^ n := by
  fun_induction size with grind

/-- Smallest `n` that fits a given size -/
def min_n (s : ℕ) : ℕ := Nat.log2 (2 * s - 1)

/-- `n = min_s` has enough room for size `s` -/
@[simp] lemma le_min_n (s : ℕ) : s ≤ 2 ^ min_n s := by
  simp only [min_n]
  have := Nat.lt_log2_self (n := 2 * s - 1)
  grind

/-- `n = min_s` is the smallest `n` that fits size `s` -/
lemma min_n_lt {n s : ℕ} (ns : n < min_n s) : 2 ^ n < s := by
  simp only [min_n, ← Nat.add_one_le_iff] at ns
  by_cases s0 : s = 0
  · simp [s0] at ns
  · rw [Nat.le_log2 (by omega)] at ns
    omega

/-- `min_n` is monotone -/
@[bound] lemma min_n_mono (s t : ℕ) (st : s ≤ t) : min_n s ≤ min_n t := by
  simp only [min_n]
  bound

/-- Size doesn't care about casts -/
@[simp] lemma size_cast [Zero α] (e : n = m) (x : Tree α n) : (e ▸ x).size = x.size := by
  subst e; rfl

/-- Size doesn't care about casts -/
@[simp] lemma size_cast_fun [Zero α] {f : ℕ → ℕ} (e : n = m) (x : Tree α (f n)) :
    (e ▸ x).size = x.size := by
  subst e; rfl

/-!
### Polynomial expansions
-/

noncomputable def poly [Semiring α] {n : ℕ} (x : Tree α n) : α[X] := match n, x with
  | _, zero => 0
  | 0, leaf x => C x
  | _ + 1, left x => x.poly
  | n + 1, both x y => x.poly + y.poly * X ^ (2 ^ n)

@[simp, grind =] lemma poly_zero [Semiring α] : (zero : Tree α n).poly = 0 := by simp only [poly]
@[simp, grind =] lemma poly_leaf [Semiring α] (x : α) : (leaf x).poly = C x := rfl
@[simp, grind =] lemma poly_left [Semiring α] (x : Tree α n) : (left x).poly = x.poly := rfl
@[simp, grind =] lemma poly_both [Semiring α] {n : ℕ} (x y : Tree α n) :
    (both x y).poly = x.poly + y.poly * X ^ (2 ^ n) := rfl

@[simp, grind =] lemma poly_cast [Semiring α] (e : n = m) (x : Tree α n) :
    (e ▸ x).poly = x.poly := by
  subst e; rfl

@[simp, grind =] lemma poly_cast_fun [Semiring α] {f : ℕ → ℕ} (e : n = m) (x : Tree α (f n)) :
    (e ▸ x).poly = x.poly := by
  subst e; rfl

/-!
### Addition
-/

def adds [Add α] {n : ℕ} (x y : Tree α n) : Tree α n := match x, y with
  | zero, x => x
  | y, zero => y
  | leaf x, leaf y => leaf (x + y)
  | left x, left y => left (adds x y)
  | left x, both y z => both (adds x y) z
  | both x y, left z => both (adds x z) y
  | both x y, both z w => both (adds x z) (adds y w)

def add_le [Add α] {m : ℕ} (x : Tree α n) (y : Tree α (n + m)) : Tree α (n + m) :=
  match m, y with
  | 0, y => x.adds y
  | m + 1, zero => left (add_le x zero)
  | m + 1, left y => left (add_le x y)
  | m + 1, both y z => both (add_le x y) z

def add [Add α] (x : Tree α n) (y : Tree α m) : Tree α (max n m) :=
  if le : n ≤ m then way x y le else max_comm n m ▸ way y x (not_le.mp le).le where
  way {n m : ℕ} (x : Tree α n) (y : Tree α m) (le : n ≤ m) : Tree α (max n m) :=
    let s := Nat.add_sub_cancel' le
    let e := s.trans (max_eq_right le).symm
    e ▸ add_le x (s.symm.ndrec y)

@[simp, grind =] lemma poly_adds [CommRing α] {n : ℕ} (x y : Tree α n) :
    (x.adds y).poly = x.poly + y.poly := by
  fun_induction adds with grind

@[simp, grind =] lemma poly_add_le [CommRing α] {m : ℕ} (x : Tree α n) (y : Tree α (n + m)) :
    (x.add_le y).poly = x.poly + y.poly := by
  fun_induction add_le <;> qsimp [add_le] <;> grind

@[simp, grind =] lemma poly_add [CommRing α] (x : Tree α n) (y : Tree α m) :
    (x.add y).poly = x.poly + y.poly := by
  simp only [add, add.way]
  grind

@[simp, grind =] lemma size_adds [Add α] (x y : Tree α n) :
    (x.adds y).size = max x.size y.size := by
  fun_induction adds with grind

@[simp, grind =] lemma size_add_le [Add α] {m : ℕ} (x : Tree α n) (y : Tree α (n + m)) :
    (x.add_le y).size = max x.size y.size := by
  fun_induction add_le <;> qsimp [add_le] <;> grind

@[simp, grind =] lemma size_add [Add α] (x : Tree α n) (y : Tree α m) :
    (x.add y).size = max x.size y.size := by
  simp only [add, add.way]
  grind

/-!
### Negation
-/

def neg [Neg α] {n : ℕ} (x : Tree α n) : Tree α n := match x with
  | zero => zero
  | leaf x => leaf (-x)
  | left x => left (neg x)
  | both x y => both (neg x) (neg y)

@[simp, grind =] lemma poly_neg [CommRing α] (x : Tree α n) : x.neg.poly = -x.poly := by
  fun_induction neg with grind

@[simp, grind =] lemma size_neg [Neg α] {n : ℕ} (x : Tree α n) : x.neg.size = x.size := by
  fun_induction neg with grind

/-!
### Subtraction
-/

def subs [Sub α] [Neg α] {n : ℕ} (x y : Tree α n) : Tree α n := match x, y with
  | x, zero => x
  | zero, y => y.neg
  | leaf x, leaf y => leaf (x - y)
  | left x, left y => left (subs x y)
  | left x, both y z => both (subs x y) (neg z)
  | both x y, left z => both (subs x z) y
  | both x y, both z w => both (subs x z) (subs y w)

def sub_le [Sub α] [Neg α] {m : ℕ} (x : Tree α n) (y : Tree α (n + m)) : Tree α (n + m) :=
  match m, y with
  | 0, y => x.subs y
  | m + 1, zero => left (sub_le x zero)
  | m + 1, left y => left (sub_le x y)
  | m + 1, both y z => both (sub_le x y) (neg z)

def sub_ge [Sub α] [Neg α] {k : ℕ} (x : Tree α (m + k)) (y : Tree α m) : Tree α (m + k) :=
  match k, x with
  | 0, x => x.subs y
  | k + 1, zero => left (sub_ge zero y)
  | k + 1, left x => left (sub_ge x y)
  | k + 1, both x z => both (sub_ge x y) z

def sub [Sub α] [Neg α] (x : Tree α n) (y : Tree α m) : Tree α (max n m) :=
  if le : n ≤ m then
    let s := Nat.add_sub_cancel' le
    let e := s.trans (max_eq_right le).symm
    e ▸ sub_le x (s.symm.ndrec y)
  else
    let ge := (not_le.mp le).le
    let s := Nat.add_sub_cancel' ge
    let e := s.trans (max_eq_left ge).symm
    e ▸ sub_ge (s.symm.ndrec x) y

@[simp, grind =] lemma poly_subs [CommRing α] {n : ℕ} (x y : Tree α n) :
    (x.subs y).poly = x.poly - y.poly := by
  fun_induction subs with grind

@[simp, grind =] lemma poly_sub_le [CommRing α] {m : ℕ} (x : Tree α n) (y : Tree α (n + m)) :
    (x.sub_le y).poly = x.poly - y.poly := by
  fun_induction sub_le <;> qsimp [sub_le] <;> grind

@[simp, grind =] lemma poly_sub_ge [CommRing α] {k : ℕ} (x : Tree α (m + k)) (y : Tree α m) :
    (x.sub_ge y).poly = x.poly - y.poly := by
  fun_induction sub_ge <;> qsimp [sub_ge] <;> grind

@[simp] lemma poly_sub [CommRing α] (x : Tree α n) (y : Tree α m) :
    (x.sub y).poly = x.poly - y.poly := by
  unfold sub
  grind

/-!
### Scalar multiplication
-/

def smul [SMul α β] (s : α) {n : ℕ} (x : Tree β n) : Tree β n := match x with
  | zero => zero
  | leaf x => leaf (s • x)
  | left x => left (smul s x)
  | both x y => both (smul s x) (smul s y)

@[simp] lemma poly_smul [Semiring α] [CommRing β] [Module α β] [IsScalarTower α β β]
    (s : α) (x : Tree β n) : (smul s x).poly = s • x.poly := by
  fun_induction smul <;> qsimp [smul] <;> grind

/-!
### Karatsuba multiplication
-/

/-- Add two trees where the second is shifted: p0 + p1*X^(2^n) -/
def add_shift [Add α] (p0 p1 : Tree α (n + 1)) : Tree α (n + 2) :=
  match p0, p1 with
  | p0, zero => left p0
  | zero, left p1 => left (both zero p1)
  | zero, both p10 p11 => both (both zero p10) (left p11)
  | left p0, left p1 => left (both p0 p1)
  | left p0, both p10 p11 => both (both p0 p10) (left p11)
  | both p00 p01, left p1 => left (both p00 (p01.adds p1))
  | both p00 p01, both p10 p11 => both (both p00 (p01.adds p10)) (left p11)

/-- Combine three products for Karatsuba: p0 + p1*X^(2^n) + p2*X^(2^(n+1)) -/
def add_karatsuba [Add α] (p0 p1 p2 : Tree α (n + 1)) : Tree α (n + 2) :=
  match p0, p1, p2 with
  | p0, p1, zero => add_shift p0 p1
  | p0, zero, p2 => both p0 p2
  | zero, left p1, left p2 => both (both zero p1) (left p2)
  | zero, left p1, both p20 p21 => both (both zero p1) (both p20 p21)
  | zero, both p10 p11, left p2 => both (both zero p10) (left (p11.adds p2))
  | zero, both p10 p11, both p20 p21 => both (both zero p10) (both (p11.adds p20) p21)
  | left p0, left p1, left p2 => both (both p0 p1) (left p2)
  | left p0, left p1, both p20 p21 => both (both p0 p1) (both p20 p21)
  | left p0, both p10 p11, left p2 => both (both p0 p10) (left (p11.adds p2))
  | left p0, both p10 p11, both p20 p21 => both (both p0 p10) (both (p11.adds p20) p21)
  | both p00 p01, left p1, left p2 => both (both p00 (p01.adds p1)) (left p2)
  | both p00 p01, left p1, both p20 p21 => both (both p00 (p01.adds p1)) (both p20 p21)
  | both p00 p01, both p10 p11, left p2 => both (both p00 (p01.adds p10)) (left (p11.adds p2))
  | both p00 p01, both p10 p11, both p20 p21 =>
      both (both p00 (p01.adds p10)) (both (p11.adds p20) p21)

/-- Multiply two trees of the same depth using Karatsuba algorithm -/
def muls [Zero α] [Add α] [Sub α] [Neg α] [Mul α] {n : ℕ} (x y : Tree α n) : Tree α (n + 1) :=
  match x, y with
  | zero, _ => zero
  | _, zero => zero
  | leaf x, leaf y => left (leaf (x * y))
  | left x, left y => left (muls x y)
  | left x, both y z => add_shift (muls x y) (muls x z)
  | both x y, left z => add_shift (muls x z) (muls y z)
  | both x0 x1, both y0 y1 =>
      let p0 := muls x0 y0
      let p2 := muls x1 y1
      let pm := muls (x0.adds x1) (y0.adds y1)
      -- Karatsuba: p1 = pm - (p0 + p2) = x0*y1 + x1*y0
      let p1 := pm.subs (p0.adds p2)
      add_karatsuba p0 p1 p2

/-- Multiply two trees of potentially different depths -/
def mul_le [Zero α] [Add α] [Sub α] [Neg α] [Mul α] {m : ℕ} (x : Tree α n) (y : Tree α (n + m)) :
    Tree α (n + m + 1) :=
  match m, y with
  | _, zero => zero
  | 0, y => x.muls y
  | m + 1, left y => left (mul_le x y)
  | m + 1, both y z => add_shift (mul_le x y) (mul_le x z)

lemma mul_nm (le : n ≤ m) : n + (m - n) + 1 = max n m + 1 := by omega

/-- Karatsuba multiplication of two trees -/
def mul [Zero α] [Add α] [Sub α] [Neg α] [Mul α] (x : Tree α n) (y : Tree α m) :
    Tree α (max n m + 1) :=
  if le : n ≤ m then way x y le else max_comm n m ▸ way y x (not_le.mp le).le where
  way {n m : ℕ} (x : Tree α n) (y : Tree α m) (le : n ≤ m) : Tree α (max n m + 1) :=
    mul_nm le ▸ x.mul_le ((Nat.add_sub_cancel' le).symm ▸ y)

/-- Clean up slightly larger powers of `X` -/
@[grind =] lemma X_pow_two_mul [Semiring α] :
    (X : α[X]) ^ (2 * 2 ^ n) = (X ^ 2 ^ n) ^ 2 := by simp [pow_mul']

@[simp, grind =] lemma poly_add_shift [CommRing α] (p0 p1 : Tree α (n + 1)) :
    (add_shift p0 p1).poly = p0.poly + p1.poly * X ^ (2 ^ n) := by
  cases p0 <;> cases p1 <;> simp [add_shift] <;> grind

@[simp, grind =] lemma poly_add_karatsuba [CommRing α] (p0 p1 p2 : Tree α (n + 1)) :
    (add_karatsuba p0 p1 p2).poly =
      p0.poly + p1.poly * X ^ (2 ^ n) + p2.poly * X ^ (2 ^ (n + 1)) := by
  cases p0 <;> cases p1 <;> cases p2 <;> simp [add_karatsuba] <;> grind

@[simp, grind =] lemma poly_muls [CommRing α] (x y : Tree α n) : (x.muls y).poly = x.poly * y.poly := by
  fun_induction muls <;> qsimp [muls] <;> grind

@[simp, grind =] lemma poly_mul_le [CommRing α] {m : ℕ} (x : Tree α n) (y : Tree α (n + m)) :
    (x.mul_le y).poly = x.poly * y.poly := by
  fun_induction mul_le <;> qsimp [mul_le] <;> grind

@[simp, grind =] lemma poly_mul [CommRing α] (x : Tree α n) (y : Tree α m) :
    (x.mul y).poly = x.poly * y.poly := by
  simp only [mul, mul.way]
  grind

/-!
### `O(log n)`-time coefficient access

Do not use in performance-critical code!
-/

-- DO NOT SUBMIT: Rename to extend right before submit. It's extend_slow to prevent accidental use.
/-- `O(log n)`-time coefficient access. Do not use in performance-critical code! -/
def extend_slow [Zero α] {n : ℕ} (x : Tree α n) (i : ℕ) : α := match n, x with
  | _, zero => 0
  | 0, leaf x => if i = 0 then x else 0
  | _ + 1, left x => x.extend_slow i
  | n + 1, both x y => if i < 2 ^ n then x.extend_slow i else y.extend_slow (i - 2 ^ n)

@[simp, grind =] lemma extend_zero [Zero α] (i : ℕ) : (zero : Tree α n).extend_slow i = 0 := by
  simp only [extend_slow]
@[simp, grind =] lemma extend_leaf [Zero α] (x : α) (i : ℕ) :
    (leaf x).extend_slow i = if i = 0 then x else 0 := rfl
@[simp, grind =] lemma extend_left [Zero α] (x : Tree α n) (i : ℕ) :
    (left x).extend_slow i = x.extend_slow i := rfl
@[simp, grind =] lemma extend_both [Zero α] (x y : Tree α n) (i : ℕ) :
    (both x y).extend_slow i =
      if i < 2 ^ n then x.extend_slow i else y.extend_slow (i - 2 ^ n) := rfl

/-- `extend` zero-extends beyond `x.size` -/
@[grind ←] lemma extend_of_le [Zero α] {n : ℕ} {x : Tree α n} {i : ℕ} (le : x.size ≤ i) :
    x.extend_slow i = 0 := by
  fun_induction extend_slow with grind

@[simp, grind =] lemma extend_cast_fun [Zero α] (e : n = m) {f : ℕ → ℕ} (x : Tree α (f n)) (i : ℕ) :
    (e ▸ x).extend_slow i = x.extend_slow i := by
  subst e; rfl

@[simp, grind =] lemma extend_cast [Zero α] (e : n = m) (x : Tree α n) (i : ℕ) :
    (e ▸ x).extend_slow i = x.extend_slow i := by
  subst e; rfl

-- DO NOT SUBMIT: Where to put this?
@[grind .] lemma Nat.two_pow_ne_zero : 2 ^ n ≠ 0 := by simp

lemma extend_eq_coeff_poly [CommRing α] (x : Tree α n) (i : ℕ) :
    x.extend_slow i = x.poly.coeff i := by
  induction x generalizing i <;> simp [extend_slow] <;> grind

/-!
### Conversion from a function
-/

def ofFn (n : ℕ) {s : ℕ} (f : Fin s → α) : Tree α n :=
  match n with
  | 0 => if h : s = 0 then zero else leaf (f ⟨0, by omega⟩)
  | n + 1 =>
    let x := ofFn n f
    if h : s ≤ 2 ^ n then left x else
    let g : Fin (s - 2 ^ n) → α := fun i ↦ f ⟨i + 2 ^ n, by omega⟩
    both x (ofFn n g)

@[simp] lemma size_ofFn (n : ℕ) {s : ℕ} (f : Fin s → α) :
    (ofFn n f).size = min s (2 ^ n) := by
  induction' n generalizing s f
  all_goals (simp only [ofFn]; aesop (add safe tactic (by omega)))

@[simp] lemma extend_ofFn [Zero α] (n : ℕ) {s : ℕ} (f : Fin s → α) (i : ℕ) :
    (ofFn n f).extend_slow i = if h : i < min s (2 ^ n) then f ⟨i, (by omega)⟩ else 0 := by
  induction' n generalizing s f i <;> simp [ofFn] <;> grind

/-!
### Prefix extraction
-/

def takes {n : ℕ} (x : Tree α n) (s : ℕ) : Tree α n := match n, x with
  | _, zero => zero
  | _, leaf x => if s = 0 then zero else leaf x
  | _, left x => left (takes x s)
  | n + 1, both x y => if s ≤ 2 ^ n then left (takes x s) else both x (takes y (s - 2 ^ n))

def take_le (m : ℕ) (x : Tree α (n + m)) (s : ℕ) : Tree α n := match m, x with
  | _, zero => zero
  | 0, x => takes x s
  | m + 1, left x => take_le m x s
  | m + 1, both x _ => take_le m x s

def take (x : Tree α n) (m s : ℕ) : Tree α (min n m) :=
  if le : m ≤ n then (min_eq_right le).symm ▸ take_le _ ((Nat.add_sub_cancel' le).symm ▸ x) s
  else (min_eq_left (not_le.mp le).le).symm ▸ takes x s

@[grind! .] lemma size_takes_le (x : Tree α n) (s : ℕ) : (takes x s).size ≤ s := by
  induction x generalizing s <;> simp [takes] <;> grind

@[grind! .] lemma size_take_le_le (x : Tree α (n + m)) (s : ℕ) : (take_le m x s).size ≤ s := by
  induction m generalizing s <;> unfold take_le <;> grind

@[simp, grind =] lemma extend_takes [Zero α] (x : Tree α n) (s i : ℕ) :
    (takes x s).extend_slow i = if i < s then x.extend_slow i else 0 := by
  induction' x generalizing s i <;> simp [takes] <;> grind

@[local grind ←] lemma le_two_pow_add (i a b : ℕ) (h : i < 2 ^ a) : i < 2 ^ (a + b) := by
  apply lt_of_lt_of_le h
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.le_add_right

@[simp, grind =] lemma extend_take_le [Zero α] (x : Tree α (n + m)) (s i : ℕ) :
    (take_le m x s).extend_slow i = if i < s ∧ i < 2 ^ n then x.extend_slow i else 0 := by
  induction m generalizing s i <;> cases x <;> simp [take_le] <;> try grind

@[simp] lemma extend_take [Zero α] (x : Tree α n) (s i : ℕ) :
    (take x m s).extend_slow i = if i < s ∧ i < 2 ^ m then x.extend_slow i else 0 := by
  simp [take]
  grind

/-!
### Componentwise map
-/

def map {n : ℕ} (x : Tree α n) (f : α → β) : Tree β n := match x with
  | zero => zero
  | leaf x => leaf (f x)
  | left x => left (map x f)
  | both x y => both (map x f) (map y f)

def mapIdx {n : ℕ} (x : Tree α n) (f : ℕ → α → β) (d : ℕ := 0) : Tree β n := match n, x with
  | _, zero => zero
  | _, leaf x => leaf (f d x)
  | _, left x => left (mapIdx x f d)
  | n + 1, both x y => both (mapIdx x f d) (mapIdx y f (d + 2 ^ n))

@[simp] lemma extend_map [Zero α] [Zero β] (x : Tree α n) (f : α → β) (f0 : f 0 = 0) (i : ℕ) :
    (map x f).extend_slow i = f (x.extend_slow i) := by
  induction' x generalizing i
  all_goals simp_all [map, apply_ite]

@[simp] lemma extend_mapIdx [Zero α] [Zero β] (x : Tree α n) (f : ℕ → α → β) {d : ℕ}
    (f0 : ∀ i, f i 0 = 0) (i : ℕ) : (mapIdx x f d).extend_slow i = f (d + i) (x.extend_slow i) := by
  induction' x generalizing i d
  all_goals simp_all [mapIdx, apply_ite]

@[simp] lemma size_map [Zero α] [Zero β] (x : Tree α n) (f : α → β) :
    (map x f).size = x.size := by
  induction' x
  all_goals simp_all [map]

@[simp] lemma size_mapIdx [Zero α] [Zero β] (x : Tree α n) (f : ℕ → α → β) {d : ℕ} :
    (mapIdx x f d).size = x.size := by
  induction' x generalizing d
  all_goals simp_all [mapIdx]

/-!
### Summation
-/

/-- Sum a tree -/
def sum [Zero α] [Add α] {n : ℕ} (x : Tree α n) : α := match x with
  | zero => 0
  | leaf x => x
  | left x => x.sum
  | both x y => x.sum + y.sum

@[simp] lemma sum_zero [Zero α] [Add α] : (zero : Tree α n).sum = 0 := rfl
@[simp] lemma sum_leaf [Zero α] [Add α] (x : α) : (leaf x).sum = x := rfl
@[simp] lemma sum_left [Zero α] [Add α] (x : Tree α n) : (left x).sum = x.sum := rfl
@[simp] lemma sum_both [Zero α] [Add α] (x y : Tree α n) : (both x y).sum = x.sum + y.sum := rfl
