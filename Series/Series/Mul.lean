import Series.Series.Basic

/-!
# Multiplication of `Series`

We use https://en.wikipedia.org/wiki/Karatsuba_algorithm.
-/

open Finset (antidiagonal)
open Polynomial (C X)
open Set
open scoped Polynomial Topology

variable {α β : Type}

/-!
### Definitions
-/

section Defs

variable [Zero α] [Add α]

/-- Add two `Subarray`s of different size, forming an `Array`. The first must be the larger. -/
def Subarray.add_helper (f g : Subarray α) (_ : g.size ≤ f.size) : Array α :=
  .ofFn fun i : Fin f.size ↦ f[i] + g.extend i

@[simp] lemma Subarray.size_add_helper (f g : Subarray α) (le : g.size ≤ f.size) :
    (f.add_helper g le).size = f.size := by simp [Subarray.add_helper]

variable [Sub α] [Mul α]

/-- Karatsuba multiplication of series, `Subarray` version -/
def Subarray.karatsuba (f g : Subarray α) (n : ℕ) (fn : f.size = n) (gn : g.size ≤ n) : Array α :=
  -- Base cases
  if h : g.size = 0 then #[] else
  if h : g.size = 1 then .ofFn fun i : Fin f.size ↦ f[i] * g[0] else
  if h : f.size = 2 then #[f[0] * g[0], f[0] * g[1] + f[1] * g[0], f[1] * g[1]] else
  let lo := (n + 1) / 2
  let hi := n - lo
  let f0 := f.take lo
  let f1 := f.drop lo
  let g0 := g.take lo
  let g1 := g.drop lo
  let p00 : Array α := f0.karatsuba g0 lo
    (by simp only [Subarray.size_take, f0]; omega)
    (by simp only [Subarray.size_take, g0]; omega)
  let p11 : Array α := f1.karatsuba g1 hi
    (by simp only [Subarray.size_drop, f1]; omega)
    (by simp only [Subarray.size_drop, g1]; omega)
  let fm := (f0.add_helper f1 (by simp [f0, f1]; omega)).toSubarray
  let gm := (g0.add_helper g1 (by simp [g0, g1]; omega)).toSubarray
  let pm := fm.karatsuba gm lo (by simp [fm, f0]; omega) (by simp [gm, g0])
  .ofFn fun i : Fin (n + (g.size - 1)) ↦
    if i < lo then p00.extend i else
    if i < 2 * lo then (pm.extend (i - lo) + p00.extend i) -
                       (p00.extend (i - lo) + p11.extend (i - lo)) else
    if i < 3 * lo then (p11.extend (i - 2 * lo) + pm.extend (i - lo)) -
                       (p00.extend (i - lo) + p11.extend (i - lo)) else
    p11.extend (i - 2 * lo)

/-- Karatsuba multiplication of `Series` -/
@[irreducible] def Series.mul (f g : Series α) : Series α :=
  let n := min f.n g.n
  let f' := f.c.toSubarray (stop := n)
  let g' := g.c.toSubarray (stop := n)
  -- TODO: Avoid unnecessarily computing coefficients beyond `n`
  let p := f'.karatsuba g' n (by simp [f', n, Series.n]) (by simp [g'])
  ⟨p.take n⟩

/-- Karatsuba multiplication of `Series` -/
instance Series.instMul : Mul (Series α) where
  mul f g := f.mul g

lemma Series.mul_def (f g : Series α) : f * g = f.mul g := rfl

/-!
### Basic properties
-/

@[simp] lemma Subarray.size_karatsuba (f g : Subarray α) (n : ℕ) (fn : f.size = n)
    (gn : g.size ≤ n) :
    (f.karatsuba g n fn gn).size = if g.size = 0 then 0 else f.size + g.size - 1 := by
  rw [karatsuba]
  split_ifs
  all_goals simp; try omega

@[simp] lemma Series.n_mul {f g : Series α} : (f * g).n = min f.n g.n := by
  simp only [n, mul_def, mul, Array.take_eq_extract, Array.size_extract, Subarray.size_karatsuba,
    Array.size_toSubarray', inf_le_right, inf_of_le_right, tsub_zero, Nat.min_eq_zero_iff,
    Array.size_eq_zero_iff, inf_le_left, Nat.min_assoc]
  split_ifs with h
  all_goals simp only [Array.size_toSubarray'] at h; omega

end Defs

/-!
### Correctness, exact case

`Subarray.karatsuba` and `Series.mul` are polynomial multiplication.
-/

section Exact

variable [CommRing α] {f g : Subarray α} {x : α} {n : ℕ}

/-- `add_helper` is correct -/
@[simp] lemma Subarray.add_helper_extend (f g : Subarray α) (le : g.size ≤ f.size)
    (k : ℕ) : (f.add_helper g le).extend k = f.extend k + g.extend k := by
  simp only [add_helper, Fin.getElem_fin, Array.extend_ofFn]
  split_ifs
  · simp only [Subarray.eq_extend]
  · rw [Subarray.extend_of_le (by omega), Subarray.extend_of_le (by omega), zero_add]

/-- Karatsuba multiplication of series, `Subarray` version -/
@[simp] lemma Subarray.poly_karatsuba (fn : f.size = n) (gn : g.size ≤ n) :
    (f.karatsuba g n fn gn).poly = f.poly * g.poly := by
  induction' n using Nat.strong_induction_on with n h generalizing f g
  rw [karatsuba]
  -- Induction base cases
  by_cases gs0 : g.size = 0
  · simp only [gs0, ↓reduceDIte, Array.poly_empty, poly_empty, mul_zero]
  simp only [gs0, dite_false]
  by_cases gs1 : g.size = 1
  · simp only [gs1, ↓reduceDIte, Fin.getElem_fin, poly_mul, poly_one, mul_comm f.poly, smul_one_mul]
  simp only [gs1, dite_false]
  by_cases fs2 : f.size = 2
  · have g2 : g.size = 2 := by omega
    simp [fs2, g2, poly_two, mul_add, add_mul, Array.poly, smul_mul_smul, ← pow_two, smul_smul,
      add_smul]
    ring_nf
  simp only [fs2, ↓reduceDIte, size_add_helper, size_take]
  -- Replace recursive Karatsuba calls
  have kt : ∀ g' n' fn' gn' i, ((f.take ((n + 1) / 2)).karatsuba g' n' fn' gn').extend i =
      ((f.take ((n + 1) / 2)).poly * g'.poly).coeff i := by
    intro g n fn gn i
    rw [Array.extend_eq_coeff_poly, h _ (by simp at fn; omega)]
  have kd : ∀ g' n' fn' gn' i, ((f.drop ((n + 1) / 2)).karatsuba g' n' fn' gn').extend i =
      ((f.drop ((n + 1) / 2)).poly * g'.poly).coeff i := by
    intro g n fn gn i
    rw [Array.extend_eq_coeff_poly, h _ (by simp at fn; omega)]
  have ks : ∀ a b ah g' n' fn' gn' i,
      ((((f.take ((n + 1) / 2)).add_helper (f.drop ((n + 1) / 2)) ah).toSubarray a b).karatsuba
        g' n' fn' gn').extend i =
      ((((f.take ((n + 1) / 2)).add_helper (f.drop ((n + 1) / 2)) ah).toSubarray a b).poly *
        g'.poly).coeff i := by
    intro a b ah g n fn gn i
    rw [Array.extend_eq_coeff_poly, h _ (by simp at fn; omega)]
  have ap : ∀ (f' : Subarray α) ah, (((f'.take ((n + 1) / 2)).add_helper
      (f'.drop ((n + 1) / 2)) ah).toSubarray 0 (min f'.size ((n + 1) / 2))).poly =
      (f'.take ((n + 1) / 2)).poly + (f'.drop ((n + 1) / 2)).poly := by
    intro f' ah
    ext i
    rw [Polynomial.coeff_add, Array.poly_toSubarray, ← Array.extend_eq_coeff_poly]
    · simp only [add_helper_extend, extend_take, extend_drop, ← extend_eq_coeff_poly]
    · simp only [size_add_helper, size_take]
  simp only [kt, ks, kd, ap]
  clear kt ks kd ap h
  -- Replace with clean polynomials
  generalize hlo : (n + 1) / 2 = lo
  generalize hhi : n - lo = hi
  generalize hf0 : f.take lo = f0
  generalize hf1 : f.drop lo = f1
  generalize hg0 : g.take lo = g0
  generalize hg1 : g.drop lo = g1
  have fe : f.poly = f0.poly + f1.poly * X ^ lo := by simp only [← hf0, ← hf1, split_poly]
  have ge : g.poly = g0.poly + g1.poly * X ^ lo := by simp only [← hg0, ← hg1, split_poly]
  generalize hm : g.size = m
  have mn : m ≤ n := by omega
  have f0s : f0.size ≤ lo := by simp only [← hf0, size_take]; omega
  have f1s : f1.size ≤ n - lo := by simp only [← hf1, size_drop]; omega
  have g0s : g0.size ≤ lo := by simp only [← hg0, size_take]; omega
  have g1s : g1.size ≤ m - lo := by simp only [← hg1, size_drop]; omega
  have lo2 : 2 ≤ lo := by omega
  -- Descend into `Array.ofFn`
  ext i
  simp only [← Array.extend_eq_coeff_poly, Array.extend_ofFn]
  clear gs0 gs1 fs2 hg0 hg1 hf0 hf1 hi hhi gn
  generalize hY : (X : α[X]) ^ lo = Y at fe ge
  have yd : Y.natDegree ≤ lo := by simp only [← hY, Polynomial.natDegree_X_pow_le]
  have yd2 : (Y ^ 2).natDegree ≤ 2 * lo := by
    simp only [← hY, ← pow_mul', Polynomial.natDegree_X_pow_le]
  -- Index lowering lemmas
  have low : ∀ (le : lo ≤ i := by omega) {f : α[X]}, f.coeff (i - lo) = (f * Y).coeff i :=
    fun le {f} ↦ by simp only [← hY, Polynomial.coeff_mul_X_pow', le, ↓reduceIte]
  have low2 : ∀ (le : 2 * lo ≤ i := by omega) {f : α[X]},
      f.coeff (i - 2 * lo) = (f * Y ^ 2).coeff i :=
    fun le {f} ↦ by simp only [← hY, ← pow_mul, mul_comm lo, Polynomial.coeff_mul_X_pow', le,
      ↓reduceIte]
  -- Zero lemmas
  have i_uy : ∀ (lt : i < lo := by omega) {u : α[X]}, (u * Y).coeff i = 0 := by
    intro lt u
    simp only [← hY, Polynomial.coeff_mul_X_pow', not_le.mpr lt, ↓reduceIte]
  have i_uy2 : ∀ (lt : i < 2 * lo := by omega) {u : α[X]}, (u * Y ^ 2).coeff i = 0 := by
    intro lt u
    simp only [← hY, Polynomial.coeff_mul_X_pow', not_le.mpr lt, ↓reduceIte, ← pow_mul']
  have uvz_i : ∀ (u v : Subarray α) {z : α[X]}
      (h : (u.size - 1) + (v.size - 1) + z.natDegree < i := by omega),
      (u.poly * v.poly * z).coeff i = 0 := by
    intro u v z h
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc (u.poly * v.poly * z).natDegree
      _ ≤ (u.poly * v.poly).natDegree + z.natDegree := by bound
      _ ≤ u.poly.natDegree + v.poly.natDegree + z.natDegree := by bound
      _ ≤ (u.size - 1) + (v.size - 1) + z.natDegree := by bound
      _ < i := h
  have uv_i : ∀ {u v : Subarray α} (h : u.size - 1 + (v.size - 1) < i := by omega),
      (u.poly * v.poly).coeff i = 0 := by
    intro u v h
    rw [← mul_one (u.poly * v.poly)]
    exact uvz_i _ _ (by simp only [Polynomial.natDegree_one, add_zero, h])
  -- Case analysis
  split_ifs with h0 h1 h2 h3
  · simp only [fe, ge, mul_add, add_mul, mul_assoc _ Y, mul_comm Y, ← pow_two, Polynomial.coeff_add,
      ← mul_assoc _ _ Y]
    rw [i_uy, i_uy, i_uy2]
    ring
  · simp only [fe, ge, mul_add, add_mul, mul_assoc _ Y, mul_comm Y, ← pow_two, Polynomial.coeff_add,
      ← mul_assoc _ _ Y]
    rw [low, low, low, i_uy2]
    ring
  · simp only [fe, ge, mul_add, add_mul, mul_assoc _ Y, mul_comm Y, ← pow_two, Polynomial.coeff_add,
      ← mul_assoc _ _ Y]
    rw [low, low, low, low2, uv_i]
    ring
  · simp only [fe, ge, mul_add, add_mul, mul_assoc _ Y, mul_comm Y, ← pow_two, Polynomial.coeff_add,
      ← mul_assoc _ _ Y]
    rw [low2, uv_i, uvz_i f0 g1, uvz_i f1 g0]
    ring
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    calc (f.poly * g.poly).natDegree
      _ ≤ f.poly.natDegree + g.poly.natDegree := by bound
      _ ≤ (f.size - 1) + (g.size - 1) := by bound
      _ < i := by omega

/-- `Series.mul` is modular polynomial multiplication -/
@[simp] lemma Series.poly_mul [Nontrivial α] {f g : Series α} :
    (f * g).poly = f.poly * g.poly %ₘ X ^ min f.n g.n := by
  rw [mul_def, mul, Series.poly]
  simp only
  simp only [Array.take_eq_extract, Array.poly_take, Subarray.poly_karatsuba,
    Array.poly_toSubarray']
  ext i
  by_cases h : i < min f.n g.n
  · simp only [lt_inf_iff] at h
    simp only [Polynomial.coeff_modByMnnic_X_pow, lt_inf_iff, h, and_self, ↓reduceIte,
      Polynomial.coeff_mul, mul_ite, ite_mul, zero_mul, mul_zero]
    refine Finset.sum_congr rfl fun ⟨a,b⟩ m ↦ ?_
    simp only [Finset.mem_antidiagonal] at m
    split_ifs
    all_goals try simp; omega
    rfl
  · trans 0
    all_goals simp only [Polynomial.coeff_modByMnnic_X_pow, h, ↓reduceIte]

end Exact

/-!
### Karatsuba approximation

`Subarray.karatsuba` is a conservative approximation of polynomial multiplication.
-/

section KaratusbaApprox

variable [Zero α] [Add α]
variable [Zero β] [Add β]
variable [Approx α β] [ApproxZero α β] [ApproxAdd α β]
variable {f g : Subarray α} {f' g' : Subarray β} {n : ℕ}

/-- `Subarray.add_helper` is conservative -/
@[approx] lemma Subarray.approx_add_helper (fa : approx f f') (ga : approx g g')
    (le : g.size ≤ f.size) (le' : g'.size ≤ f'.size) :
    approx (f.add_helper g le) (f'.add_helper g' le') := by
  refine ⟨?_, ?_⟩
  · simp only [size_add_helper, fa.1]
  · intro i lt
    simp only [add_helper, Fin.getElem_fin, Array.getElem_ofFn]
    approx

variable [Sub α] [Mul α] variable [Sub β] [Mul β]
variable [ApproxSub α β] [ApproxMul α β]

/-- Karasuba multiplication is conservative -/
@[approx] lemma Subarray.approx_karatsuba (fa : approx f f') (ga : approx g g') (fn : f.size = n)
    (gn : g.size ≤ n) (fn' : f'.size = n) (gn' : g'.size ≤ n) :
    approx (f.karatsuba g n fn gn) (f'.karatsuba g' n fn' gn') := by
  induction' n using Nat.strong_induction_on with n h generalizing f g f' g'
  have fs := fa.1
  have gs := ga.1
  refine ⟨by simp only [size_karatsuba, gs, fn, fn'], fun i lt ↦ ?_⟩
  simp only [size_karatsuba, Array.eq_extend] at lt ⊢
  rw [karatsuba, karatsuba]
  by_cases g0 : g.size = 0
  · have g0' : g'.size = 0 := by simpa only [← ga.1]
    simp only [g0, ↓reduceDIte, List.size_toArray, List.length_nil, zero_le, Array.extend_of_le,
      gs ▸ g0, approx_zero]
  simp only [g0, ↓reduceDIte, Fin.getElem_fin, size_add_helper, size_take, gs ▸ g0]
  by_cases g1 : g.size = 1
  · simp only [g1, ↓reduceDIte, Array.extend_ofFn, gs ▸ g1]
    by_cases fi : i < f.size
    · simp only [fi, ↓reduceDIte, fs ▸ fi]
      approx
    · simp only [fi, ↓reduceDIte, fs ▸ fi, approx_zero]
  simp only [g1, ↓reduceDIte, gs ▸ g1]
  by_cases f2 : f.size = 2
  · simp only [f2, ↓reduceDIte, fs ▸ f2]
    approx
  simp only [f2, ↓reduceDIte, Array.extend_ofFn, dite_eq_ite, ← fs, ← gs]
  split_ifs with h0 h1
  all_goals try apply approx_sub
  all_goals try apply approx_add
  all_goals try apply approx_zero
  all_goals apply Array.approx_extend; apply h _ (by omega); all_goals approx

/-- Series multiplication is conservative, `Series` version -/
instance Series.instApproxMulSeries : ApproxMul (Series α) (Series β) where
  approx_mul {f g f' g'} fa ga := by
    simp only [mul_def, mul, approx_def, Series.n]
    simp only [← fa.1, ← ga.1]
    approx

/-- `Series.mul` depends only on shared coefficients -/
lemma Series.mul_congr {f g f' g' : Series α} {n : ℕ} (h : min f.n g.n = n) (h' : min f'.n g'.n = n)
    (fe : ∀ i < n, f.c.extend i = f'.c.extend i) (ge : ∀ i < n, g.c.extend i = g'.c.extend i) :
    f * g = f' * g' := by
  ext i lt
  · simp only [n_mul, h, h']
  · suffices a : approx (f * g) (f' * g') by simpa only [Array.eq_extend, approx] using a.2 _ lt
    simp only [mul_def, mul, approx_def, h, h']
    simp only [Series.n, min_eq_iff] at h h'
    have n0 : n ≤ f.c.size := by omega
    have n1 : n ≤ f'.c.size := by omega
    have n2 : n ≤ g.c.size := by omega
    have n3 : n ≤ g'.c.size := by omega
    apply Array.approx_take
    apply Subarray.approx_karatsuba
    all_goals simp [approx, n0, n1, n2, n3, Array.eq_extend]; assumption

end KaratusbaApprox

/-!
### Series approximation

`Series` multiplication is a conservative approximation of function multiplication.
-/

section Approx

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
variable [ApproxRing α 𝕜]

/-- Exact series multiply as polynomials -/
lemma Series.exact_mul {f g : 𝕜 → 𝕜} {n : ℕ} (df : ∀ i < n, ContDiffAt 𝕜 i f 0)
    (dg : ∀ i < n, ContDiffAt 𝕜 i g 0) : exact (f * g) n = exact f n * exact g n := by
  ext i lt
  · simp only [n_exact, n_mul, min_self]
  · simp only [n_exact] at lt
    simp only [exact, Array.size_ofFn, lt, Array.extend_of_lt, Array.getElem_ofFn,
      Array.extend_eq_coeff_poly, ← poly_def, poly_mul, n_mk, min_self,
      Polynomial.coeff_modByMnnic_X_pow, ↓reduceIte, Polynomial.coeff_mul]
    simp only [series_coeff_mul (df i lt) (dg i lt), poly_def, ← Array.extend_eq_coeff_poly,
      Array.extend_ofFn, dite_eq_ite, mul_ite, ite_mul, zero_mul, mul_zero]
    refine Finset.sum_congr rfl fun p m ↦ ?_
    simp only [Finset.mem_antidiagonal] at m
    split_ifs
    · rfl
    · omega
    · omega

/-- Series multiplication is conservative, function version -/
instance Series.instApproxMulFun : ApproxMul (Series α) (𝕜 → 𝕜) where
  approx_mul {f g f' g'} fa ga := by
    rw [Series.approx_iff_exact] at fa ga ⊢
    constructor
    · intro i lt
      simp only [Series.n_mul, lt_inf_iff] at lt
      exact (fa.1 i lt.1).mul (ga.1 i lt.2)
    · simp only [Series.n_mul]
      rw [Series.exact_mul]
      · rw [Series.mul_congr (f' := Series.exact f' f.n) (g' := Series.exact g' g.n)
          (n := min f.n g.n)]
        · approx
        · simp only [Series.n_exact, min_self]
        · simp only [Series.n_exact]
        · intro i lt; simp only [lt_inf_iff] at lt; simp [exact, lt]
        · intro i lt; simp only [lt_inf_iff] at lt; simp [exact, lt]
      · intro i lt; simp only [lt_inf_iff] at lt; exact fa.1 i lt.1
      · intro i lt; simp only [lt_inf_iff] at lt; exact ga.1 i lt.2

end Approx
