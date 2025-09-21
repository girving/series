import Interval.Unbundled
import Series.Pi
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

/-- Karatsuba multiplication of series, unordered `Subarray` version -/
@[irreducible] def Subarray.karatsuba' (f g : Subarray α) : Array α :=
  if h : g.size ≤ f.size then f.karatsuba g f.size rfl h
  else g.karatsuba f g.size rfl (by order)

/-- Karatsuba multiplication of `Series` -/
@[irreducible] def Series.mul (f g : Series α) : Series α :=
  let order := min f.order g.order
  let p := (f.c.takeLt order).karatsuba' (g.c.takeLt order)
  ⟨p.take (order.min_coe p.size), order, by simp⟩

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

@[simp] lemma Subarray.size_karatsuba' (f g : Subarray α) :
    (f.karatsuba' g).size = if f.size = 0 ∨ g.size = 0 then 0 else f.size + g.size - 1 := by
  rw [karatsuba']
  simp only [apply_dite (f := fun f : Array α ↦ f.size), size_karatsuba]
  grind

@[simp] lemma Series.order_mul {f g : Series α} : (f * g).order = min f.order g.order := by
  simp only [mul_def, mul]

lemma Series.size_mul {f g : Series α} :
    (f * g).c.size = if f.c.size = 0 ∨ g.c.size = 0 then 0 else
      (min f.order g.order).min_coe (f.c.size + g.c.size - 1) := by
  simp only [mul_def, mul, Subarray.size_karatsuba', tsub_zero, ENat.min_coe_eq_zero_iff,
    Array.size_eq_zero_iff, Array.take_eq_extract, Array.size_extract, ENat.min_min_coe_right,
    Array.size_takeLt]
  generalize min f.order g.order = o
  split_ifs with h
  all_goals simp_all
  induction' o with o
  · simp only [ENat.top_min_coe]
  · simp only [Nat.cast_eq_zero, ← Array.size_eq_zero_iff] at h
    simp only [ENat.coe_min_coe]
    omega

@[simp] lemma Subarray.karatsuba'_empty {f g : Subarray α} (g0 : g.size = 0) :
    f.karatsuba' g = #[] := by
  rw [← Array.size_eq_zero_iff]
  simp only [size_karatsuba', g0, or_true, ↓reduceIte]

@[simp] lemma Subarray.empty_karatsuba' {f g : Subarray α} (f0 : f.size = 0) :
    f.karatsuba' g = #[] := by
  rw [← Array.size_eq_zero_iff]
  simp only [size_karatsuba', f0, true_or, ↓reduceIte]

end Defs

/-!
### Correctness, exact case

`Subarray.karatsuba` and `Series.mul` are polynomial multiplication.
-/

section Exact

variable {f g : Subarray α} {x : α} {n : ℕ}

/-- `add_helper` is correct -/
@[simp] lemma Subarray.add_helper_extend [Zero α] [Add α] [AddZeroClass' α] (f g : Subarray α)
    (le : g.size ≤ f.size) (k : ℕ) : (f.add_helper g le).extend k = f.extend k + g.extend k := by
  simp only [add_helper, Fin.getElem_fin, Array.extend_ofFn]
  split_ifs
  · simp only [Subarray.eq_extend]
  · rw [Subarray.extend_of_le (by omega), Subarray.extend_of_le (by omega), zero_add']

variable [CommRing α]

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

@[simp] lemma Subarray.poly_karatsuba' : (f.karatsuba' g).poly = f.poly * g.poly := by
  rw [karatsuba']
  split_ifs with h
  all_goals simp only [poly_karatsuba, mul_comm]

lemma Subarray.extend_karatsuba' : (f.karatsuba' g).extend = (f.poly * g.poly).coeff := by
  ext i
  simp only [Array.extend_eq_coeff_poly, poly_karatsuba']

/-- `Series.mul` is modular polynomial multiplication -/
@[simp] lemma Series.poly_mul [Nontrivial α] {f g : Series α} :
    (f * g).poly = (f.poly * g.poly).trunc (min f.order g.order) := by
  rw [mul_def, mul, Series.poly]
  simp only
  simp only [Subarray.size_karatsuba', Array.size_takeLt, ENat.min_coe_eq_zero_iff,
    Array.size_eq_zero_iff, Array.take_eq_extract, Array.poly_take, Subarray.poly_karatsuba',
    Array.poly_takeLt]
  repeat rw [Array.size_takeLt]
  generalize horder : min f.order g.order = order
  by_cases o0 : order = 0; · simp [o0]
  by_cases f0 : f.c.size = 0
  · simp only [Array.size_eq_zero_iff] at f0
    simp [f0, Series.poly]
  by_cases g0 : g.c.size = 0
  · simp only [Array.size_eq_zero_iff] at g0
    simp [g0, Series.poly]
  have e : order.min_coe (order.min_coe f.c.size + order.min_coe g.c.size - 1) =
      order.min_coe (f.c.size + g.c.size - 1) := by
    induction' order with o
    · simp only [ENat.top_min_coe]
    · simp only [ENat.coe_min_coe]; omega
  split_ifs with h
  · simp only [ENat.min_coe_eq_zero_iff, f0, or_false, g0, or_self] at h
    simp only [h, Polynomial.trunc_zero, mul_zero, ENat.min_coe_zero, pow_zero,
      Polynomial.modByMonic_one]
  simp only [e]
  ext i
  by_cases h : i < order
  · simp only [Polynomial.coeff_modByMnnic_X_pow, ENat.lt_min_coe_iff, h, true_and, if_true,
      Polynomial.coeff_mul, Polynomial.coeff_trunc, mul_ite, ite_mul, zero_mul, mul_zero]
    split_ifs with lt
    · refine Finset.sum_congr rfl fun ⟨a,b⟩ m ↦ ?_
      simp only [Finset.mem_antidiagonal] at m
      simp only [← Array.extend_eq_coeff_poly, poly]
      have fle := f.le
      have gle := g.le
      split_ifs with h0 h1
      · rfl
      · simp only [not_lt] at h1
        have bad : (i : ℕ∞) < a := by order
        rw [Nat.cast_lt] at bad
        omega
      · simp only [not_lt] at h0
        have bad : (i : ℕ∞) < b := by order
        rw [Nat.cast_lt] at bad
        omega
    · symm
      refine Finset.sum_eq_zero fun ⟨a,b⟩ m ↦ ?_
      simp only [Finset.mem_antidiagonal] at m
      simp only [← Array.extend_eq_coeff_poly, poly]
      have le : f.c.size ≤ a ∨ g.c.size ≤ b := by omega
      rcases le with le | le
      all_goals simp only [Array.extend_of_le le, zero_mul, mul_zero]
  · simp only [Polynomial.coeff_modByMnnic_X_pow, ENat.lt_min_coe_iff, h, false_and, ↓reduceIte,
      Polynomial.coeff_trunc]

end Exact

/-!
### Karatsuba approximation

`Subarray.karatsuba` is a conservative approximation of polynomial multiplication.
-/

section KaratsubaApprox

variable [Zero α] [Add α] [AddZeroClass' α]
variable [Zero β] [Add β] [AddZeroClass' β]
variable [Approx α β] [ApproxAdd α β]
variable {f g : Subarray α} {f' g' : Subarray β} {n : ℕ}

/-- `Subarray.add_helper` is conservative -/
@[approx] lemma Subarray.approx_add_helper_extend (fa : approx f.extend f'.extend)
    (ga : approx g.extend g'.extend) (le : g.size ≤ f.size) (le' : g'.size ≤ f'.size) :
    approx (f.add_helper g le).extend (f'.add_helper g' le').extend := by
  intro i
  simp only [add_helper_extend]
  exact approx_add (fa _) (ga _)

/-- `Subarray.add_helper` is conservative -/
@[approx] lemma Subarray.approx_add_helper [ApproxZero α β] (fa : approx f f') (ga : approx g g')
    (le : g.size ≤ f.size) (le' : g'.size ≤ f'.size) :
    approx (f.add_helper g le) (f'.add_helper g' le') := by
  refine ⟨?_, ?_⟩
  · simp only [size_add_helper, fa.1]
  · intro i lt
    simp only [Array.eq_extend, add_helper_extend]
    approx

variable [Sub α] [Mul α]
variable [Sub β] [Mul β]
variable [ApproxSub α β] [ApproxMul α β] [ApproxZero α β]

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

/-- Karasuba multiplication is conservative -/
@[approx] lemma Subarray.approx_karatsuba' (fa : approx f f') (ga : approx g g') :
    approx (f.karatsuba' g) (f'.karatsuba' g') := by
  rw [karatsuba', karatsuba']
  have fs := fa.1
  have gs := ga.1
  split_ifs with h h'
  · convert Subarray.approx_karatsuba fa ga rfl h (by omega) (by omega)
  · omega
  · omega
  · convert Subarray.approx_karatsuba ga fa rfl (by omega) (by omega) (by omega)

end KaratsubaApprox

/-!
### Series approximation

`Series` multiplication is a conservative approximation of function multiplication.
-/

section Approx

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [ApproxRing α 𝕜] [CharZero 𝕜]

lemma mul_order_rearrange (fo go : ℕ∞) (fs gs : ℕ) :
    ((min fo go).min_coe ((min fo go).min_coe fs + (min fo go).min_coe gs - 1)) =
      ((min fo go).min_coe ((min fo go).min_coe (fo.min_coe fs) +
                            (min fo go).min_coe (go.min_coe gs) - 1)) := by
  all_goals induction' fo with fo
  all_goals induction' go with go
  all_goals simp; try omega

/-- Exact series multiply as polynomials -/
lemma Series.exact_mul {f g : Series α} {f' g' : 𝕜 → 𝕜}
    (df : ∀ i : ℕ, i < f.order → ContDiffAt 𝕜 i f' 0)
    (dg : ∀ i : ℕ, i < g.order → ContDiffAt 𝕜 i g' 0)
    (f0 : ∀ i : ℕ, f.c.size ≤ i → i < f.order → series_coeff i f' 0 = 0)
    (g0 : ∀ i : ℕ, g.c.size ≤ i → i < g.order → series_coeff i g' 0 = 0) :
    exact (f' * g') (f * g).order (f * g).c.size =
      exact f' f.order f.c.size * exact g' g.order g.c.size := by
  simp only [order_mul]
  ext i lt
  · simp only [order_exact, order_mul]
  · simp only [size_mul, Array.size_eq_zero_iff, size_exact, ENat.min_coe_eq_zero_iff, order_exact]
    split_ifs with h0 h1 h2
    · aesop
    · aesop
    · aesop
    · have fle := f.le
      have gle := g.le
      generalize f.order = fo at fle
      generalize g.order = go at gle
      induction' fo with fo
      all_goals induction' go with go
      all_goals simp at fle gle ⊢
      all_goals omega
  · simp only [size_mul, size_exact, ENat.lt_min_coe_iff, lt_inf_iff,
      apply_ite (f := fun x ↦ i < x), not_lt_zero', if_false_left, not_or] at lt
    obtain ⟨⟨fi,gi⟩,⟨fs0,gs0⟩,_,lt⟩ := lt
    simp only [exact, Array.extend_eq_coeff_poly, ← poly_def, poly_mul, Polynomial.coeff_trunc,
      lt_inf_iff, fi, gi, and_self, ↓reduceIte, Polynomial.coeff_mul]
    simp only [← Array.extend_eq_coeff_poly, Array.size_ofFn, size_mul, fs0, gs0, or_self,
      ↓reduceIte, ENat.lt_min_coe_iff, lt_inf_iff, fi, gi, and_self, lt, Array.extend_of_lt,
      Array.getElem_ofFn, series_coeff_mul (df i fi) (dg i gi), poly_def, Array.extend_ofFn,
      dite_eq_ite, mul_ite, ite_mul, zero_mul, mul_zero]
    refine Finset.sum_congr rfl fun p m ↦ ?_
    simp only [Finset.mem_antidiagonal] at m
    split_ifs with h0 h1
    · rfl
    · simp only [not_and, not_lt] at h1
      have lt : p.1 < f.order := lt_of_le_of_lt (by simp only [Nat.cast_le]; omega) fi
      rw [f0 _ (h1 lt) lt, zero_mul]
    · simp only [not_and, not_lt] at h0
      have lt : p.2 < g.order := lt_of_le_of_lt (by simp only [Nat.cast_le]; omega) gi
      rw [g0 _ (h0 lt) lt, mul_zero]

variable [AddZeroClass' α] [ApproxZeroIff α 𝕜]

/-- Series multiplication is conservative, function version -/
instance Series.instApproxMulFun : ApproxMul (Series α) (𝕜 → 𝕜) where
  approx_mul {f g f' g'} fa ga := by
    apply approx_of_exact
    · intro i lt
      simp only [Series.order_mul, lt_inf_iff] at lt
      exact (fa i lt.1).1.mul (ga i lt.2).1
    · intro i le lt
      simp only [order_mul, lt_inf_iff] at lt
      rw [series_coeff_mul]
      · simp only [size_mul, apply_ite (f := fun x ↦ x ≤ i), zero_le, if_true_left, not_or,
          and_imp, ENat.min_coe_le_iff, min_le_iff, not_le.mpr lt.1, not_le.mpr lt.2,
          false_or] at le
        refine Finset.sum_eq_zero fun ⟨a,b⟩ m ↦ ?_
        simp only [Finset.mem_antidiagonal, mul_eq_zero] at m ⊢
        have big : f.c.size ≤ a ∨ g.c.size ≤ b := by omega
        rcases big with big | big
        · exact .inl (series_coeff_eq_zero fa a big (lt_of_le_of_lt (by simp; omega) lt.1))
        · exact .inr (series_coeff_eq_zero ga b big (lt_of_le_of_lt (by simp; omega) lt.2))
      · exact (fa i lt.1).1
      · exact (ga i lt.2).1
    · rw [exact_mul]
      · generalize ho : min f.order g.order = order
        simp only [mul_def, mul, ho, order_exact, Subarray.size_karatsuba', Series.approx_def,
          extend_def, Array.size_takeLt, ENat.min_coe_eq_zero_iff, size_exact, lt_min_iff]
        intro i ⟨io,_⟩
        have o0 : order ≠ 0 := by contrapose io; simp_all
        have fo0 : f.order ≠ 0 := by contrapose o0; simp_all
        have go0 : g.order ≠ 0 := by contrapose o0; simp_all
        split_ifs with h0 h1 h2
        · simp only [o0, Array.size_eq_zero_iff, false_or] at h0
          rcases h0 with h0 | h0
          all_goals simp [h0]
        · simp only [o0, false_or, fo0, go0, not_or] at h1
          simp only [o0, h1, or_self] at h0
        · simp only [o0, false_or, not_or] at h0
          simp only [o0, fo0, h0, or_self, go0] at h2
        · apply Array.approx_extend
          have r := ho ▸ mul_order_rearrange f.order g.order f.c.size g.c.size
          rw [← r]
          apply Array.approx_take
          apply Subarray.approx_karatsuba'
          · refine ⟨by simp [← ho], fun i lt ↦ ?_⟩
            simp only [Array.size_takeLt, ENat.lt_min_coe_iff] at lt
            have flt : i < f.order := lt_of_lt_of_le lt.1 (by order)
            simp only [Subarray.eq_extend, lt.1, flt, lt.2, exact, Array.extend_takeLt,
              if_true, Array.extend_ofFn, ENat.lt_min_coe_iff, true_and, dite_true]
            exact (fa i flt).2
          · refine ⟨by simp [← ho], fun i lt ↦ ?_⟩
            simp only [Array.size_takeLt, ENat.lt_min_coe_iff] at lt
            have glt : i < g.order := lt_of_lt_of_le lt.1 (by order)
            simp only [Subarray.eq_extend, lt.1, glt, lt.2, exact, Array.extend_takeLt,
              if_true, Array.extend_ofFn, ENat.lt_min_coe_iff, true_and, dite_true]
            exact (ga i glt).2
      · intro i lt; exact (fa i lt).1
      · intro i lt; exact (ga i lt).1
      · intro i le lt; exact series_coeff_eq_zero fa _ le lt
      · intro i le lt; exact series_coeff_eq_zero ga _ le lt

end Approx
