import Mathlib.Algebra.Order.Floor.Div
import Series.Analysis.Comp
import Series.Analysis.Newton
import Series.Analysis.Unique
import Series.Series.Const

/-!
# Newton's method for power series

Newton's method for scalar equations `f x = 0` is

  `x ← x - f x / f' x`

Sometimes in numerical analysis we apply Newton's method after some exact arithmetic trickery, so
our machinery is passed the entire iterative step rather than approximate routines for `f` and `f'`
separately.
-/

open Function (uncurry)
open Set
open scoped ContDiff Topology

variable {𝕜 : Type} [RCLike 𝕜]
variable {α : Type} [Zero α]

/-- Machinery for power series Newton iteration -/
structure Newton (α : Type) [Zero α] : Type where
  order : ℕ
  start : α
  step : Series α → Series α
  order_step : ∀ f : Series α, f.order ≤ order → (step f).order = f.order

namespace Newton

variable [Approx α 𝕜] {j k : ℕ} {n : Newton α} {f : 𝕜 → 𝕜 → 𝕜} {y : 𝕜 → 𝕜} {c : 𝕜}
attribute [simp] Newton.order_step

/-- Solve an equation via power series Newton's method -/
def solve (n : Newton α) (k : ℕ) : Series α :=
  if k ≤ 1 then .const n.start k else
  n.step ((n.solve (k ⌈/⌉ 2)).withOrder k)
  termination_by k
  decreasing_by simp only [Nat.ceilDiv_eq_add_pred_div, Nat.add_one_sub_one]; omega

/-- `solve` achieves the desired order -/
@[simp] lemma order_solve (le : k ≤ n.order) : (n.solve k).order = k := by
  rw [solve]
  split_ifs with c
  all_goals simp [le]

/-- Validity of a Newton iteration -/
structure Valid (n : Newton α) (f : 𝕜 → 𝕜 → 𝕜) (y : 𝕜 → 𝕜) (c : 𝕜) : Prop where
  df : ContDiffAt 𝕜 (n.order + 1) (uncurry f) (0, c)
  dy : ContDiffAt 𝕜 (n.order - 1) y 0
  fc : f 0 c = y 0
  f0 : deriv (f 0) c ≠ 0
  start : approx n.start c
  step : ∀ {x : Series α} {x' : 𝕜 → 𝕜}, x' 0 = c → approx x x' → x.order ≠ 0 → x.order ≤ n.order →
    approx (n.step x) (newton_step_fun f y x')

/-- The exact iteration that `solve` approximates -/
noncomputable def exact_solve (f : 𝕜 → 𝕜 → 𝕜) (y : 𝕜 → 𝕜) (c : 𝕜) (k : ℕ) : 𝕜 → 𝕜 :=
  if k ≤ 1 then fun _ ↦ c else
  newton_step_fun f y (exact_solve f y c (k ⌈/⌉ 2))
  termination_by k
  decreasing_by simp only [Nat.ceilDiv_eq_add_pred_div, Nat.add_one_sub_one]; omega

/-- `exact_solve` finds a solution of `f x = 0` -/
lemma Valid.exact_solve_correct (v : Valid n f y c) (jk : j ≤ n.order) :
    let x := exact_solve f y c j
    x 0 = c ∧ ContDiffAt 𝕜 (n.order - 1) x 0 ∧ (fun z ↦ f z (x z)) =ˢ[j] y := by
  induction' j using Nat.strong_induction_on with j h
  rw [exact_solve]
  split_ifs with j1
  · refine ⟨by simp, contDiffAt_const, fun i ij ↦ ?_⟩
    have i0 : i = 0 := by omega
    refine ⟨?_, v.dy.of_le (by simp [i0]), by simp [i0, v.fc]⟩
    simp [i0]
    exact (v.df.of_le (zero_le _)).comp (f := fun z ↦ (z, c)) _ (by fun_prop)
  · generalize hm : j ⌈/⌉ 2 = m
    have mj : m < j := by simp [Nat.ceilDiv_eq_add_pred_div] at hm; omega
    have mk : m < n.order := lt_of_lt_of_le (by norm_cast) jk
    have k1 : Sub.sub n.order 1 = n.order - 1 := rfl
    obtain ⟨x0, dx, fx⟩ := h m mj mk.le
    refine ⟨?_, ?_, ?_⟩
    · simp [newton_step_fun, x0, v.fc]
    · apply ContDiffAt.newton_step (m := n.order + 1)
      · simp [x0]
        exact v.df.of_le (by norm_cast)
      · simp [x0, v.f0]
      · exact dx.of_le (by rfl)
      · apply v.dy
      · norm_cast; apply add_le_add_right; simp
    · apply newton_step_quadratic (m := n.order + 1)
      · simp only [x0]
        exact v.df.of_le (by norm_cast)
      · simp [x0, v.f0]
      · exact dx.of_le (by apply tsub_le_tsub_right; norm_cast)
      · apply v.dy.of_le; apply tsub_le_tsub_right; norm_cast
      · exact fx
      · exact add_le_add_right (by norm_cast) _
      · simp only [Nat.ceilDiv_eq_add_pred_div, Nat.add_one_sub_one] at hm
        omega

/-- Newton solves approximate any solution to the equation -/
lemma Valid.approx_exact [ApproxZero α 𝕜] (v : n.Valid f y c) (jk : j ≤ n.order) {x : 𝕜 → 𝕜}
    (x0 : x 0 = c) (dx : ∀ i < j, ContDiffAt 𝕜 i x 0) (fx : (fun z ↦ f z (x z)) =ˢ[j] y) :
    approx (n.solve j) x := by
  induction' j using Nat.strong_induction_on with j h generalizing x
  rw [solve]
  split_ifs with j1
  · intro i lt
    simp only [Series.order_const] at lt
    have i0 : i = 0 := by omega
    have j0 : j ≠ 0 := by omega
    have j0' : 0 < j := by omega
    simp only [i0, CharP.cast_eq_zero, Series.extend_const, ne_eq, j0, not_false_eq_true, and_self,
      ↓reduceIte, series_coeff_zero']
    exact ⟨dx _ (by omega), x0 ▸ v.start⟩
  · generalize hi : j ⌈/⌉ 2 = i
    simp only [Nat.ceilDiv_eq_add_pred_div] at hi
    have ij : i < j := by omega
    have i1 : 1 ≤ i := by omega
    have io : i ≤ n.order := le_trans (by order) jk
    have ux : approx ((n.solve i).withOrder j)
        (seriesTrunc x (min (n.solve i).order j) 0) := by
      apply Series.approx_withOrder_seriesTrunc
      exact h _ (by omega) io x0 (fun _ _ ↦ dx _ (by omega)) (fx.mono (by omega))
    rw [order_solve io, min_eq_left ij.le] at ux
    set u := n.solve i with hu
    have xt0 : seriesTrunc x i 0 0 = c := by rw [seriesTrunc_const (by omega), x0]
    refine Series.congr_right (n := j) (v.step xt0 ux (by simp; omega) (by simp; omega)) ?_ ?_
    · refine solution_unique (x0 ▸ v.df) (x0 ▸ v.f0) dx ?_ fx ?_ ?_ ?_
      · intro a aj
        apply (xt0 ▸ v.df).newton_step (xt0 ▸ v.f0)
        · fun_prop
        · apply v.dy.of_le
          trans ↑j - 1
          · norm_cast; omega
          · apply tsub_le_tsub_right; norm_cast
        · simp only [WithTop_ENat.add_one_le_add_one]
          trans ↑j
          · simp [aj.le]
          · norm_cast
      · refine newton_step_quadratic (xt0 ▸ v.df) (xt0 ▸ v.f0) (k := i) (by fun_prop) ?_ ?_
          (by simp; norm_cast) (by omega)
        · apply v.dy.of_le; apply tsub_le_tsub_right; norm_cast
        · refine SeriesEq.trans (SeriesEq.comp_param_left ?_ ?_) (fx.mono (by omega))
          · exact fun a ai ↦ (xt0 ▸ v.df).of_le (by
              trans ↑n.order; trans ↑i; simp [ai.le]; norm_cast; simp)
          · exact SeriesEq.trunc fun a ai ↦ dx _ (by omega)
      · simp [newton_step_fun, xt0, v.fc, x0]
      · have k1 : Add.add n.order 1 = n.order + 1 := rfl
        norm_cast
        exact le_trans jk (by simp [add_assoc])
    · rw [order_step]
      all_goals simp [jk]
