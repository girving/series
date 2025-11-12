import Series.Series.Basic

/-!
# Sums of series coefficients

These are a bit awkward since we have to juggle `Array` and `Finset` sums.
-/

variable {n : ℕ}
variable {α' : Type} [NontriviallyNormedField α']
variable {β' : Type} [NontriviallyNormedField β']
variable {α : Type} [SeriesScalar α] [ApproxSeries α α']
variable {β : Type} [Zero β] [Add β] [Approx β β'] [ApproxZero β β'] [ApproxAdd β β']

/-- Sum the coefficients of a series, mapping it along the way. We'll require `g _ 0 = 0` later. -/
def Series.sum (f : Series α) (g : ℕ → α → β) : β :=
  (f.c.mapIdx g).sum

/-- Series sums approximate `series_coeff` sums -/
@[approx] lemma Series.approx_sum {f : Series α} {f' : α' → α'} (fa : approx f f') {g : ℕ → α → β}
    {g' : ℕ → α' → β'} (ga : ∀ k x x', approx x x' → approx (g k x) (g' k x'))
    (g0 : ∀ k, g' k 0 = 0) (fn : f.order = n) :
    approx (f.sum g) (∑ k ∈ Finset.range n, g' k (series_coeff k f' 0)) := by
  rw [← Finset.sum_subset (s₁ := Finset.range f.c.size) (s₂ := Finset.range n)
    (by simpa [fn] using f.le)]
  · simp only [sum, ← Array.sum_eq_sum_toList, Array.toList_mapIdx]
    generalize hxs : f.c.toList = xs
    generalize hys : (fun k ↦ series_coeff k f' 0) = ys
    replace hys : ∀ k, series_coeff k f' 0 = ys k := by simp [← hys]
    have se : f.c.size = xs.length := by simp [← hxs]
    have sa : ∀ k (h : k < xs.length), approx xs[k] (series_coeff k f' 0) := by
      intro k lt
      have a := (fa k (lt_of_lt_of_le (by simp [se, lt]) f.le)).2
      simp only [Series.extend_def, Array.extend_def, se, lt, dite_true] at a
      simp only [← hxs, Array.getElem_toList, a]
    simp only [se, hys] at sa ⊢
    clear f fa fn hxs se g0 f' hys
    induction' xs with x xs h generalizing g g' ys
    · simp
    · simp only [List.mapIdx_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
        add_comm _ (g' _ _)]
      refine approx_add (ga _ _ _ ?_) ?_
      · simpa using sa 0 (by simp)
      · apply h
        · intro k x x' a
          exact ga _ _ _ a
        · intro k lt
          simpa using sa (k + 1) (by simp; omega)
  · intro k lt m
    simp only [Finset.mem_range, not_lt] at lt m
    have z := (fa k (by simp [fn, lt])).2
    simp only [extend_def, Array.extend_def, not_lt.mpr m, ↓reduceDIte, approx_zero_iff] at z
    simp only [z, g0]
