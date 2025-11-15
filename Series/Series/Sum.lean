import Series.Series.Basic

/-!
# Sums of series coefficients

These are a bit awkward since we have to juggle `Array` and `Finset` sums.
-/

variable {n : ℕ}
variable {α' : Type} [NontriviallyNormedField α']
variable {β' : Type} [NontriviallyNormedField β']
variable {α : Type} [SeriesScalar α] [ApproxSeries α α']
variable {β : Type} [Zero β] [Add β] [Approx β β'] [ApproxZero β β'] [ApproxZeroIff α α']
  [ApproxAdd β β']

/-- Sum the coefficients of a series, mapping it along the way. We'll require `g _ 0 = 0` later. -/
def Series.sum (f : Series α) (g : ℕ → α → β) : β :=
  (f.c.mapIdx g).sum

/-- Tree summation approximates `Finset.sum` -/
lemma Series.Tree.approx_sum' {f : Tree α n} {g : ℕ → α → β} {f' : ℕ → α'} {g' : ℕ → α' → β'}
    {d m : ℕ} (fm : f.size ≤ m) (fa : ∀ k < m, approx (f.extend_slow k) (f' (d + k)))
    (ga : ∀ k x x', approx x x' → approx (g k x) (g' k x')) (g0 : ∀ k, g' k 0 = 0) :
    approx (f.mapIdx g d).sum (∑ k ∈ Finset.range m, g' (d + k) (f' (d + k))) := by
  induction' f with n x n x h n x y hx hy generalizing d m
  all_goals simp_all [mapIdx]
  · rw [Finset.sum_eq_zero]
    · approx
    · simp_all [approx_zero_iff]
  · rw [Finset.sum_eq_single (a := 0)]
    · specialize fa 0 (by omega)
      simp_all
    · intro i im i0
      specialize fa i (by simpa using im)
      simp only [i0, ↓reduceIte, approx_zero_iff] at fa
      simp_all
    · intro m0
      simp at m0
      omega
  · rw [← Finset.sum_subset (s₁ := Finset.range (2 ^ n + y.size)) (s₂ := Finset.range m),
      Finset.sum_range_add]
    · apply approx_add
      · refine hx x.size_le_pow fun k lt ↦ ?_
        simpa only [lt, ↓reduceIte] using fa k (by omega)
      · simp only [← add_assoc]
        refine hy (le_refl _) fun k lt ↦ ?_
        simpa [add_comm k, ← add_assoc] using fa (k + 2 ^ n) (by omega)
    · simp [fm]
    · intro k km le
      simp only [Finset.mem_range, not_lt] at le km
      have nk : ¬k < 2 ^ n := by omega
      have sk : y.size ≤ k - 2 ^ n := by omega
      specialize fa k (by omega)
      simp only [nk, ↓reduceIte, extend_of_le sk, approx_zero_iff] at fa
      simp only [fa, g0]

/-- Tree summation approximates `Finset.sum`, `d = 0` version -/
lemma Series.Tree.approx_sum {f : Tree α n} {g : ℕ → α → β} {f' : ℕ → α'} {g' : ℕ → α' → β'}
    {m : ℕ} (fm : f.size ≤ m) (fa : ∀ k < m, approx (f.extend_slow k) (f' k))
    (ga : ∀ k x x', approx x x' → approx (g k x) (g' k x')) (g0 : ∀ k, g' k 0 = 0) :
    approx (f.mapIdx g).sum (∑ k ∈ Finset.range m, g' k (f' k)) := by
  have h := Series.Tree.approx_sum' (f := f) (g := g) (f' := f') (g' := g') (fm := fm) (d := 0)
    ?_ ?_ g0
  all_goals simp_all

/-- Series sums approximate `series_coeff` sums -/
@[approx] lemma Series.approx_sum {f : Series α} {f' : α' → α'} (fa : approx f f') {g : ℕ → α → β}
    {g' : ℕ → α' → β'} (ga : ∀ k x x', approx x x' → approx (g k x) (g' k x'))
    (g0 : ∀ k, g' k 0 = 0) (fn : f.order = n) :
    approx (f.sum g) (∑ k ∈ Finset.range n, g' k (series_coeff k f' 0)) :=
  f.c.approx_sum (by simpa [fn] using f.size_le) (fun k lt ↦ (fa k (fn ▸ lt)).2) ga g0
