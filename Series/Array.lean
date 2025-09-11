/-!
# Array facts
-/

variable {α β γ : Type}

/-- Compose `Array.mapIdx` with `Array.map` -/
theorem Array.mapIdx_map (f : Nat → β → γ) (g : α → β) (a : Array α) :
    (a.map g).mapIdx f = a.mapIdx (fun k x ↦ f k (g x)) := by
  ext k
  · simp only [Array.size_mapIdx, Array.size_map]
  · simp only [Array.getElem_mapIdx, Array.getElem_map]
