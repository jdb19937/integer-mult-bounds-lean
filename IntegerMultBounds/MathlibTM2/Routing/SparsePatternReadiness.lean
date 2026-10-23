module

public import IntegerMultBounds.MathlibTM2.Routing.SparsePatternCoordinates

/-! Derive executed coordinate traversal readiness from ordered sparse positions
and a single width bound, rather than independent per-entry execution premises. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {W m N : ℕ}

theorem sparseCoordinatesReady_of_ordered (L cursor : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (horder : entries.Pairwise (fun a b => a.1 < b.1))
    (hbound : ∀ e ∈ entries, e.1 + 1 < 2 ^ L)
    (hcursor : ∀ e ∈ entries, cursor ≤ e.1) :
    SparseCoordinatesReady L cursor (sparseCoordinateValues entries) := by
  induction entries generalizing cursor with
  | nil => trivial
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
    refine ⟨hbound (x, q) (by simp), hcursor (x, q) (by simp), ?_⟩
    apply ih (x + 1) htail
    · intro e he; exact hbound e (List.mem_cons_of_mem _ he)
    · intro e he; have hh := hhead e he; omega

theorem sparsePatternCoordinates_bound (pos : ℕ → ℕ)
    (src : Fin m → Option (Fin W)) (hbound : ∀ j < m, pos j < N)
    (e : ℕ × Fin (W + 1)) (he : e ∈ sparsePatternCoordinates (N := N) pos src) : e.1 < N := by
  simp only [sparsePatternCoordinates, List.mem_reverse, List.mem_ofFn] at he
  obtain ⟨j, rfl⟩ := he
  have hj := hbound j.val j.isLt
  simp only
  omega

theorem sparsePatternCoordinates_ready (L : ℕ) (hN : N < 2 ^ L)
    (pos : ℕ → ℕ) (hpos : StrictMono pos)
    (src : Fin m → Option (Fin W)) (hbound : ∀ j < m, pos j < N) :
    SparseCoordinatesReady L 0 (sparseCoordinateValues (sparsePatternCoordinates (N := N) pos src)) := by
  apply sparseCoordinatesReady_of_ordered L 0 _ (sparsePatternCoordinates_ordered pos hpos src hbound)
  · intro e he
    have hh := sparsePatternCoordinates_bound pos src hbound e he
    omega
  · intro e he; omega

end IntegerMultBounds.MathlibTM2.Routing
