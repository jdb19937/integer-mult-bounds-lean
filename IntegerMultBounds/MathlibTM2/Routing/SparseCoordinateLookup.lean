module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateCoverage

/-! Absolute target lookup in the expanded coordinate runs. Ordered coordinates
read exactly their supplied selector, even when source selectors repeat. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {W : ℕ}

theorem sparseCoordinatesReady_member (L cursor : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (hr : SparseCoordinatesReady L cursor (sparseCoordinateValues entries))
    (x : ℕ) (q : Fin (W + 1)) (hm : (x, q) ∈ entries) : cursor ≤ x := by
  induction entries generalizing cursor with
  | nil => simp at hm
  | cons pair rest ih =>
    obtain ⟨y, r⟩ := pair
    obtain ⟨_, hcy, ht⟩ := hr
    rcases List.mem_cons.mp hm with he | hm
    · cases he; exact hcy
    · have hh := ih (y + 1) ht hm
      omega

theorem sparseCoordinateLookup_target (L cursor : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (hr : SparseCoordinatesReady L cursor (sparseCoordinateValues entries))
    (x : ℕ) (q : Fin (W + 1)) (hm : (x, q) ∈ entries) :
    (SparseSelectorRun.expand (sparseCoordinateRuns cursor entries))[x - cursor]? = some q := by
  induction entries generalizing cursor with
  | nil => simp at hm
  | cons pair rest ih =>
    obtain ⟨y, r⟩ := pair
    obtain ⟨_, hcy, ht⟩ := hr
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      simp only [sparseCoordinateRuns, SparseSelectorRun.expand, SparseSelectorRun.indices]
      rw [List.getElem?_append_left (by simp)]
      rw [List.getElem?_append_right (by simp)]
      simp
    · have hxy := sparseCoordinatesReady_member L (y + 1) rest ht x q hm
      simp only [sparseCoordinateRuns, SparseSelectorRun.expand]
      rw [List.getElem?_append_right (by rw [SparseSelectorRun.indices_length]; simp only; omega)]
      rw [SparseSelectorRun.indices_length]
      have hi : x - cursor - (y - cursor + 1) = x - (y + 1) := by omega
      rw [hi]
      exact ih (y + 1) ht hm

theorem sparseCoordinateLookup_gap (L cursor : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (hr : SparseCoordinatesReady L cursor (sparseCoordinateValues entries))
    (x : ℕ) (hcx : cursor ≤ x)
    (hx : x < sparseCoordinateEnd cursor (sparseCoordinateValues entries))
    (hoff : ∀ q, (x, q) ∉ entries) :
    (SparseSelectorRun.expand (sparseCoordinateRuns cursor entries))[x - cursor]? = some 0 := by
  induction entries generalizing cursor with
  | nil => simp only [sparseCoordinateValues, List.map_nil, sparseCoordinateEnd] at hx; omega
  | cons pair rest ih =>
    obtain ⟨y, r⟩ := pair
    obtain ⟨_, hcy, ht⟩ := hr
    have hne : x ≠ y := by
      intro he; subst x
      exact hoff r (by simp)
    by_cases hxy : x < y
    · simp only [sparseCoordinateRuns, SparseSelectorRun.expand, SparseSelectorRun.indices]
      rw [List.getElem?_append_left (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega)]
      rw [List.getElem?_append_left (by simp only [List.length_replicate]; omega)]
      simp [show x - cursor < y - cursor by omega]
    · have hyx : y + 1 ≤ x := by omega
      simp only [sparseCoordinateRuns, SparseSelectorRun.expand]
      rw [List.getElem?_append_right (by rw [SparseSelectorRun.indices_length]; simp only; omega)]
      rw [SparseSelectorRun.indices_length]
      have hi : x - cursor - (y - cursor + 1) = x - (y + 1) := by omega
      rw [hi]
      apply ih (y + 1) ht hyx
      · exact hx
      · intro q hq; exact hoff q (List.mem_cons_of_mem _ hq)

end IntegerMultBounds.MathlibTM2.Routing
