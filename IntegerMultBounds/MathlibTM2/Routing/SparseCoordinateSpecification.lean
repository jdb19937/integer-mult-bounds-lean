module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateLookup

/-! Target and gap lookup specifications identify the whole generated dense
selector list, including the reversed list required by descriptor compilation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {W : ℕ}

theorem sparseCoordinateRuns_eq (L : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (hr : SparseCoordinatesReady L 0 (sparseCoordinateValues entries))
    (qs : List (Fin (W + 1)))
    (hend : sparseCoordinateEnd 0 (sparseCoordinateValues entries) = qs.length)
    (htarget : ∀ x q, (x, q) ∈ entries → qs[x]? = some q)
    (hgap : ∀ x, x < qs.length → (∀ q, (x, q) ∉ entries) → qs[x]? = some 0) :
    SparseSelectorRun.expand (sparseCoordinateRuns 0 entries) = qs := by
  have hlen : (SparseSelectorRun.expand (sparseCoordinateRuns 0 entries)).length = qs.length := by
    rw [sparseCoordinateRuns_coverage L 0 entries hr, hend, Nat.sub_zero]
  apply List.ext_getElem?
  intro x
  by_cases hx : x < qs.length
  · by_cases hm : ∃ q, (x, q) ∈ entries
    · obtain ⟨q, hq⟩ := hm
      have he := sparseCoordinateLookup_target L 0 entries hr x q hq
      simpa only [Nat.sub_zero, htarget x q hq] using he
    · have hoff : ∀ q, (x, q) ∉ entries := by simpa only [not_exists] using hm
      have he := sparseCoordinateLookup_gap L 0 entries hr x (by omega) (by omega) hoff
      rw [Nat.sub_zero, ← hgap x hx hoff] at he
      exact he
  · have hleft : ¬x < (SparseSelectorRun.expand (sparseCoordinateRuns 0 entries)).length := by omega
    simp [hx, hleft]

theorem sparseCoordinateRuns_reverse_eq (L : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (hr : SparseCoordinatesReady L 0 (sparseCoordinateValues entries))
    (qs : List (Fin (W + 1)))
    (hend : sparseCoordinateEnd 0 (sparseCoordinateValues entries) = qs.length)
    (htarget : ∀ x q, (x, q) ∈ entries → qs.reverse[x]? = some q)
    (hgap : ∀ x, x < qs.length → (∀ q, (x, q) ∉ entries) → qs.reverse[x]? = some 0) :
    SparseSelectorRun.expand (sparseCoordinateRuns 0 entries) = qs.reverse := by
  apply sparseCoordinateRuns_eq L entries hr qs.reverse
  · simpa using hend
  · exact htarget
  · intro x hx hoff; exact hgap x (by simpa using hx) hoff

end IntegerMultBounds.MathlibTM2.Routing
