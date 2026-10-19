module

public import IntegerMultBounds.Machine.CountedPackedParityRun
public import IntegerMultBounds.Compact.PackedArithValue

/-! The physically extracted dirty-control bits are exactly the parities of
the base-two-power digits in the compact later-source arithmetic specification.
This connects literal control tapes to packedLate without an oracle input. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CountedPackedParityValue
noncomputable section
open Compact Compact.PowerTwo Compact.Radix

/-- Low bits physically read from equally wide blocks are the digit parities. -/
theorem controls_eq_digit_parities (b : ℕ) (hb : 1 ≤ b) (U : List Bool) (n : ℕ)
    (hU : U.length = n*b) :
    (CountedPackedParityRun.parities b U n).map ctrl =
      (digits ((2 : ℤ)^b) n (Counter.value U)).map (· % 2) := by
  rw [digits_blocks U b n hU]
  simp only [CountedPackedParityRun.parities, blockValues, List.map_map]
  apply List.map_congr_left
  intro i _
  have h := value_field_one U (i*b) b hb
  simp only [Gather.field, List.range_one, List.map_cons, List.map_nil,
    add_zero, Counter.value] at h
  cases U.getD (i*b) false <;> simpa [ctrl, Gather.field] using h

end
end IntegerMultBounds.Machine.CountedPackedParityValue
