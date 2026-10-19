module

public import IntegerMultBounds.Machine.CompactGlobalRowPadding
public import IntegerMultBounds.Machine.CompactGadgetReservationShape

/-! Original global parameters determine the complete reserved layout. Rows
use only the original first q0 axes; all three compact fields, unused bits,
active axes and payload remain in every row and hence in every role. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactGlobalReservation
open CompactGlobalRowPadding
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape

def reservedAxes (c m d G K : ℕ) := rowAxes c m d+frontChunks d G K+backChunks d G K

def shape (c m d D G K payload : ℕ) : Shape where
  axes := d
  guard := G
  chunk := K
  active := D-reservedAxes c m d G K
  payload := payload

theorem original_axes (c m d D G K : ℕ) (hD : reservedAxes c m d G K ≤ D) :
    rowAxes c m d+frontChunks d G K+(D-reservedAxes c m d G K)+backChunks d G K = D :=
  axes_exact D (rowAxes c m d) d G K hD

theorem original_bits (c m d D G K payload : ℕ) (hK : 0 < K)
    (hD : reservedAxes c m d G K ≤ D) :
    rowAxes c m d*K+(shape c m d D G K payload).bits = D*K := by
  rw [Shape.existing_bits _ hK]
  have he := original_axes c m d D G K hD
  simp only [shape]
  nlinarith

/-- The entire original address volume is retained by the row reinterpretation. -/
theorem original_volume (c m d D G K payload : ℕ) (hK : 0 < K)
    (hD : reservedAxes c m d G K ≤ D) :
    originalRows c m d K*(shape c m d D G K payload).recordWidth = 2^(D*K)*payload := by
  simp only [originalRows,Shape.recordWidth,shape]
  rw [← Nat.mul_assoc,← pow_add]
  exact congrArg (fun b => 2^b*payload) (original_bits c m d D G K payload hK hD)

end IntegerMultBounds.Machine.CompactGlobalReservation
