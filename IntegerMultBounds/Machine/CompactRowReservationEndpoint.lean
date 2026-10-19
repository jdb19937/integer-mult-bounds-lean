module

public import IntegerMultBounds.Machine.CompactRowReservationBudget

/-! Literal cells of the complete reservation-layout endpoint. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactRowReservationEndpoint
noncomputable section
variable {a c r l : ℕ}
open CompactRowReservationPlacement (NativeTapes CommonTapes bank common base roles)
open CompactRowReservationData (padded outputPayload)

def final (hc : 0 < c) (x : Fin (1*r*l) → Bool) (rs ls : List Bool) :=
  bank (fun _ => blank) (outputPayload (a := a) hc x) rs ls none none

/-- Exact original row/width header words and their original heads. -/
theorem original_headers (hc : 0 < c) (x : Fin (1*r*l) → Bool) (rs ls : List Bool) :
    (final (a := a) hc x rs ls).head (Fin.castAdd (NativeTapes c) (Fin.castAdd c (2 : Fin 25))) = 1 ∧
    (final (a := a) hc x rs ls).tape (Fin.castAdd (NativeTapes c) (Fin.castAdd c (2 : Fin 25))) = RadixZeroFill.encodedBinary rs ∧
    (final (a := a) hc x rs ls).head (Fin.castAdd (NativeTapes c) (Fin.castAdd c (3 : Fin 25))) = 1 ∧
    (final (a := a) hc x rs ls).tape (Fin.castAdd (NativeTapes c) (Fin.castAdd c (3 : Fin 25))) = RadixZeroFill.encodedBinary ls := by
  simp [final,bank,CleanSubbank.bank,common,base,SharedPlacementAlphabet.setTape,
    Tapes.append,CompactRowPaddingRun.bank]

/-- Literal complete padded role streams, with no free payload permutation. -/
theorem role_word (hc : 0 < c) (x : Fin (1*r*l) → Bool) (rs ls : List Bool) (j : Fin c) :
    (final (a := a) hc x rs ls).head (Fin.castAdd (NativeTapes c) (Fin.natAdd 25 j)) = 0 ∧
    (final (a := a) hc x rs ls).tape (Fin.castAdd (NativeTapes c) (Fin.natAdd 25 j)) =
      RecursiveRowsConstruct.word (RecursiveInterchangeRows.roleArray a c
        (CompactRowHeaders.descriptor (IntegerMultBounds.Compact.Layout.paddedRows r c) l)
        (CompactRowPaddingRound.padded_bounds r c hc).2.2 (padded (c := c) x) j) := by
  simp [final,bank,CleanSubbank.bank,common,roles,outputPayload,RecursiveRowsMove.rolePayload,
    CyclicRowCopy.payload,Tapes.append]

end
end IntegerMultBounds.Machine.CompactRowReservationEndpoint
