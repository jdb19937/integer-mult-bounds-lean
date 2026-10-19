module

public import IntegerMultBounds.Machine.CompactRowReservationPlacement

/-! Literal padded role arrays, retaining every within-record binary coordinate. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactRowReservationData
noncomputable section
variable {a c r l : ℕ}
open IntegerMultBounds.Compact.Layout (paddedRows)
open RecursiveInterchangeLayout (volume)
open CompactRowHeaders (descriptor)

def original (x : Fin (1*r*l) → Bool) : ℤ → Fin (a+4) :=
  putWord (fun _ => blank) 0 (List.ofFn (fun i => bitSymbol (x i)))

def padded (x : Fin (1*r*l) → Bool) : Fin (volume a (descriptor (paddedRows r c) l)) → Fin (a+4) :=
  fun i => RecursiveRowPadding.pad (paddedRows r c) (bitSymbol false) (fun i => bitSymbol (x i))
    (Fin.cast (by simp [volume,descriptor]) i)

theorem padded_word (x : Fin (1*r*l) → Bool) :
    RecursiveRowsConstruct.word (padded (a := a) (c := c) x) =
      putWord (fun _ => blank) 0
        (List.ofFn (RecursiveRowPadding.pad (paddedRows r c) (bitSymbol false) (fun i => bitSymbol (x i)))) := by
  unfold RecursiveRowsConstruct.word
  congr 1
  have hdim : volume a (descriptor (paddedRows r c) l) = 1*paddedRows r c*l := by simp [volume,descriptor]
  apply (List.ofFn_congr hdim (padded (a := a) (c := c) x)).trans
  apply congrArg List.ofFn
  funext i
  unfold padded
  exact congrArg _ (Fin.ext rfl)

def outputPayload (hc : 0 < c) (x : Fin (1*r*l) → Bool) : Tapes (1+c) a :=
  RecursiveRowsMove.rolePayload (CompactRowPaddingRound.padded_bounds r c hc).2.2
    (padded (c := c) x)

end
end IntegerMultBounds.Machine.CompactRowReservationData
