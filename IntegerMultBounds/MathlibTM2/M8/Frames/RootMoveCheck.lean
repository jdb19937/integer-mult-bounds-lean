module

public import IntegerMultBounds.MathlibTM2.M8.Frames.RootBankCheck

/-! The integer rank drops along a chain of root complements. Equal-rank
steps are free; all other steps contribute one child of their rank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames.RootBank

def rankSteps (bank : Nat → Record) : List Nat → List Nat
  | [] => []
  | [_] => []
  | i :: j :: ids =>
      let rank := (bank i).basis.length - (bank j).basis.length
      if rank = 0 then rankSteps bank (j :: ids) else rank :: rankSteps bank (j :: ids)

end IntegerMultBounds.MathlibTM2.M8.Frames.RootBank
