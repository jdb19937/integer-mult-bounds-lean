module

public import IntegerMultBounds.Machine.ActivePrefixStageRuntimeCoordinates
import Mathlib.Tactic.Positivity.Finset

/-! The complete active word is recoverable from the original serialized
ordinal, independently of the source/target dependent address decomposition. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeOrdinal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixStageRuntimeWord (word word_length)
open BinaryAddressTableData (row row_length row_rank)
open ActivePrefixDirtyControlGlobalSwap (index)
variable {s : Shape}

def front (d : Inputs s) (i : Address d) : ℕ :=
  (((((i.row.val*2^((geometry d).n*(geometry d).b)+i.u.val)*
    2^(s.H-(geometry d).n*(geometry d).b)+i.uTail.val)*2^((geometry d).n*(geometry d).b)+i.t.val)*
    2^(s.H-(geometry d).n*(geometry d).b)+i.tTail.val)*2^s.F+i.frontSlack.val)

theorem word_value (d : Inputs s) (i : Address d) : Counter.value (word d i)=
    (i.activeBefore.val*2^((geometry d).n*(geometry d).q)+i.target.val)*2^(geometry d).after+i.activeAfter.val := by
  simp only [word,ColumnTransducer.value_append,List.length_append,row_length,
    row_rank _ _ i.activeBefore.isLt,row_rank _ _ i.target.isLt,row_rank _ _ i.activeAfter.isLt,pow_add]
  ring

theorem index_factored (d : Inputs s) (i : Address d) :
    (index s (geometry d) i).val=
      ((front d i*2^(s.active*s.chunk)+Counter.value (word d i))*2^(s.H+s.B)+i.back.val)*s.payload+i.payload.val := by
  rw [ActivePrefixDirtyControlGlobalSwap.index,CompactActiveTargetLayout.index_val,word_value]
  have hs := (geometry d).activeSize
  rw [←hs]
  simp only [front,pow_add]
  ring

theorem quotient (a b c : ℕ) (hc : 0<c) (hb : b<c) : (a*c+b)/c=a := by
  rw [Nat.mul_comm a c,Nat.mul_add_div hc,Nat.div_eq_of_lt hb,Nat.add_zero]

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeOrdinal
