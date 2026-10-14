module

public import IntegerMultBounds.Machine.ChirpNativeTruncate

/-! Two native truncation placements on the shared complex-arithmetic bank.
Original four operand tapes stay outside both calls. The first call retains
the imaginary numerator; the second retains the rounded real result. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpRoundCalls
noncomputable section

abbrev tapeCount := 98

def resultSlot (field : Fin 2) : Fin tapeCount := if field=0 then 14 else 15
def sourceSlot (field : Fin 2) : Fin tapeCount := if field=0 then 4 else 9

def slots (field : Fin 2) (slot : Fin 93) : Fin tapeCount :=
  if slot.val=4 then 84
  else if slot.val=9 then 86
  else if slot.val=14 then 95
  else if slot.val=15 then (if field=0 then 15 else 4)
  else if slot.val=84 then 97
  else if slot.val=86 then 96
  else if slot.val=91 then resultSlot field
  else if slot.val=92 then sourceSlot field
  else ⟨slot.val,by change slot.val<98; omega⟩

theorem slots_injective (field : Fin 2) : Function.Injective (slots field) := by
  fin_cases field <;> decide

def placement (field : Fin 2) := InjectivePlacement.placement (slots field) (slots_injective field) (by decide : 93+5=98)
def call (field : Fin 2) := Placement.placed ChirpNativeTruncate.program (placement field)

end
end IntegerMultBounds.Machine.ChirpRoundCalls
