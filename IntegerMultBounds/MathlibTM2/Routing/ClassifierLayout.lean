module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryTemporaryMask
public import IntegerMultBounds.MathlibTM2.Routing.BinaryPhaseMask

/-! The two classifier generators share dimensions, counters and scratch.
Their outputs and low-offset words are the only separate roles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def temporaryPhaseRole : TemporaryBlockReg → PhaseBlockReg
  | .width => .width
  | .run => .run
  | .bin => .bin
  | .high => .high
  | .dst => .dst
  | .work => .work
  | .scratch i => .scratch i

theorem temporaryPhaseRole_injective : Function.Injective temporaryPhaseRole := by
  intro r s he
  cases r <;> cases s <;> simp_all [temporaryPhaseRole]

theorem temporaryPhaseRole_ne_low (r : TemporaryBlockReg) : temporaryPhaseRole r ≠ .low := by
  cases r <;> simp [temporaryPhaseRole]

/-- The count and two archive tapes are shared; the fourth role is an output. -/
def classifierRepeatRole (phase : Bool) (i : Fin 4) : Fin 5 :=
  if i = 3 then (if phase then 4 else 3) else i.castSucc

theorem classifierRepeatRole_injective (phase : Bool) : Function.Injective (classifierRepeatRole phase) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> cases phase <;> simp_all [classifierRepeatRole]

@[simp] theorem classifierRepeatRole_zero (phase : Bool) : classifierRepeatRole phase 0 = 0 := by
  cases phase <;> rfl
@[simp] theorem classifierRepeatRole_one (phase : Bool) : classifierRepeatRole phase 1 = 1 := by
  cases phase <;> rfl
@[simp] theorem classifierRepeatRole_two (phase : Bool) : classifierRepeatRole phase 2 = 2 := by
  cases phase <;> rfl
@[simp] theorem classifierRepeatRole_three (phase : Bool) :
    classifierRepeatRole phase 3 = (if phase then 4 else 3) := by cases phase <;> rfl

theorem classifierRepeatRole_phase_ne_temporary (i : Fin 4) : classifierRepeatRole true i ≠ 3 := by
  fin_cases i <;> decide +kernel

/-- Low offsets differ by one, whereas the high-padding dimension is shared. -/
def classifierPadRole (phase : Bool) (i : Fin 2) : Fin 3 :=
  if i = 0 then (if phase then 1 else 0) else 2

theorem classifierPadRole_injective (phase : Bool) : Function.Injective (classifierPadRole phase) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> cases phase <;> simp_all [classifierPadRole]

@[simp] theorem classifierPadRole_zero (phase : Bool) :
    classifierPadRole phase 0 = (if phase then 1 else 0) := by cases phase <;> rfl
@[simp] theorem classifierPadRole_one (phase : Bool) : classifierPadRole phase 1 = 2 := by
  cases phase <;> rfl

end IntegerMultBounds.MathlibTM2.Routing
