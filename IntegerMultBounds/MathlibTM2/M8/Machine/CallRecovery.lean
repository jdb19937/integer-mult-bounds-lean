module

public import IntegerMultBounds.MathlibTM2.M8.Machine.CallSemantics
public import IntegerMultBounds.Machine.RecursiveRowsSerialization

/-! Actual counted recovery after a child has transformed its I/O word. The
child result is moved back to the active Wire role and all parked arrays,
stack cells and controls are physically restored. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.CallRecovery
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CallLayout
open CallSemantics
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveMixedSchedule (Data)
open RecursiveRoleSerialization (roles)
open RecursiveCallBank
open SharedBankStageInput (raw)
open SharedPlacementAlphabet (setTape)
variable {u : ℕ} {v : Descriptor}

theorem roles_update (data : Data payloadCount v) (k : Fin payloadCount) (out : Fin (volume prime v) → Fin 4) :
    roles (Function.update data k out) = setTape (roles data) k (RecursiveShiftRoleBank.source out) 0 := by
  apply congrArg₂ Tapes.mk <;> funext j <;> by_cases hj : j = k
  · subst j; simp only [roles,Function.update_self]
  · simp only [roles,Function.update_of_ne hj]
  · subst j; simp only [roles,Function.update_self]
  · simp only [roles,Function.update_of_ne hj]

/-- Exact updated-parent entry endpoint in the canonical array serialization. -/
theorem entered_data_updated (w : Wire) (data : Data payloadCount v)
    (out : Fin (volume prime v) → Fin 4) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime) :
    RecursiveCallProtocol.entered (parked w) (wireSlot w) io (volume prime v)
      (bank (roles (Function.update data (wireSlot w) out)) hs f p aux st) =
    setTape (RecursiveCallProtocol.entered (parked w) (wireSlot w) io (volume prime v)
      (bank (roles data) hs f p aux st)) (role (u := u) io).val (RecursiveShiftRoleBank.source out) 0 :=
  (congrArg (fun rr => RecursiveCallProtocol.entered (parked w) (wireSlot w) io (volume prime v)
    (bank rr hs f p aux st)) (roles_update data (wireSlot w) out)).trans
      (entered_bank_updated w (volume prime v) (roles data) hs f p aux st (RecursiveShiftRoleBank.source out))

/-- Actual count generation, move-back, reverse parking and count erasure.
Its input is the existing entered bank with exactly the returned child word;
its output is the parent data with exactly one updated Wire stream. -/
theorem recovers (w : Wire) (data : Data payloadCount v)
    (out : Fin (volume prime v) → Fin 4) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (hf : ∀ z, p ≤ z → f z = blank) (hio : data io = fun _ => blank) :
    HoareTime (RecursiveCallProtocol.recover (u := u) (parked w) (wireSlot w) io (active_ne_io w)).program
      (fun ww => ww = raw (setTape
        (RecursiveCallProtocol.entered (parked w) (wireSlot w) io (volume prime v)
          (bank (roles data) hs f p aux st)) (role (u := u) io).val (RecursiveShiftRoleBank.source out) 0)
        (RecursiveCallProtocol.recover (u := u) (parked w) (wireSlot w) io (active_ne_io w)).tapes)
      (fun ww => ww = raw (bank (roles (Function.update data (wireSlot w) out)) hs f p aux st)
        (RecursiveCallProtocol.recover (u := u) (parked w) (wireSlot w) io (active_ne_io w)).tapes)
      ((92*(parked w).length+51883)*volume prime v) := by
  have hh := RecursiveCallProtocol.recovers (parked w) (parked_nodup w) (wireSlot w) io
    (active_ne_io w) (active_not_parked w) (io_not_parked w) v
    (roles (Function.update data (wireSlot w) out)) hs f p aux st hv hp
    (fun k _ => roles_supported _ k) (fun z hz _ => hf z hz)
    (roles_supported _ _) (by
      constructor
      · rfl
      · change RecursiveShiftRoleBank.source ((Function.update data (wireSlot w) out) io) = _
        rw [Function.update_of_ne ((wireSlot_ne_io w).symm),hio]
        exact RecursiveRowsSerialization.source_blank v)
  apply hh.consequence _ (fun _ h => h) le_rfl
  intro ww hww
  exact hww.trans (congrArg (fun vv => raw vv
    (RecursiveCallProtocol.recover (u := u) (parked w) (wireSlot w) io (active_ne_io w)).tapes)
      (entered_data_updated w data out hs f p aux st).symm)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.CallRecovery
