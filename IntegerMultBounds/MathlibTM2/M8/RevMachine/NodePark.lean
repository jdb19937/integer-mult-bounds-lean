module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeRows
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallSemantics

/-!
# Parking the roles of a call

A block call on wire `w` parks every other wire on the payload stack, moves `w` to `io` and runs
the child on `io` (`RecursiveCallProtocol.payloadEntry`); recovery reverses it. Here the parking
order of a reversed network (`parked`): every wire but `w`, never `io`. After parking, the role
tapes are the child's: `io` holds the former tape of `w`, every other role tape is blank
(`entered_rolePart`). A child that ends with blank role tapes and its output on `io` is exactly
the parked bank of the parent with `w` replaced by that output (`entered_updated`), the input of
recovery.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.NodePark

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open RecursiveCallBank (role role_injective rolePart controlSlot layout)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRoleSerialization (roles)
open NodeBank (tapes io wireSlot wires)

variable (N : RevNetwork) {u : ℕ}

/-- The parking order of a call on wire `w`: every other wire. -/
def parked (w : N.World ⊕ N.Temp) : List (Fin (tapes N)) :=
  (List.finRange (tapes N)).filter fun i => i ≠ wireSlot N w ∧ i ≠ io N

theorem mem_parked (w : N.World ⊕ N.Temp) (i : Fin (tapes N)) :
    i ∈ parked N w ↔ i ≠ wireSlot N w ∧ i ≠ io N := by
  simp [parked]

theorem parked_nodup (w : N.World ⊕ N.Temp) : (parked N w).Nodup :=
  (List.nodup_finRange _).filter _

theorem active_not_parked (w : N.World ⊕ N.Temp) : wireSlot N w ∉ parked N w := by
  simp [mem_parked]

theorem io_not_parked (w : N.World ⊕ N.Temp) : io N ∉ parked N w := by
  simp [mem_parked]

theorem parked_length_le (w : N.World ⊕ N.Temp) : (parked N w).length ≤ tapes N :=
  (List.length_filter_le _ _).trans (by simp)

/-- The child's role tapes: one input on `io`, every other tape blank. -/
def childRoles (input : ℤ → Fin (prime+4)) : Tapes (tapes N) prime :=
  setTape (SharedBank.empty (tapes N) prime) (io N) input 0

theorem childRoles_unique (vv : Tapes (tapes N) prime) (input : ℤ → Fin (prime+4))
    (hw : ∀ i, i ≠ io N → vv.head i = 0 ∧ vv.tape i = fun _ => blank)
    (hi : vv.head (io N) = 0 ∧ vv.tape (io N) = input) : vv = childRoles N input := by
  have hp (k : Fin (tapes N)) : vv.head k = (childRoles N input).head k ∧
      vv.tape k = (childRoles N input).tape k := by
    by_cases hk : k = io N
    · subst hk; simpa [childRoles, setTape] using hi
    · simpa [childRoles, setTape, hk, SharedBank.empty] using hw k hk
  exact congrArg₂ Tapes.mk (funext fun k => (hp k).1) (funext fun k => (hp k).2)

/-- The row split's input is the child's role tapes. -/
theorem source_roles {v : Descriptor} (x : Fin (volume prime v) → Fin 4) :
    roles (RecursiveRowsSerialization.sourceData (wires N) x) =
      childRoles N (RecursiveShiftRoleBank.source x) := by
  apply childRoles_unique
  · intro i hi
    refine ⟨rfl, ?_⟩
    change RecursiveShiftRoleBank.source (RecursiveRowsSerialization.sourceData (wires N) x i) = _
    have hx : RecursiveRowsSerialization.sourceData (wires N) x i = fun _ => blank := by
      by_cases hsel : ∃ j, wires N j = i
      · obtain ⟨j, rfl⟩ := hsel
        change RecursiveRowsSerialization.putData _ _ _ = _
        rw [RecursiveRowsSerialization.putData_selected _ (NodeBank.wires_injective N)]
        induction j using Fin.addCases with
        | left j =>
          rw [show j = 0 from Subsingleton.elim _ _, NodeBank.wires_zero] at hi
          exact absurd rfl hi
        | right j => simp only [RecursiveRowsSerialization.sourceLocal, Fin.addCases_right]
      · exact RecursiveRowsSerialization.putData_unselected _ _ _ hsel
    rw [hx]
    exact RecursiveRowsSerialization.source_blank v
  · refine ⟨rfl, ?_⟩
    change RecursiveShiftRoleBank.source (RecursiveRowsSerialization.sourceData (wires N) x (io N)) = _
    congr 1
    change RecursiveRowsSerialization.putData _ _ _ = _
    rw [← NodeBank.wires_zero N, RecursiveRowsSerialization.putData_selected _ (NodeBank.wires_injective N)]
    simp only [RecursiveRowsSerialization.sourceLocal, Fin.addCases_left]

/-! ### The parked bank -/

theorem entered_io (w : N.World ⊕ N.Temp) (n : ℕ) (v : Tapes (RecursiveCallBank.TapeCount (tapes N) u) prime) :
    (RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n v).head (role (u := u) (io N)).val = 0 ∧
      (RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n v).tape (role (u := u) (io N)).val =
        v.tape (role (wireSlot N w)).val := by
  have hs := RoleArrayFrames.saved_frame layout ((parked N w).map role) n v
    (role (u := u) (wireSlot N w)).val (role (wireSlot N w)).property.1 (by
      intro k hk he
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
      exact active_not_parked N w (role_injective (Subtype.ext he) ▸ hj))
  refine ⟨?_, ?_⟩
  · simp only [RecursiveCallProtocol.entered, RoleArrayCall.entered, RoleArrayMove.moved, RoleArrayCall.slots,
      Matrix.cons_val_zero, Matrix.cons_val_one, setTape, Function.update_self]
  · simp only [RecursiveCallProtocol.entered, RoleArrayCall.entered, RoleArrayMove.moved, RoleArrayCall.slots,
      Matrix.cons_val_zero, Matrix.cons_val_one, setTape, Function.update_self]
    exact hs.2

theorem entered_blank (w : N.World ⊕ N.Temp) (n : ℕ) (v : Tapes (RecursiveCallBank.TapeCount (tapes N) u) prime)
    (k : Fin (tapes N)) (hk : k ≠ io N) :
    (RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n v).head (role (u := u) k).val = 0 ∧
      (RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n v).tape (role (u := u) k).val =
        fun _ => blank := by
  have hio : (role (u := u) k).val ≠ (role (io N)).val := fun he => hk (role_injective (Subtype.ext he))
  by_cases hkw : k = wireSlot N w
  · subst hkw
    simp only [RecursiveCallProtocol.entered, RoleArrayCall.entered, RoleArrayMove.moved, RoleArrayCall.slots,
      Matrix.cons_val_zero, Matrix.cons_val_one, setTape, Function.update_of_ne hio, Function.update_self]
    constructor <;> trivial
  · have hkw' : (role (u := u) k).val ≠ (role (wireSlot N w)).val := fun he =>
      hkw (role_injective (Subtype.ext he))
    have hm : role (u := u) k ∈ (parked N w).map role :=
      List.mem_map.mpr ⟨_, (mem_parked N w k).mpr ⟨hkw, hk⟩, rfl⟩
    have hh := RoleArrayFrames.saved_role layout ((parked N w).map role)
      ((parked_nodup N w).map (role_injective (u := u))) n v (role k) hm
    simp only [RecursiveCallProtocol.entered, RoleArrayCall.entered, RoleArrayMove.moved, RoleArrayCall.slots,
      Matrix.cons_val_zero, Matrix.cons_val_one, setTape, Function.update_of_ne hkw', Function.update_of_ne hio]
    exact hh

/-- After parking, the role tapes are the child's. -/
theorem entered_rolePart (w : N.World ⊕ N.Temp) (n : ℕ) (v : Tapes (RecursiveCallBank.TapeCount (tapes N) u) prime) :
    rolePart (RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n v) =
      childRoles N (v.tape (role (u := u) (wireSlot N w)).val) :=
  childRoles_unique N _ _ (fun k hk => entered_blank N w n v k hk) (entered_io N w n v)

/-- Replacing a role tape of the call bank. -/
theorem bank_setTape (rr : Tapes (tapes N) prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) (k : Fin (tapes N)) (out : ℤ → Fin (prime+4)) :
    RecursiveCallBank.bank (setTape rr k out 0) hs f p aux st =
      setTape (RecursiveCallBank.bank rr hs f p aux st) (role (u := u) k).val out 0 := by
  apply congrArg₂ Tapes.mk <;> funext j <;> induction j using Fin.addCases with
  | left j =>
    by_cases hj : j = k
    · subst hj; simp [RecursiveCallBank.bank, RecursiveShiftRoleBank.common, Tapes.append, setTape, role]
    · have hj' : Fin.castAdd (7 + ((3+u)+2)) j ≠ (role (u := u) k).val := fun he =>
        hj (Fin.castAdd_injective _ _ he)
      simp [RecursiveCallBank.bank, RecursiveShiftRoleBank.common, Tapes.append, setTape,
        Function.update_of_ne hj, Function.update_of_ne hj']
  | right j =>
    have hj' : Fin.natAdd (tapes N) j ≠ (role (u := u) k).val := by
      intro he; have := congrArg Fin.val he; simp [role] at this; omega
    simp [RecursiveCallBank.bank, RecursiveShiftRoleBank.common, Tapes.append, setTape, Function.update_of_ne hj']

/-- The parked bank of a parent whose wire `w` holds `out` is the parked bank with `out` on `io`. -/
theorem entered_updated (w : N.World ⊕ N.Temp) (n : ℕ) (rr : Tapes (tapes N) prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime) (out : ℤ → Fin (prime+4)) :
    RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n
      (RecursiveCallBank.bank (setTape rr (wireSlot N w) out 0) hs f p aux st) =
    setTape (RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n
      (RecursiveCallBank.bank rr hs f p aux st)) (role (u := u) (io N)).val out 0 := by
  rw [bank_setTape]
  apply M8.Machine.CallSemantics.entered_setTape
  · exact role_injective.ne (NodeBank.wireSlot_ne_io N w)
  · intro h
    obtain ⟨k, hk, he⟩ := List.mem_map.mp h
    exact active_not_parked N w (role_injective he ▸ hk)

/-- The parked bank is the common bank with the child's role tapes. -/
theorem entered_eq (w : N.World ⊕ N.Temp) (n : ℕ) (rr : Tapes (tapes N) prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime) :
    RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n (RecursiveCallBank.bank rr hs f p aux st) =
      RecursiveCallBank.bank (childRoles N (rr.tape (wireSlot N w))) hs
        ((RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n
          (RecursiveCallBank.bank rr hs f p aux st)).tape (controlSlot 2))
        ((RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n
          (RecursiveCallBank.bank rr hs f p aux st)).head (controlSlot 2)) aux st := by
  set E := RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n (RecursiveCallBank.bank rr hs f p aux st)
  have h : E = RecursiveCallBank.bank (rolePart E) hs (E.tape (controlSlot 2)) (E.head (controlSlot 2)) aux st :=
    RecursiveCallBank.entered_bank (parked N w) (wireSlot N w) (io N) n rr hs f p aux st
  have hr := entered_rolePart N (u := u) w n (RecursiveCallBank.bank rr hs f p aux st)
  have ht : (RecursiveCallBank.bank rr hs f p aux st).tape (role (u := u) (wireSlot N w)).val = rr.tape (wireSlot N w) := by
    simp [RecursiveCallBank.bank, RecursiveShiftRoleBank.common, Tapes.append, role]
  rw [ht] at hr
  rw [hr] at h
  exact h

theorem roles_supported {v : Descriptor} (data : RecursiveMixedSchedule.Data (tapes N) v) (k : Fin (tapes N)) :
    (roles data).head k = 0 ∧ RoleArrayStack.Supported ((roles data).tape k) (volume prime v) := by
  constructor
  · rfl
  · change RoleArrayStack.Supported (RecursiveShiftRoleBank.source (data k)) _
    rw [RecursiveRoleSerialization.source_eq_word]
    exact RoleArrayStack.supported_word _ _ (by simp [List.length_ofFn])

/-- The payload stack keeps a blank suffix above its new head. -/
theorem entered_blank_suffix (w : N.World ⊕ N.Temp) (n : ℕ) (rr : Tapes (tapes N) prime)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) (hf : ∀ z, p ≤ z → f z = blank) :
    let mid := RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n (RecursiveCallBank.bank rr hs f p aux st)
    ∀ z, mid.head (controlSlot 2) ≤ z → mid.tape (controlSlot 2) z = blank := by
  apply M8.Machine.CallSemantics.entered_blank_suffix layout ((parked N w).map role) (role (wireSlot N w)) (role (io N)) n _
  simpa only [layout, (RecursiveCallBank.payload_stack rr hs f p aux st).1,
    (RecursiveCallBank.payload_stack rr hs f p aux st).2] using hf

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.NodePark
