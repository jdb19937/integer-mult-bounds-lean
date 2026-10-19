module

public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeTransport
public import IntegerMultBounds.Machine.RecursiveRowsNode
public import IntegerMultBounds.Machine.Shared50RecursiveNodeRows

/-!
# The node layout

A node splits its input rows over the contract roles only (`wires`): the input/output tape and
the contract-role tapes take part in the split and the merge, the temporary tapes do not. Split
and merge are the generic row machines (`entry`, `exit`), with the merge routed by the network's
route (`mergeRoute`).

The temporaries are machine-private zero rows. After the split their tapes are blank;
`tempInit` fills each with the zero bit, and before the merge `tempClear` makes each blank again
(`run_tempOps`). Both read the input/output tape only as a source slot of the role volume.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

variable [Net]

namespace NodeLayout

/-- The tape of a contract role. -/
def world (i : World) : Fin payloadCount := wireSlot (.inl i)

/-- The split and merge slots: the input/output tape, then the contract roles in their
enumeration. -/
def wires : Fin (1 + roleCount) → Fin payloadCount :=
  Fin.addCases (fun _ => io) (fun j => world ((Net.net).roleEquiv j))

@[simp] theorem wires_role (j : Fin roleCount) : wires (Fin.natAdd 1 j) = world ((Net.net).roleEquiv j) := by
  simp only [wires, Fin.addCases_right]

theorem wires_io : wires (Fin.castAdd roleCount (0 : Fin 1)) = io := by
  simp only [wires, Fin.addCases_left]

theorem wires_injective : Function.Injective wires := by
  intro i j he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => congr 1; exact Subsingleton.elim _ _
    | right j =>
      simp only [wires, Fin.addCases_left, Fin.addCases_right] at he
      exact absurd he.symm (wireSlot_ne_io _)
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [wires, Fin.addCases_left, Fin.addCases_right] at he
      exact absurd he (wireSlot_ne_io _)
    | right j =>
      simp only [wires, Fin.addCases_right, world] at he
      have h := wireSlot_injective he
      simp only [Sum.inl.injEq] at h
      exact congrArg (Fin.natAdd 1) ((Net.net).roleEquiv.injective h)

/-- The network's route as a permutation of the contract roles. -/
def routeEquiv : Equiv.Perm World :=
  ⟨(Net.net).route, (Net.net).route, (Net.net).route_involutive, (Net.net).route_involutive⟩

/-- The merge source permutation in the role enumeration. -/
def mergeRoute : Equiv.Perm (Fin roleCount) :=
  (Net.net).roleEquiv.trans (routeEquiv.trans (Net.net).roleEquiv.symm)

@[simp] theorem mergeRoute_symm (i : Fin roleCount) :
    mergeRoute.symm i = (Net.net).roleEquiv.symm ((Net.net).route ((Net.net).roleEquiv i)) := rfl

def entry {u : ℕ} := RecursiveRowsNode.entry (u := u) wires wires_injective
def exit {u : ℕ} := RecursiveRowsNode.exit (u := u) mergeRoute wires wires_injective

/-! ### Temporaries -/

/-- The tape of a temporary. -/
def tempSlot (k : Fin tempCount) : Fin payloadCount := wireSlot (.inr ((Net.net).tempEquiv k))

theorem tempSlot_ne_io (k : Fin tempCount) : io ≠ tempSlot k := (wireSlot_ne_io _).symm

/-- Fill every temporary tape with the symbol `s`, reading the input/output tape. -/
def tempOps (s : Fin 4) : List (RoleOps.Op payloadCount) :=
  (List.finRange tempCount).map fun k => .fill ⟨io, tempSlot k, tempSlot_ne_io k⟩ s

def tempInit {u : ℕ} := RoleOpsBank.machine (u := u) (tempOps (SparseRoleCircuit.encode (a := 0) 0))
def tempClear {u : ℕ} := RoleOpsBank.machine (u := u) (tempOps blank)

/-- Is a slot a temporary tape. -/
def IsTemp (i : Fin payloadCount) : Prop := ∃ k, tempSlot k = i

theorem run_fills {v : Descriptor} (ks : List (Fin tempCount)) (s : Fin 4)
    (data : RecursiveMixedSchedule.Data payloadCount v) (i : Fin payloadCount) :
    RoleOps.run (ks.map fun k => RoleOps.Op.fill ⟨io, tempSlot k, tempSlot_ne_io k⟩ s) data i =
      if ∃ k ∈ ks, tempSlot k = i then fun _ => s else data i := by
  induction ks generalizing data with
  | nil => simp [RoleOps.run]
  | cons k ks ih =>
    change RoleOps.run (ks.map _) (RoleOps.transform _ data) i = _
    rw [ih]
    simp only [RoleOps.transform, List.mem_cons, exists_eq_or_imp]
    by_cases hk : tempSlot k = i
    · subst hk; simp
    · simp only [hk, false_or]
      split_ifs <;> simp [Function.update_of_ne (Ne.symm hk)]

/-- The temporary fills set every temporary tape to `s` and keep every other tape. -/
theorem run_tempOps {v : Descriptor} (s : Fin 4) (data : RecursiveMixedSchedule.Data payloadCount v)
    (i : Fin payloadCount) [Decidable (IsTemp i)] :
    RoleOps.run (tempOps s) data i = if IsTemp i then fun _ => s else data i := by
  rw [tempOps, run_fills]
  simp only [List.mem_finRange, true_and, IsTemp]
  congr 1

end NodeLayout

end
end IntegerMultBounds.MathlibTM2.M8.Machine
