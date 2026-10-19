module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ChildPermutation
public import IntegerMultBounds.Machine.Shared50RecursiveBank

/-!
# Node blocks on the permanent recursive bank

The node's blocks run on the same permanent bank as the recursive calls
(`Shared50RecursiveBank.bank`, which is generic in the role count), as
`Shared50RecursiveBankNodes` places the Shared50 blocks: the split and merge (`entry`, `exit`),
the temporaries' fills (`tempInit`, `tempClear`), and every segment, gate and reset. The node
frame and the scalar-view frame occupy different physical tapes.

`parked w` is the fixed parking order of a call on wire `w`: every other wire tape, in the wire
enumeration, never the input/output tape (`mem_parked`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open Shared50RecursiveBank
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewedAction (Data)
open RecursiveRoleSerialization (roles)

variable [Net] {u b : ℕ} {v : Descriptor}

namespace BankNodes

def entry := adapt (NodeLayout.entry (u := AuxCount u - 1)) (commonRename (t := payloadCount) nodeSlot)
def exit := adapt (NodeLayout.exit (u := AuxCount u - 1)) (commonRename (t := payloadCount) nodeSlot)
def tempInit := adapt (NodeLayout.tempInit (u := AuxCount u - 1)) (commonRename (t := payloadCount) nodeSlot)
def tempClear := adapt (NodeLayout.tempClear (u := AuxCount u - 1)) (commonRename (t := payloadCount) nodeSlot)
def segment (seg : Segment) :=
  adapt (seg.machine (u := AuxCount u - 1)) (commonRename (t := payloadCount) scalarSlot)
def gate (g : Gate) := adapt (g.machine (u := AuxCount u - 1)) (commonRename (t := payloadCount) nodeSlot)
def reset (r : Reset) := adapt (r.machine (u := AuxCount u - 1)) (commonRename (t := payloadCount) nodeSlot)

theorem entry_hoare (hs : Fin 6 → List Bool) (node scalar : Tapes 1 prime)
    (f : ℤ → Fin (prime + 4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (v : Descriptor) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → Fin 4) :
    ∃ rs : List Bool, RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.role v roleCount)
      (RecursiveRowsNodeHeaders.headers hs rs) ∧
      HoareTime (entry (u := u)).program
        (fun w => w = raw (bank (roles (RecursiveRowsSerialization.sourceData NodeLayout.wires x))
          hs f p node scalar aux st) (entry (u := u)).tapes)
        (fun w => w = raw (bank (roles (RecursiveRowsSerialization.roleData NodeLayout.wires (Equiv.refl _) hd x))
          (RecursiveRowsNodeHeaders.headers hs rs) f p (RecursiveViewFrame.savedStack hs node) scalar aux st)
          (entry (u := u)).tapes)
        (RecursiveViewFrame.pushCost hs + RecursiveRowsClean.bound roleCount (volume prime v) +
          RecursiveRowsNodeRoleBank.constant roleCount * volume prime v + 2) := by
  obtain ⟨rs, hh, h⟩ := RecursiveRowsNode.entry_hoare NodeLayout.wires NodeLayout.wires_injective hs node
    (rest nodeSlot (auxiliary f p node scalar aux st)) v roleCount_pos hv hp hd x
  have h' := adapt_realizes _ (commonRename nodeSlot) _ _ _ h
  rw [node_endpoint] at h'
  rw [rest_node f p node (RecursiveViewFrame.savedStack hs node) scalar aux st, node_endpoint] at h'
  exact ⟨rs, hh, h'⟩

theorem exit_hoare (old hs : Fin 6 → List Bool) (node scalar : Tapes 1 prime)
    (f : ℤ → Fin (prime + 4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (hf : RecursiveViewFrame.Free old node) (v : Descriptor)
    (hv : RecursiveDimensionBank.Headers v old) (hp : v.Positive) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → Fin 4) :
    HoareTime (exit (u := u)).program
      (fun w => w = raw (bank (roles (RecursiveRowsSerialization.roleData NodeLayout.wires NodeLayout.mergeRoute hd x))
        hs f p (RecursiveViewFrame.savedStack old node) scalar aux st) (exit (u := u)).tapes)
      (fun w => w = raw (bank (roles (RecursiveRowsSerialization.sourceData NodeLayout.wires x))
        old f p node scalar aux st) (exit (u := u)).tapes)
      (RecursiveViewFrame.restoreCost old hs + RecursiveRowsClean.bound roleCount (volume prime v) + 1) := by
  have h := RecursiveRowsNode.exit_hoare NodeLayout.mergeRoute NodeLayout.wires NodeLayout.wires_injective
    old hs node (rest nodeSlot (auxiliary f p node scalar aux st)) hf v roleCount_pos hv hp hd x
  have h' := adapt_realizes _ (commonRename nodeSlot) _ _ _ h
  rw [node_endpoint] at h'
  rw [rest_node f p node (RecursiveViewFrame.savedStack old node) scalar aux st, node_endpoint] at h'
  exact h'

/-- A role-operation block on the node frame. -/
theorem ops_hoare (ops : List (RoleOps.Op payloadCount)) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime + 4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) (data : Data payloadCount v) :
    HoareTime (adapt (RoleOpsBank.machine (u := AuxCount u - 1) ops) (commonRename (t := payloadCount) nodeSlot)).program
      (fun w => w = raw (bank (roles data) hs f p node scalar aux st)
        (adapt (RoleOpsBank.machine (u := AuxCount u - 1) ops) (commonRename (t := payloadCount) nodeSlot)).tapes)
      (fun w => w = raw (bank (roles (RoleOps.run ops data)) hs f p node scalar aux st)
        (adapt (RoleOpsBank.machine (u := AuxCount u - 1) ops) (commonRename (t := payloadCount) nodeSlot)).tapes)
      (RoleOpsClean.coefficient ops * volume prime v) := by
  have h := RoleOpsBank.realizes ops hs node (rest nodeSlot (auxiliary f p node scalar aux st)) hv hp data
  have h' := adapt_realizes _ (commonRename nodeSlot) _ _ _ h
  simp only [node_endpoint] at h'
  exact h'

theorem segment_hoare (seg : Segment) (hw : v.width = width * b)
    (hp : v.Positive) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime + 4)) (p : ℤ) (node : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) (data : Data payloadCount v) :
    HoareTime (segment (u := u) seg).program
      (fun w => w = raw (bank (roles data) hs f p node (SharedBank.empty 1 prime) aux st) (segment (u := u) seg).tapes)
      (fun w => w = raw (bank (roles (seg.array hw data)) hs f p node
        (SharedBank.empty 1 prime) aux st) (segment (u := u) seg).tapes)
      (seg.coefficient * volume prime v) := by
  have h := seg.realizesNode hw hp hs hv
    (rest scalarSlot (auxiliary f p node (SharedBank.empty 1 prime) aux st)) data
  have h' := adapt_realizes _ (commonRename scalarSlot) _ _ _ h
  simp only [scalar_endpoint] at h'
  exact h'

end BankNodes

/-! ### Parking for calls -/

namespace CallLayout

/-- Every other wire tape, in the wire enumeration. -/
def parked (w : Wire) : List (Fin payloadCount) :=
  ((List.finRange wireCount).filter (fun i => i ≠ wireEquiv.symm w)).map (Fin.castAdd 1)

theorem parked_nodup (w : Wire) : (parked w).Nodup :=
  ((List.nodup_finRange wireCount).filter _).map (Fin.castAdd_injective wireCount 1)

theorem mem_parked (w : Wire) (k : Fin payloadCount) :
    k ∈ parked w ↔ k ≠ wireSlot w ∧ k ≠ io := by
  induction k using Fin.addCases with
  | left k =>
    have hn : Fin.castAdd 1 k ≠ io := by
      have := wireSlot_ne_io (wireEquiv k)
      simpa only [wireSlot, Equiv.symm_apply_apply] using this
    simp only [parked, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, he⟩
      have hjk := Fin.castAdd_injective _ _ he
      subst j
      exact ⟨(Fin.castAdd_injective wireCount 1).ne hj, hn⟩
    · intro hk
      exact ⟨k, fun he => hk.1 (congrArg (Fin.castAdd 1) he), rfl⟩
  | right k =>
    have he : Fin.natAdd wireCount k = io := by
      apply Fin.ext; have hk := k.isLt; simp only [io, Fin.val_natAdd, Fin.val_last]; omega
    rw [he]
    simp only [ne_eq, not_true_eq_false, and_false, iff_false]
    intro h
    obtain ⟨j, _, hj⟩ := List.mem_map.mp h
    exact wireSlot_ne_io (wireEquiv j) (by simpa only [wireSlot, Equiv.symm_apply_apply] using hj)

theorem active_not_parked (w : Wire) : wireSlot w ∉ parked w := by
  rw [mem_parked]; simp

theorem io_not_parked (w : Wire) : io ∉ parked w := by
  rw [mem_parked]; simp

theorem active_ne_io (w : Wire) : wireSlot w ≠ io := wireSlot_ne_io w

end CallLayout

end
end IntegerMultBounds.MathlibTM2.M8.Machine
