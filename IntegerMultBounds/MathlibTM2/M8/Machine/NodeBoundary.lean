module

public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeData

/-!
# Node entry and exit on bit arrays

The split puts the rows of a bit array on the contract-role tapes (`enter_binary`), and the merge
takes the routed transpose of the rows back to the input/output tape (`exit_binary`), each with a
linear time bound, as `Shared50RecursiveNodeBoundary` does for Shared50. The temporaries stay
blank across both: `tempInit` and `tempClear` run in between.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.NodeBoundary

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open NodeLayout (wires entry exit mergeRoute)
open Shared50RecursiveNodeSemantics (encoded)
open RecursiveViewFrameRoleBank (bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)

variable [Net] {u : ℕ} {v : Descriptor}

def entryConstant : ℕ :=
  74 + RecursiveRowsNode.rowConstant roleCount + RecursiveRowsNodeRoleBank.constant roleCount
def exitConstant : ℕ := 128 + RecursiveRowsNode.rowConstant roleCount

theorem enter_binary (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (st : Tapes 1 prime) (aux : Tapes u prime) (hav : RecursiveStackAllocation.Available 0 st) :
    ∃ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount) (RecursiveRowsNodeHeaders.headers hs rs) ∧
      RecursiveStackAllocation.Available 0 (RecursiveViewFrame.savedStack hs st) ∧
      HoareTime (entry (u := u)).program
        (fun w => w = raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs st aux)
          (entry (u := u)).tapes)
        (fun w => w = raw (bank (roles (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd (encoded x)))
          (RecursiveRowsNodeHeaders.headers hs rs) (RecursiveViewFrame.savedStack hs st) aux)
          (entry (u := u)).tapes)
        (entryConstant * volume prime v) := by
  obtain ⟨rs, hrs, hh⟩ := RecursiveRowsNode.entry_hoare (c := roleCount) wires NodeLayout.wires_injective
    hs st aux v roleCount_pos hv hp hd (encoded x)
  exact ⟨rs, hrs, RecursiveRowsNode.saved_available hs st hav,
    hh.consequence (fun _ h => h) (fun _ h => h) (RecursiveRowsNode.entry_cost_linear (c := roleCount) v hp hs hv)⟩

theorem exit_binary (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2)
    (old hs : Fin 6 → List Bool) (ho : RecursiveDimensionBank.Headers v old)
    (hh : RecursiveDimensionBank.Headers (role v roleCount) hs) (hp : v.Positive)
    (st : Tapes 1 prime) (aux : Tapes u prime) (hav : RecursiveStackAllocation.Available 0 st) :
    HoareTime (exit (u := u)).program
      (fun w => w = raw (bank (roles (RecursiveRowsSerialization.roleData wires mergeRoute hd
        (Shared50RecursiveNodeRows.transpose hd (encoded x)))) hs (RecursiveViewFrame.savedStack old st) aux)
        (exit (u := u)).tapes)
      (fun w => w = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (Shared50RecursiveNodeRows.transpose hd x)))) old st aux) (exit (u := u)).tapes)
      (exitConstant * volume prime v) := by
  have h := RecursiveRowsNode.exit_hoare mergeRoute wires NodeLayout.wires_injective old hs st aux
    (RecursiveRowsNode.free_of_available old st hav) v roleCount_pos ho hp hd
    (Shared50RecursiveNodeRows.transpose hd (encoded x))
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (RecursiveRowsNode.exit_cost_linear (c := roleCount) v hp roleCount_pos hd old hs ho hh)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.NodeBoundary
