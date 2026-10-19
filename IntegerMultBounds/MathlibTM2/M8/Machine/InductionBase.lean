module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Budget
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallReady
public import IntegerMultBounds.Machine.Shared50RecursiveBasePermutation

/-! The graph's induction base, in the canonical binary source-bank interface and the
logical-volume budget of the recursive case, as `Shared50RecursiveInductionBase` gives it for
Shared50. The width-one digit machine is the full-field transpose
(`Shared50RecursiveBasePermutation.array_transpose`, generic in the descriptor). -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.InductionBase
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Control
open Implementation (implementation widthSlot pcStack)
open BaseExecution (entryConfig)
open Shared50RecursiveBank (bank)
open CallReady (Ready)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeRows (transpose)
open NodeLayout (wires)
open RecursiveRoleSerialization (roles)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
variable {k : ℕ} {v : Descriptor}

/-- Updating the common I/O tape is exactly the canonical output serialization. -/
theorem source_roles_updated (x out : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.updated (roles (RecursiveRowsSerialization.sourceData wires x)) io out =
      roles (RecursiveRowsSerialization.sourceData wires out) := by
  rw [CallReady.source_roles,CallReady.source_roles]
  simp only [RecursiveShiftRoleBank.updated,CallSemantics.childRoles,
    SharedPlacementAlphabet.setTape_setTape]

/-- Binary canonical input is actually transposed and returned to the decoded
caller in the fixed graph, with every stack and spectator retained. -/
theorem run (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (v : Descriptor) (shape : Depth.Shape 0 v)
    (hs old : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hold : ∀ i, (old i).length ≤ 2*volume prime v)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    ∃ n ≤ Budget.budget k 0 (volume prime v),
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        ((raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
          (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st
            (FiniteReturnStack.address capacity (encoding target))))
          (tapeCount capacity widthSlot pcStack (implementation k))).start
          (Control.program capacity widthSlot pcStack (implementation k))) =
      some (entryConfig capacity target
        (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded (transpose (one_dvd v.rows) x))))
          old f p node scalar (SharedBank.empty 0 prime) st)) := by
  have hw := Depth.base_width shape
  let rr := roles (RecursiveRowsSerialization.sourceData wires (encoded x))
  have ht : rr.tape io = RecursiveShiftRoleBank.source (encoded x) := by
    change (roles (RecursiveRowsSerialization.sourceData wires (encoded x))).tape io = _
    rw [CallReady.source_roles]
    simp only [CallSemantics.childRoles,SharedPlacementAlphabet.setTape,Function.update_self]
  obtain ⟨n,hn,htrace⟩ := BaseExecution.guard_base_return capacity target v hw shape.positive
    rr old hs hv f p node scalar (SharedBank.empty 0 prime) st ready.descriptor ready.pc (encoded x) rfl ht
  have hout : RecursiveShiftRoleBank.updated rr io (RecursiveDigitRoleBank.array hw (encoded x)) =
      roles (RecursiveRowsSerialization.sourceData wires (encoded (transpose (one_dvd v.rows) x))) := by
    rw [Shared50RecursiveBasePermutation.array_transpose]
    exact source_roles_updated (encoded x) _
  rw [hout] at htrace
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v shape.positive
  have hreturn := Budget.return_cost_bound (volume prime v) hV old hs hold
    (RecursiveRowsNode.header_length v shape.positive hs hv)
  refine ⟨n,?_,htrace⟩
  unfold Budget.budget Budget.base
  nlinarith

end
end IntegerMultBounds.MathlibTM2.M8.Machine.InductionBase
