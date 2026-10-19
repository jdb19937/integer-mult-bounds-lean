module

public import IntegerMultBounds.MathlibTM2.M8.Machine.InductionBase
public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeExecution
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallInductionBridge
public import IntegerMultBounds.MathlibTM2.M8.Machine.Budget

/-! Depth induction for one actual fixed recursive graph. Every child call
uses the graph's physical entry and decoded recovery edge, with the exact
logical-volume budget and the allocated nested stack invariants. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.Induction
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
open RecursiveInterchangeLayout (Descriptor volume role)
open SharedBankStageInput (raw)
variable {k : ℕ}

/-- The recursion contract, including exact restored caller state. -/
def Contract (capacity : Fintype.card PC ≤ 2^k) (depth : ℕ) : Prop :=
  ∀ (target : PC) (v : Descriptor) (_shape : Depth.Shape depth v)
    (hs old : Fin 6 → List Bool) (_hv : RecursiveDimensionBank.Headers v hs)
    (_hold : ∀ i, (old i).length ≤ 2*volume prime v)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (_ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2),
    ∃ n ≤ Budget.budget k depth (volume prime v),
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        ((raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
          (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st
            (FiniteReturnStack.address capacity (encoding target))))
          (tapeCount capacity widthSlot pcStack (implementation k))).start
          (Control.program capacity widthSlot pcStack (implementation k))) =
      some (entryConfig capacity target
        (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded (transpose (one_dvd v.rows) x))))
          old f p node scalar (SharedBank.empty 0 prime) st))

/-- The recursive contract supplies every literal physical call trace. -/
theorem calls {depth b : ℕ} {v : Descriptor} (capacity : Fintype.card PC ≤ 2^k)
    (ih : Contract capacity depth) (hw : v.width=Machine.width*b) (hp : v.Positive)
    (childShape : ∀ i j : Fin Machine.width,
      Depth.Shape depth (RecursiveAffineViews.cross prime b v i j))
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node (SharedBank.empty 1 prime) st) :
    NodeExecution.Calls capacity hw hs f p node st
      (Budget.budget k depth (volume prime v)) := by
  intro site w i j hi data hdata
  obtain ⟨bits,rfl⟩ := hdata
  let mid := CallReady.parkedBank w bits hs f p node
    (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st
  have htrace : ∀ ch : Fin 6 → List Bool,
      RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.child prime 1 b v i j) ch →
      ∃ n ≤ Budget.budget k depth (volume prime v),
        Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
          (entryConfig capacity .guard (RecursiveCallProtocol.childBank mid ch
            (node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime)))
            (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site)))) =
        some (entryConfig capacity (.recover site) (SharedPlacementAlphabet.setTape mid
          (RecursiveCallBank.role (u := 1+(1+0)) io).val
          (RecursiveShiftRoleBank.source (Shared50RecursiveChildPermutation.array hw i j (encoded (bits w)))) 0)) := by
    intro ch hch
    have hr := CallInductionBridge.ready_original w bits hs f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st ready
    have hold : ∀ z, (hs z).length ≤ 2*volume prime (RecursiveAffineViews.cross prime b v i j) := by
      rw [RecursiveAffineViews.cross_volume prime b v i j hw]
      exact RecursiveRowsNode.header_length v hp hs hv
    obtain ⟨n,hn,ht⟩ := ih (.recover site) (RecursiveAffineViews.cross prime b v i j)
      (childShape i j) ch hs hch hold (mid.tape (RecursiveCallBank.controlSlot 2))
      (mid.head (RecursiveCallBank.controlSlot 2)) node (SharedBank.empty 1 prime) st hr
      (Shared50RecursiveChildPermutation.toChild hw i j (bits w))
    rw [RecursiveAffineViews.cross_volume prime b v i j hw] at hn
    have hin := CallInductionBridge.input_bank w i j hw bits hs ch f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st
      (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site))
    have hout := CallInductionBridge.returned_bank w i j hw bits hs f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st
    change Machine.run _ n (entryConfig capacity .guard _) = some (entryConfig capacity (.recover site) _) at ht
    dsimp only [mid] at ht
    dsimp only [returnCode] at hin
    dsimp only at hout
    rw [← hin,hout] at ht
    exact ⟨n,hn,ht⟩
  have hcall := PieceExecution.call_actual (capacity := capacity) (hw := hw)
    (hp := hp) (hs := hs) (hv := hv) (f := f) (p := p) (node := node) (st := st)
    site w i j hi (encodedBits bits (fun _ => blank))
    (Shared50RecursiveChildPermutation.array hw i j (encoded (bits w))) (encodedBits_io _ _) ready.payload _ htrace
  have he : encodedBits bits (fun _ => blank) (wireSlot w) =
      encoded (bits w) := encodedBits_wire bits _ w
  simpa only [PieceExecution.actualCallBound,ChildPermutation.child,he] using hcall

/-- Complete termination, transpose correctness and charged runtime for the
fixed recursive controller on all power-widthSlot nodes. -/
theorem contract (capacity : Fintype.card PC ≤ 2^k) (depth : ℕ) : Contract capacity depth := by
  induction depth with
  | zero => exact InductionBase.run capacity
  | succ depth ih =>
    intro target v shape hs old hv hold f p node scalar st ready x
    have hscalar := ready.scalar
    subst scalar
    have saved := RecursiveStackAllocation.saved_stacks_available old st
      (FiniteReturnStack.address capacity (encoding target)) ready.descriptor ready.pc
    have hw := Depth.split_width shape
    have hd := Depth.split_divides shape
    have hpRole := Depth.split_positive shape
    have hrolevol : volume prime (role v roleCount) = volume prime v/roleCount :=
      (Depth.selected_volume_role shape ⟨0,width_pos⟩ ⟨0,width_pos⟩).symm.trans
        (Depth.selected_volume shape ⟨0,width_pos⟩ ⟨0,width_pos⟩)
    have allCalls : ∀ rs : List Bool,
        RecursiveDimensionBank.Headers (role v roleCount) (RecursiveRowsNodeHeaders.headers hs rs) →
        NodeExecution.Calls capacity (v := role v roleCount) hw
          (RecursiveRowsNodeHeaders.headers hs rs) f p (RecursiveViewFrame.savedStack hs node)
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
          (Budget.budget k depth (volume prime v/roleCount)) := by
      intro rs hrs
      rw [← hrolevol]
      exact calls capacity ih hw hpRole (fun i j => Depth.selected_shape shape i j)
        _ hrs f p _ _ ⟨ready.payload,RecursiveRowsNode.saved_available hs node ready.node,rfl,saved.1,saved.2⟩
    obtain ⟨n,hn,ht⟩ := NodeExecution.guard_return (v := v) capacity target hw shape.positive hd
      old hs hv f p node st ready.node ready.descriptor ready.pc x
      (Budget.budget k depth (volume prime v/roleCount)) allCalls
    have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v shape.positive
    have hroleLe : volume prime (role v roleCount) ≤ volume prime v := by
      rw [hrolevol]
      exact Nat.div_le_self _ _
    have hret := Budget.return_cost_bound (volume prime v) hV old hs hold
      (RecursiveRowsNode.header_length v shape.positive hs hv)
    have hbound := Budget.node_bound k depth (volume prime v)
      (volume prime (role v roleCount)) (RecursiveChildCallReturn.cost old hs) hV hroleLe hret
    exact ⟨n,hn.trans hbound,ht⟩

/-- The explicit graph execution interface, with generalized depth. -/
theorem run (capacity : Fintype.card PC ≤ 2^k) (depth : ℕ) : Contract capacity depth :=
  contract capacity depth

end
end IntegerMultBounds.MathlibTM2.M8.Machine.Induction
