module

public import IntegerMultBounds.Machine.RecursiveFrameControl
public import IntegerMultBounds.Machine.BinaryDescriptorFrameRestore

/-! A real return path over retained nonblank child headers: physically erase
and rewind them, restore saved ancestor fields, pop the binary return PC, and
run the selected continuation. Intervening child execution remains explicit. -/

@[expose] public section

namespace IntegerMultBounds.Machine.RecursiveCleanReturn
open BinaryDescriptorFrames
open FiniteReturnStack (Code Control address)
open SharedPlacementAlphabet (setTape)
variable {t a k N b : ℕ}
noncomputable section

def restoreCost {stack : Fin t} (ops : List (Slot stack)) (older child : Fin t → List Bool) : ℕ :=
  BinaryDescriptorCleanupList.cost (BinaryDescriptorFrameRestore.slots ops) child+1+cost ops older

/-- Restore runtime fields before decoding the binary PC and running its
selected fixed continuation. No decoded address is lost in a Hoare abstraction. -/
def returnProgram (hN : N ≤ 2^k) (stack : Fin t) (ops : List (Slot stack))
    (pcStack : Fin t) (states : Fin N → ℕ) (family : ∀ pc, Program t (states pc) a) :=
  seq (BinaryDescriptorFrameRestore.program stack ops) (FiniteReturnStackAt.dispatchProgram hN pcStack states family)

theorem return_hoare (hN : N ≤ 2^k) (stack : Fin t) (ops : List (Slot stack)) (hu : ops.Nodup)
    (pcStack : Fin t) (hslots : ∀ i ∈ ops, pcStack ≠ i.val)
    (states : Fin N → ℕ) (family : ∀ pc, Program t (states pc) a) (pc : Fin N)
    (xs child : Fin t → List Bool) (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hd : ∀ i ∈ ops, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (child i)) (hfree : Free stack ops xs v)
    (hpct : v.tape pcStack = FiniteReturnStack.wordPart f p (address hN pc) k le_rfl)
    (hpch : v.head pcStack = p+k) (hpcfree : ∀ j < k, f (p+j) = blank)
    (B : ℕ) (post : TapePred t a)
    (hc : HoareTime (family pc) (fun w => w = setTape (restored ops xs v) pcStack f p) post B) :
    HoareTime (returnProgram hN stack ops pcStack states family)
      (fun w => w = saved stack ops xs v) post (restoreCost ops xs child+1+(k+2+B)) := by
  have hf := restored_frame ops xs v pcStack hslots
  exact (BinaryDescriptorFrameRestore.restore_hoare stack ops hu xs child v hd hfree).seq
    (FiniteReturnStackAt.dispatch_hoare hN pcStack states family pc (restored ops xs v) f p B post
      (hf.2.trans hpct) (hf.1.trans hpch) hpcfree hc)

/-- The exact continuation terminal state survives both the return decoder
and the preceding physical cleanup-and-pop program, ready for a finite-flow edge. -/
theorem return_exact (hN : N ≤ 2^k) (stack : Fin t) (ops : List (Slot stack)) (hu : ops.Nodup)
    (pcStack : Fin t) (hslots : ∀ i ∈ ops, pcStack ≠ i.val)
    (states : Fin N → ℕ) (family : ∀ pc, Program t (states pc) a) (pc : Fin N)
    (xs child : Fin t → List Bool) (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hd : ∀ i ∈ ops, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (child i)) (hfree : Free stack ops xs v)
    (hpct : v.tape pcStack = FiniteReturnStack.wordPart f p (address hN pc) k le_rfl)
    (hpch : v.head pcStack = p+k) (hpcfree : ∀ j < k, f (p+j) = blank)
    (steps : ℕ) (d : Config t (states pc) a)
    (hr : run (family pc) steps ((setTape (restored ops xs v) pcStack f p).start (family pc)) = some d)
    (halt : step (family pc) d = none) :
    ∃ prefixSteps, prefixSteps ≤ restoreCost ops xs child ∧
      run (returnProgram hN stack ops pcStack states family) (prefixSteps+1+(k+2+steps))
        ((saved stack ops xs v).start (returnProgram hN stack ops pcStack states family)) =
        some ((d.mapState (FiniteDispatch.right states pc)).mapState (Fin.natAdd (BinaryDescriptorCleanupList.states (BinaryDescriptorFrameRestore.slots ops)+popStates ops))) ∧
      step (returnProgram hN stack ops pcStack states family)
        ((d.mapState (FiniteDispatch.right states pc)).mapState (Fin.natAdd (BinaryDescriptorCleanupList.states (BinaryDescriptorFrameRestore.slots ops)+popStates ops))) = none := by
  obtain ⟨prefixSteps,c,hbound,hfirst,hhalt,hout⟩ := BinaryDescriptorFrameRestore.restore_hoare stack ops hu xs child v hd hfree _ rfl
  have hf := restored_frame ops xs v pcStack hslots
  obtain ⟨hrun,hstop⟩ := FiniteReturnStackAt.dispatch_exact hN pcStack states family pc (restored ops xs v) f p
    (hf.2.trans hpct) (hf.1.trans hpch) hpcfree steps d hr halt
  refine ⟨prefixSteps,hbound,?_,seq_halt_right _ _ hstop⟩
  have hm : (restored ops xs v).start (FiniteReturnStackAt.dispatchProgram hN pcStack states family) =
      {state := (FiniteReturnStackAt.dispatchProgram hN pcStack states family).start,head := c.head,tape := c.tape} := by
    rw [← hout]; rfl
  rw [hm] at hrun
  exact seq_run _ _ hfirst hhalt hrun

end
end IntegerMultBounds.Machine.RecursiveCleanReturn
