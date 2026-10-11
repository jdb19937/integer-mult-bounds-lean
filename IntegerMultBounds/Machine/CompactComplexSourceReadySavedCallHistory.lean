module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyFullChildSavedStackHistory
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedSavedStackHistory

/-! The physical saved-PC stack is associated with a list of genuine calls.
Each frame contains the original code of its call, so a reached nonempty
stack supplies both its exact top call and its older semantic stack. Actual
full child entry pushes this list; the actual corrected decoder restores it. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexSourceReadySavedCallHistory
noncomputable section
open Networks
open CompactComplexSavedStackTailInvariant (History Invariant history_tail)
open CompactComplexSourceReadyScalarWorkspace (roles tapes scratch)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyCorrectedSavedReturnPath (publicSaved path)
open CompactComplexSourceReadyCorrectedActualTable (savedStackSlot)
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexNonleafRolePreparation (sourceReady)
open CompactComplexNonleafRoleChildBank (storage output)
variable {s : ℕ} {sh : Shape} {left k : ℕ}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

/-- The list is newest-call first, and every stored frame is its genuine code. -/
inductive Associated (origin : ℤ) : List ComplexRecursiveCallSchema.Call → (ℤ → Fin 6) → ℤ → Prop
  | empty : Associated origin [] (fun _ => blank) origin
  | push {calls f head} (older : Associated origin calls f head) (call : ComplexRecursiveCallSchema.Call) :
      Associated origin (call::calls)
        (FiniteReturnStack.wordPart f head (CompactComplexCallReturn.code call)
          (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (head+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))

/-- Semantic association supplies the ordinary physical history and blank tail. -/
theorem physical {origin head : ℤ} {calls : List ComplexRecursiveCallSchema.Call} {f : ℤ → Fin 6}
    (h : Associated origin calls f head) :
    History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) origin f head := by
  induction h with
  | empty => exact History.empty
  | push older call ih => exact History.push ih (CompactComplexCallReturn.code call)

/-- A known top call is matched to its actual code, with an associated older list. -/
theorem top {origin head : ℤ} {call : ComplexRecursiveCallSchema.Call}
    {calls : List ComplexRecursiveCallSchema.Call} {f : ℤ → Fin 6}
    (h : Associated origin (call::calls) f head) :
    ∃ older top,Associated origin calls older top ∧
      CompactComplexSavedStackTailInvariant.BlankTail older top ∧
      f=FiniteReturnStack.wordPart older top (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl ∧
      head=top+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3) := by
  cases h with
  | push older call => exact ⟨_,_,older,history_tail (physical older),rfl,rfl⟩

/-- An arbitrary reached list exposes either a genuinely empty stack or its top call. -/
theorem cases_stack {origin head : ℤ} {calls : List ComplexRecursiveCallSchema.Call} {f : ℤ → Fin 6}
    (h : Associated origin calls f head) :
    (calls=[] ∧ f=(fun _ => blank) ∧ head=origin) ∨
      ∃ call rest older top,calls=call::rest ∧ Associated origin rest older top ∧
        CompactComplexSavedStackTailInvariant.BlankTail older top ∧
        f=FiniteReturnStack.wordPart older top (CompactComplexCallReturn.code call)
          (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl ∧
        head=top+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3) := by
  cases h with
  | empty => exact Or.inl ⟨rfl,rfl,rfl⟩
  | push older call => exact Or.inr ⟨call,_,_,_,rfl,older,history_tail (physical older),rfl,rfl⟩

/-- Semantic call stack at the actual saved-PC port of the complete controller. -/
def Reached (pcStack : Fin s) (origin : ℤ) (calls : List ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s roles) 2) : Prop :=
  Associated origin calls (v.tape (savedStackSlot pcStack)) (v.head (savedStackSlot pcStack))

/-- All private suffixes retain the exact semantic call association. -/
theorem ready_associated (pcStack : Fin s) (origin : ℤ) (calls : List ComplexRecursiveCallSchema.Call)
    (v : Tapes (publicTapes s roles) 2) (scalar : Tapes scratch 2)
    (h : Associated origin calls (v.tape (publicSaved pcStack)) (v.head (publicSaved pcStack))) :
    Reached pcStack origin calls ((ready v).append scalar) := by
  have hs := CompactComplexSourceReadyCorrectedSavedReturnPath.ready_saved pcStack v scalar
  unfold Reached
  rw [hs.1,hs.2]
  exact h

/-- The complete actual child-entry endpoint pushes its own call onto the list. -/
theorem child_entry_push (call : ComplexRecursiveCallSchema.Call) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell p : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/roles) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) roles) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s)
    (hh : pcStack≠headerStack) (hl : pcStack≠liveStack) (origin : ℤ)
    (calls : List ComplexRecursiveCallSchema.Call)
    (h : Associated origin calls
      (v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack)))
      (v.head (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack)))) :
    let out := CompactComplexSourceReadyChildEntryPath.publicOutput call rho visit hactive pair rows ell p f v
      parentTarget n headerStack pcStack liveStack
    Associated origin (call::calls) (out.tape (publicSaved pcStack)) (out.head (publicSaved pcStack)) := by
  dsimp only
  have hs := CompactComplexSourceReadyFullChildSavedStackHistory.source_ready_pc
    (CompactComplexSourceReadyChildEntryPath.selected call) rho visit hactive pair rows ell p f v pcStack
  have ho := CompactComplexSourceReadyFullChildSavedStackHistory.output_pc
    (sourceReady (CompactComplexSourceReadyChildEntryPath.selected call) rho visit hactive pair rows ell p f v)
    parentTarget n (k+2) headerStack pcStack liveStack hh hl call.site rho visit hactive pair call.slot
    (rows/roles) ell p (CompactNativeRoleReservedBridge.sourcePayload sh (rows/roles) ell f roles)
  dsimp only at ho
  change Associated origin (call::calls)
    ((output _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).tape (storage (Fin.natAdd 10 pcStack)))
    ((output _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).head (storage (Fin.natAdd 10 pcStack)))
  rw [ho.1,ho.2,hs.1,hs.2]
  simpa only [CompactComplexRecursiveGeometry.arity,CompactComplexCallReturn.code] using Associated.push h call

/-- Reached association supplies the genuine top call and older tape for the
actual corrected decoder, and returns with the older semantic list restored. -/
theorem decoded_return_pop (headerStack pcStack liveStack : Fin s)
    (origin : ℤ) (call : ComplexRecursiveCallSchema.Call) (calls : List ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s roles) 2) (h : Reached pcStack origin (call::calls) v) :
    ∃ older top,path headerStack pcStack liveStack 0 v
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5)
        (CompactComplexScheduledPCDecode.savedPC call) (setTape v (savedStackSlot pcStack) older top) ∧
      Reached pcStack origin calls (setTape v (savedStackSlot pcStack) older top) ∧
      Invariant (savedStackSlot pcStack) (setTape v (savedStackSlot pcStack) older top) := by
  obtain ⟨older,top,hOlder,hBlank,ht,hh⟩ := top h
  have hs : FiniteReturnStack.bank (v.tape (savedStackSlot pcStack)) (v.head (savedStackSlot pcStack))=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older top (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (top+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) := by
    rw [ht,hh]
  have hr := CompactComplexSourceReadyReachedSavedStackHistory.decoded_return_history
    headerStack pcStack liveStack call v older origin top (physical hOlder) hs
  refine ⟨older,top,hr.1,?_,hr.2.2⟩
  simpa only [Reached,setTape,Function.update_self] using hOlder

end
end IntegerMultBounds.Machine.CompactComplexSourceReadySavedCallHistory
