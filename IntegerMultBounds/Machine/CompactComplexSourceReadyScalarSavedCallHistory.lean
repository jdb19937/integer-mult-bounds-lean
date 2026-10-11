module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarGeometryEventPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadySavedCallHistory

/-! Actual scalar events retain the semantic saved-call stack. The canonical
caller output changes storage7 and emitted role words only, so the physical
saved-PC port and its associated call list survive the paid scalar node path. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexSourceReadyScalarSavedCallHistory
noncomputable section
open Networks
open CompactComplexSourceReadyScalarWorkspace (roles tapes nodeTapes permanent ready output)
open CompactComplexSourceReadyCorrectedActualTable (savedStackSlot)
open CompactComplexScalarCountRootBank (countSlot)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexScalarCallerEndpoint (storageOutput emitted)
open CompactComplexSourceReadySavedCallHistory (Reached)
variable {s : ℕ}
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexScalarSequenceSemantics (values)
open CompactComplexDenominatorCapacity (ledger scalarRows)
open CompactSpectatorInheritedGrid (dependencyCoefficient)
open Networks.GaussianPrecision (BoundedGrid)
open ButterflyStreamData (Coefficient)
namespace Actual
export CompactComplexSourceReadyActualTable (countHeader countHeader_ne_live scalar event childReturn)
end Actual
theorem liveProof : 7<10+s := by omega
open SharedPlacementAlphabet (setTape)
attribute [local irreducible] ComplexRank25.program CompactComplexRolePhaseSite.roleCount
  CompactComplexCompletedLiveLower.schedule CompactComplexScalarIntegerRows.gates
  Networks.ComplexFramedExecution.rows

/-- The real full-controller saved port selects the original permanent storage. -/
theorem saved_permanent (pcStack : Fin s) (v : Tapes (nodeTapes s roles) 2) :
    (ready v).head (savedStackSlot pcStack)=(permanent v).head (countSlot (Fin.natAdd 10 pcStack)) ∧
    (ready v).tape (savedStackSlot pcStack)=(permanent v).tape (countSlot (Fin.natAdd 10 pcStack)) := by
  simp only [ready,savedStackSlot,CompactComplexSourceReadyActualTable.savedStackSlot,
    CompactComplexSourceReadyOrientationInvariants.savedSlot,Tapes.append,Fin.addCases_left,
    permanent,countSlot,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot]
  exact ⟨rfl,rfl⟩

/-- The live7 update and literal role emission preserve the actual saved stack. -/
theorem caller_saved (pcStack : Fin s) (hs : 7<10+s)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar rawStage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+roles) 2)
    (words : Fin roles → ℤ → Fin 6) (n : ℕ) :
    let before := bank control queue scalar rawStage tail storage payload
    let after := bank control queue scalar rawStage tail (storageOutput hs storage n) (emitted payload words)
    after.head (countSlot (Fin.natAdd 10 pcStack))=before.head (countSlot (Fin.natAdd 10 pcStack)) ∧
    after.tape (countSlot (Fin.natAdd 10 pcStack))=before.tape (countSlot (Fin.natAdd 10 pcStack)) := by
  dsimp only
  have hne : (Fin.natAdd 10 pcStack : Fin (10+s))≠⟨7,hs⟩ := by
    intro he
    have hv := congrArg Fin.val he
    change 10+pcStack.val=7 at hv
    omega
  have h0 := CompactComplexSpectatorTargetBank.old_bank control queue scalar rawStage tail storage payload
    (Fin.natAdd 10 pcStack)
  have h1 := CompactComplexSpectatorTargetBank.old_bank control queue scalar rawStage tail
    (storageOutput hs storage n) (emitted payload words) (Fin.natAdd 10 pcStack)
  simp only [storageOutput,setTape,Function.update_of_ne hne] at h1
  exact ⟨h1.1.trans h0.1.symm,h1.2.trans h0.2.symm⟩

/-- Exact canonical scalar output preserves the associated list on the full bank. -/
theorem output_reached (pcStack : Fin s) (hs : 7<10+s)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar rawStage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+roles) 2)
    (words : Fin roles → ℤ → Fin 6) (n : ℕ) (origin : ℤ)
    (calls : List ComplexRecursiveCallSchema.Call) (v : Tapes (nodeTapes s roles) 2)
    (hv : permanent v=bank control queue scalar rawStage tail storage payload)
    (h : Reached pcStack origin calls (ready v)) :
    Reached pcStack origin calls
      (ready (output v (bank control queue scalar rawStage tail (storageOutput hs storage n) (emitted payload words)))) := by
  have hi := saved_permanent pcStack v
  have hf := saved_permanent pcStack
    (output v (bank control queue scalar rawStage tail (storageOutput hs storage n) (emitted payload words)))
  have he := CompactComplexSourceReadyScalarWorkspace.output_public v
    (bank control queue scalar rawStage tail (storageOutput hs storage n) (emitted payload words))
    (countSlot (Fin.natAdd 10 pcStack))
  have hp := caller_saved pcStack hs control queue scalar rawStage tail storage payload words n
  have hhead : (ready (output v (bank control queue scalar rawStage tail
        (storageOutput hs storage n) (emitted payload words)))).head (savedStackSlot pcStack)=
      (ready v).head (savedStackSlot pcStack) := by
    exact hf.1.trans (he.1.trans (hp.1.trans ((congrArg (fun w => w.head (countSlot (Fin.natAdd 10 pcStack))) hv).symm.trans hi.1.symm)))
  have htape : (ready (output v (bank control queue scalar rawStage tail
        (storageOutput hs storage n) (emitted payload words)))).tape (savedStackSlot pcStack)=
      (ready v).tape (savedStackSlot pcStack) := by
    exact hf.2.trans (he.2.trans (hp.2.trans ((congrArg (fun w => w.tape (countSlot (Fin.natAdd 10 pcStack))) hv).symm.trans hi.2.symm)))
  unfold Reached
  rw [hhead,htape]
  exact h


/-- A genuine scalar event pays its actual corrected-table transition and retains the semantic call list. -/
theorem scalar_path_reached {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (stage : ActivePrefixStageParameters.Stage sh) (parentRows : ℕ)
    (hrows : 0<parentRows/roles) (hG : 0<sh.guard) (hK : 0<sh.chunk) (g : GroupIndex) (ell p C axes metadataP n : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (v : Tapes (nodeTapes s roles) 2)
    (hv : permanent v=bank control queue scalar
      (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Array sh (parentRows/roles) ell)
    (hw : ∀ a i,(data a i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data a i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hblank : storage.head Actual.countHeader=0 ∧ storage.tape Actual.countHeader=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          CompactSpectatorLeafAxis.word (data a))
    (hlive : storage.head ⟨7,liveProof (s:=s)⟩=1 ∧ storage.tape ⟨7,liveProof (s:=s)⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+(gates g).length*guardBits≤sh.chunk)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (baseline : ℕ) (hbase : baseline≤p)
    (hdenRoom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk)
    (hledger : n≤ledger scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows g.val).length)
    (hgrid : ∀ wire i,BoundedGrid n
      (CompactFramedScalarGrid.bound g.val
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n
        data i wire))
    (headerStack pcStack liveStack : Fin s) (origin : ℤ) (calls : List ComplexRecursiveCallSchema.Call)
    (hReached : Reached pcStack origin calls (ready v))
    (i : Fin CompactComplexCompletedLiveLower.schedule.length)
    (hi : CompactComplexCompletedLiveLower.schedule.get i=
      CompactComplexCompletedLiveLower.Event.scalar g) :
    let rawStage := CompactComplexNativeCodec.raw stage parentRows ell metadataP
    let nextStorage := storageOutput (liveProof (s:=s)) storage (n+(gates g).length)
    let nextPayload := emitted payload (fun j => CompactSpectatorLeafAxis.word
      (execute (block g) data (CompactComplexScalarRolePorts.roleIndex.symm j)))
    let nextCaller := bank control queue scalar rawStage tail nextStorage nextPayload
    ∃ m≤(CompactComplexScalarCountLifecycle.roleTimeConstant (block g)+1)*
        (parentRows*(NativePolynomialStageShape.shape sh ell metadataP).recordWidth),
      CompactComplexSourceReadyCorrectedSavedReturnPath.path headerStack pcStack liveStack
        (CompactComplexScheduledPCLayout.eventPC i) (ready v) m
        (CompactComplexScheduledPCLayout.nextPC i) (ready (output v nextCaller)) ∧
      Reached pcStack origin calls (ready (output v nextCaller)) := by
  dsimp only
  obtain ⟨m,hm,hpath⟩ := CompactComplexSourceReadyScalarGeometryEventPath.scalar_path
    path stage parentRows hrows hG hK g ell p C axes metadataP n control queue scalar tail storage payload
    v hv data hw hblank hsource hlive ha hp haxes hroom hC baseline hbase hdenRoom hledger hgrid
    (savedStackSlot pcStack) headerStack pcStack liveStack
    (CompactComplexSourceReadyCorrectedActualTable.controls pcStack)
    (CompactComplexSourceReadyCorrectedActualTable.classify pcStack) i hi
  have hh := output_reached pcStack (by omega) control queue scalar
    (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload
    (fun j => CompactSpectatorLeafAxis.word
      (CompactComplexScalarPolynomialSequence.execute (CompactComplexScalarSegmentRows.block g) data
        (CompactComplexScalarRolePorts.roleIndex.symm j))) (n+(gates g).length) origin calls v hv hReached
  exact ⟨m,hm,hpath,hh⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyScalarSavedCallHistory
