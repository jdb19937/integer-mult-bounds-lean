module

public import IntegerMultBounds.Machine.CompactComplexAlignedStoppedChildRun
public import IntegerMultBounds.Machine.CompactComplexAlignedReachedNodeEntryPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalBank

/-! Actual preorientation and nonstopped classification of the literal raw
whole-source bank. The classifier's computed oriented source is exactly the
originalBank consumed by the physical tag-two node entry. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedNonleafClassifierPrefix
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexSourceReadyWorkspace (leafTapes)
open CompactComplexAlignedReachedNodeEntryPath (originalBank)
open Networks.Shared50ModularControl (prime)
variable {stackCount q : ℕ} {shape : Shape}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount
  CompactComplexCallReturn.addressWidth CompactComplexCallReturn.addressCount

def publicInput (stage : ActivePrefixStageParameters.Stage shape) (rows ell metadataPrecision : ℕ)
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2) :=
  ((bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataPrecision) tail storage
    (CompactNativeRoleReservedBridge.sourcePayload shape rows ell coefficients roles)).append auxiliary).append
    (SharedBank.empty 7 2)

private theorem numeric_ports (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar raw : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+stackCount) 2) (payload : Tapes (1+roles) 2) (auxiliary : Tapes 2 2) (index : Fin 43) :
    (((bank control queue scalar raw tail storage payload).append auxiliary).append (SharedBank.empty 7 2)).head
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric (s:=10+stackCount) (c:=roles) index))=
      (ActiveRepairRankHeadersCommands.bank (a:=2) raw).head index ∧
    (((bank control queue scalar raw tail storage payload).append auxiliary).append (SharedBank.empty 7 2)).tape
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric (s:=10+stackCount) (c:=roles) index))=
      (ActiveRepairRankHeadersCommands.bank (a:=2) raw).tape index := by
  have headers := CompactComplexSourceReadyNonleafFinalBank.headers control queue scalar raw tail storage payload auxiliary
  have headEquation := congrArg (fun candidate => candidate.head index) headers
  have tapeEquation := congrArg (fun candidate => candidate.tape index) headers
  simpa only [CompactComplexNonleafRoleEntry.headerPlacement,InjectivePlacement.active_bank,
    Tapes.append,Fin.addCases_left] using And.intro headEquation tapeEquation

private theorem source_ports (stage : ActivePrefixStageParameters.Stage shape) (rows ell metadataPrecision : ℕ)
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2) :
    (publicInput stage rows ell metadataPrecision coefficients control queue scalar tail storage auxiliary).head
      CompactComplexSourceReadyOrientedControlsFrame.source=0 ∧
    (publicInput stage rows ell metadataPrecision coefficients control queue scalar tail storage auxiliary).tape
      CompactComplexSourceReadyOrientedControlsFrame.source=
      NativeZeroPadding.word (NativeZeroPaddingArray.word coefficients) := by
  have sourceEquation := CompactComplexSourceReadyNonleafFinalBank.source control queue scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataPrecision) tail storage
    (CompactNativeRoleReservedBridge.sourcePayload shape rows ell coefficients roles) auxiliary
  simpa only [publicInput,CompactComplexSourceReadyOrientedControlsFrame.source,Tapes.append,Fin.addCases_left,
    CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload,
    show (0 : Fin (1+roles))=Fin.castAdd roles (0 : Fin 1) from rfl,Fin.addCases_left] using sourceEquation

private theorem public_ready (stage : ActivePrefixStageParameters.Stage shape) (rows ell metadataPrecision : ℕ)
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2) :
    CompactComplexSourceReadyGuard.Ready
      (publicInput stage rows ell metadataPrecision coefficients control queue scalar tail storage auxiliary) := by
  intro slot
  by_cases firstThree : slot.val<3
  · have portEquation := numeric_ports control queue scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataPrecision) tail storage
      (CompactNativeRoleReservedBridge.sourcePayload shape rows ell coefficients roles) auxiliary
      (⟨28+slot.val,by omega⟩ : Fin 43)
    simp only [CompactComplexSourceReadyGuard.scratch,dite_eq_left firstThree]
    dsimp only [publicInput]
    rw [portEquation.1,portEquation.2]
    have indexEquation : (⟨28+slot.val,by omega⟩ : Fin 43)=Fin.natAdd 28 (⟨slot.val,by omega⟩ : Fin 15) := Fin.ext rfl
    rw [indexEquation]
    simp only [ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,Fin.addCases_right,SharedBank.empty,and_self]
  · simp only [CompactComplexSourceReadyGuard.scratch,dite_eq_right firstThree,publicInput,Tapes.append,Fin.addCases_right]
    exact ⟨rfl,rfl⟩

private theorem original_bank_public (stage : ActivePrefixStageParameters.Stage shape) (rows ell metadataPrecision : ℕ)
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2) :
    originalBank stage rows ell metadataPrecision coefficients control queue scalar tail storage auxiliary=
      CompactComplexAlignedBoundaryPaths.alignedBank
        ((CompactComplexSourceReadyWorkspace.ready
          (publicInput stage rows ell metadataPrecision coefficients control queue scalar tail storage auxiliary)).append
          (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)) := by
  unfold originalBank CompactComplexSourceReadyNonleafContraction.ready
  rw [CompactComplexSourceReadyNonleafFinalGeometry.entry_append]
  rfl

private theorem replace_source_word {storageCount roleCount : ℕ}
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar raw : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes storageCount 2) (auxiliary : Tapes 2 2)
    (beforeWord afterWord : ℤ → Fin 6) :
    SharedPlacementAlphabet.setTape
      (((bank control queue scalar raw tail storage
        (CyclicRowCopy.payload beforeWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0))).append auxiliary).append
          (SharedBank.empty 7 2))
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=storageCount) (c:=roleCount))) afterWord 0=
      ((bank control queue scalar raw tail storage
        (CyclicRowCopy.payload afterWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0))).append auxiliary).append
          (SharedBank.empty 7 2) := by
  have singleEqual : SharedPlacementAlphabet.setTape
      (CompactComplexNativeRoleBridge.single
        (CyclicRowCopy.payload beforeWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0)))
      0 afterWord 0=
      CompactComplexNativeRoleBridge.single
        (CyclicRowCopy.payload afterWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0)) := by
    apply congrArg₂ Tapes.mk <;> funext port
    all_goals have portZero : port=(0 : Fin 1) := Fin.ext (by omega)
    all_goals subst port
    all_goals simp only [SharedPlacementAlphabet.setTape,Function.update_self,
      CompactComplexNativeRoleBridge.single,CyclicRowCopy.payload,Tapes.append,
      show (0 : Fin (1+roleCount))=Fin.castAdd roleCount (0 : Fin 1) from rfl,Fin.addCases_left]
  have rolesEqual : CompactNativeRoleSourcePorts.roles
      (CyclicRowCopy.payload beforeWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0))=
      CompactNativeRoleSourcePorts.roles
        (CyclicRowCopy.payload afterWord (fun _ : Fin roleCount => fun _ => blank) 0 (fun _ => 0)) := by
    apply congrArg₂ Tapes.mk <;> funext port
    all_goals have rolePortEquation : (⟨port.val+1,by omega⟩ : Fin (1+roleCount))=Fin.natAdd 1 port := Fin.ext (by simp only [Fin.val_natAdd]; exact Nat.add_comm _ _)
    all_goals simp only [CompactNativeRoleSourcePorts.roles,rolePortEquation,CyclicRowCopy.payload,
      Tapes.append,Fin.addCases_right]
  unfold CompactComplexNonleafRoleEntry.source CompactComplexSpectatorTargetBank.numericSlot
    CompactComplexControllerNativeFrame.nativeSlot bank CompactComplexNativeRoleBridge.bank
    CompactComplexNativeRoleBridge.native CompactComplexControllerNativeFrame.bank
  have sourceIndex : (65 : Fin 66)=Fin.natAdd 43 (Fin.natAdd 22 (0 : Fin 1)) := rfl
  rw [sourceIndex]
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right]
  rw [singleEqual,rolesEqual]


private theorem oriented_public (stage : ActivePrefixStageParameters.Stage shape) (rows ell metadataPrecision : ℕ)
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    CompactComplexSourceReadyOrientedControlsFrame.output call
      (publicInput stage rows ell metadataPrecision coefficients control queue scalar tail storage auxiliary) coefficients=
      publicInput stage rows ell metadataPrecision (oriented call coefficients) control queue scalar tail storage auxiliary := by
  unfold CompactComplexSourceReadyOrientedControlsFrame.output oriented
  split_ifs with inverseCall
  · exact replace_source_word control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataPrecision)
      tail storage auxiliary _ _
  · rfl

/-- Preorientation and the real nonstopped marker enter tag two on exactly
the oriented literal source bank, retaining every original tape frame. -/
theorem runs {nodeLeft nodeExponent levels frames returned rows ell inputPrecision baselinePrecision growthConstant initialLive : ℕ}
    (basisProgram : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin stackCount) (call : Networks.ComplexRecursiveCallSchema.Call)
    (stage : ActivePrefixStageParameters.Stage shape)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent levels frames returned)
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell)
    (inputWidth : CompactSpectatorInheritedGrid.Width shape rows ell inputPrecision coefficients)
    (inputGrid : CompactSpectatorInheritedGrid.Grid shape rows ell inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant levels (frames+2*returned)) coefficients)
    (baselineFits : baselinePrecision≤ inputPrecision)
    (dependencyFitsChunk : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤ shape.chunk)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (activeFitsAxes : shape.active≤ shape.axes)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2)
    (exponentReady : control.head 1=1 ∧ control.tape 1=BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits nodeExponent))
    (origin : ℤ) (olderCalls : List Networks.ComplexRecursiveCallSchema.Call)
    (savedAssociated : CompactComplexSourceReadySavedCallHistory.Associated origin (call::olderCalls)
      (storage.tape (Fin.natAdd 10 pcStack)) (storage.head (Fin.natAdd 10 pcStack)))
    (nodeNonstopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes nodeExponent=false) :
    CompactSpectatorInheritedGrid.Width shape rows ell inputPrecision (oriented call coefficients) ∧
    CompactSpectatorInheritedGrid.Grid shape rows ell inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant levels (frames+2*returned))
      (oriented call coefficients) ∧
    ∃ elapsed≤(CompactComplexSourceReadyOrientationInvariants.constant+
        4*CompactComplexSourceReadyGuard.guardConstant+1)*
      CompactNativeRoleTransferBudget.volume rows shape ell (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)+1,
      CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
        (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount
          CompactComplexCompletedLiveLower.schedule.length 0)
        (originalBank stage rows ell (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
          coefficients control queue scalar tail storage auxiliary) elapsed
        (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount
          CompactComplexCompletedLiveLower.schedule.length 2)
        (originalBank stage rows ell (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
          (oriented call coefficients) control queue scalar tail storage auxiliary) := by
  refine ⟨CompactComplexSourceReadyOrientationInvariants.oriented_width call shape rows ell inputPrecision coefficients inputWidth,
    CompactComplexSourceReadyOrientationInvariants.oriented_grid call entryPath baselinePrecision growthConstant initialLive
      baselineFits dependencyFitsChunk coefficients inputWidth inputGrid,?_⟩
  let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision
  let publicBank := publicInput stage rows ell metadataPrecision coefficients control queue scalar tail storage auxiliary
  obtain ⟨older,top,olderAssociated,olderBlank,tapeEquation,headEquation⟩ :=
    CompactComplexSourceReadySavedCallHistory.top savedAssociated
  have publicSavedPorts : publicBank.head (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack)=
      storage.head (Fin.natAdd 10 pcStack) ∧
      publicBank.tape (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack)=storage.tape (Fin.natAdd 10 pcStack) := by
    simp only [publicBank,publicInput,CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved,
      CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexControllerNativeFrame.storageSlot,bank,CompactComplexNativeRoleBridge.bank,
      CompactComplexControllerNativeFrame.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]
    exact ⟨True.intro,True.intro⟩
  have savedStackReady : Placement.active
      (FiniteReturnStackAt.placement (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack))
      (CompactComplexSourceReadyWorkspace.ready publicBank)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older top (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (top+CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) := by
    rw [FiniteReturnStackAt.active_bank]
    simp only [CompactComplexSourceReadyWorkspace.ready,CompactComplexSourceReadyWorkspace.bank,
      CompactComplexSourceReadyOrientationInvariants.savedSlot,Tapes.append,Fin.addCases_left]
    exact congrArg₂ FiniteReturnStack.bank (publicSavedPorts.2.trans tapeEquation) (publicSavedPorts.1.trans headEquation)
  have sourceReady := source_ports stage rows ell metadataPrecision coefficients control queue scalar tail storage auxiliary
  have dimensionReady : publicBank.head CompactComplexSourceReadyGuard.dimension=1 ∧
      publicBank.tape CompactComplexSourceReadyGuard.dimension=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits shape.axes) := by
    have rawDimension := numeric_ports control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataPrecision)
      tail storage (CompactNativeRoleReservedBridge.sourcePayload shape rows ell coefficients roles) auxiliary 1
    exact rawDimension
  have controlPorts := CompactComplexSourceReadyScalarChildReadiness.entry_control control queue scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataPrecision) tail storage
    (CompactNativeRoleReservedBridge.sourcePayload shape rows ell coefficients roles) auxiliary (SharedBank.empty 7 2) 1
  have actualExponent : publicBank.head CompactComplexSourceReadyGuard.exponent=1 ∧
      publicBank.tape CompactComplexSourceReadyGuard.exponent=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits nodeExponent) := by
    refine ⟨controlPorts.1.trans exponentReady.1,?_⟩
    have controlTape := controlPorts.2.trans exponentReady.2
    exact controlTape.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _)
  obtain ⟨elapsed,elapsedBound,classifierPath⟩ := CompactComplexAlignedStoppedChildRun.classifier_path
    basisProgram headerStack pcStack liveStack call publicBank
    (SharedBank.empty leafTapes 2) (SharedBank.empty 10 2)
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime)
    older top savedStackReady entryPath baselinePrecision growthConstant initialLive baselineFits dependencyFitsChunk
    rowsPositive guardPositive axesPositive activeFitsAxes coefficients inputWidth inputGrid sourceReady.2 sourceReady.1
    (public_ready stage rows ell metadataPrecision coefficients control queue scalar tail storage auxiliary)
    dimensionReady actualExponent
  rw [nodeNonstopped] at classifierPath
  dsimp only [publicBank] at classifierPath
  rw [oriented_public] at classifierPath
  refine ⟨elapsed,elapsedBound,?_⟩
  rw [original_bank_public,original_bank_public]
  exact classifierPath

end
end IntegerMultBounds.Machine.CompactComplexAlignedNonleafClassifierPrefix
