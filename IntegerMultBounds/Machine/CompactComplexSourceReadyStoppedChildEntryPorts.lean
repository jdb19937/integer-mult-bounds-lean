module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCapturedChildFrames
public import IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnPorts
public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedSettledFrames

/-! Literal controller, immutable scalar, count and clock ports retained by
actual source preparation and child entry, including all saved stack pushes. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedChildEntryPorts
noncomputable section
open CompactComplexNonleafRoleChildBank (tapes control storage)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexSourceReadyCapturedChildFrames (childOutput)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller)
open CompactComplexChildHeadersData (parent)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyChildEntryPath (selected)
variable {stackTapeCount roleCount : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule

/-- Ports outside every actual child-entry write: the retained control fields,
immutable scalar descriptor bank, erased count and reusable auxiliary clock. -/
def Retained (portValue : ℕ) : Prop :=
  (portValue<43 ∧ portValue≠1) ∨
  (120+stackTapeCount≤portValue ∧ portValue<163+stackTapeCount) ∨
  portValue=110 ∨ portValue=164+stackTapeCount+roleCount

private theorem retained_split (port : Fin (tapes stackTapeCount roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val)
    (localPort : Fin (43+CompactNativeRoleInstall.rawCount roleCount)) :
    port≠CompactComplexNonleafRoleSplit.slot (s:=10+stackTapeCount) (c:=roleCount) localPort := by
  intro portsEqual
  have portValuesEqual := congrArg Fin.val portsEqual
  have localPortBound := localPort.isLt
  dsimp only [CompactComplexNonleafRoleSplit.slot] at portValuesEqual
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at portValuesEqual
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at localPortBound
  rcases retained with controlRange|scalarRange|countPort|clockPort
  all_goals split_ifs at portValuesEqual <;> omega

private theorem retained_numeric (port : Fin (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val)
    (numericPort : Fin 43) : port≠CompactComplexNonleafRoleEntry.numeric numericPort := by
  intro portsEqual
  have portValuesEqual := congrArg Fin.val portsEqual
  have numericPortBound := numericPort.isLt
  simp only [CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at portValuesEqual
  rcases retained with controlRange|scalarRange|countPort|clockPort <;> omega

private theorem retained_stack (port : Fin (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val) :
    port≠CompactComplexNonleafRoleEntry.stack := by
  intro portsEqual
  have portValuesEqual := congrArg Fin.val portsEqual
  simp only [CompactComplexNonleafRoleEntry.stack,Fin.val_natAdd,
    CompactComplexNativeCodecFrame.permanentTapes,CompactComplexNativeRoleBridge.publicTapes,
    CompactComplexControllerNativeFrame.tapes] at portValuesEqual
  rcases retained with controlRange|scalarRange|countPort|clockPort <;> omega

private theorem retained_source (port : Fin (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val) :
    port≠CompactComplexNonleafRoleEntry.source := by
  intro portsEqual
  have portValuesEqual := congrArg Fin.val portsEqual
  simp only [CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at portValuesEqual
  rcases retained with controlRange|scalarRange|countPort|clockPort <;> omega

private theorem retained_role (port : Fin (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val)
    (role : Fin roleCount) : port≠CompactComplexNonleafRoleEntry.roleTape role := by
  intro portsEqual
  have portValuesEqual := congrArg Fin.val portsEqual
  have roleBound := role.isLt
  simp only [CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNonleafRoleEntry.tapes,CompactComplexNativeRoleBridge.roleSlot,
    CompactComplexNativeCodecFrame.permanentTapes,CompactComplexNativeRoleBridge.publicTapes,
    CompactComplexControllerNativeFrame.tapes,Fin.val_castAdd,Fin.val_natAdd] at portValuesEqual
  rcases retained with controlRange|scalarRange|countPort|clockPort <;> omega

private theorem retained_control_one (port : Fin (tapes stackTapeCount roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val) : port≠control 1 := by
  intro portsEqual
  have portValuesEqual := congrArg Fin.val portsEqual
  change port.val=1 at portValuesEqual
  rcases retained with controlRange|scalarRange|countPort|clockPort <;> omega

private theorem retained_storage (port : Fin (tapes stackTapeCount roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val)
    (storagePort : Fin (10+stackTapeCount))
    (written : storagePort.val=7 ∨ storagePort.val=8 ∨ storagePort.val=9 ∨ 10≤storagePort.val) :
    port≠storage storagePort := by
  intro portsEqual
  have portValuesEqual := congrArg Fin.val portsEqual
  have storagePortBound := storagePort.isLt
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at portValuesEqual
  rcases retained with controlRange|scalarRange|countPort|clockPort
  all_goals rcases written with livePort|targetPort|targetStack|savedStack <;> omega

private theorem replace_retained (inputBank : Tapes (tapes stackTapeCount roleCount) 2)
    (rawBank : Tapes (43+CompactNativeRoleInstall.rawCount roleCount) 2)
    (port : Fin (tapes stackTapeCount roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val) :
    (Placement.replace CompactComplexNonleafRoleSplit.placement inputBank rawBank).head port=inputBank.head port ∧
    (Placement.replace CompactComplexNonleafRoleSplit.placement inputBank rawBank).tape port=inputBank.tape port := by
  obtain ⟨placedPort,portEquation⟩ := (CompactComplexNonleafRoleSplit.placement (s:=10+stackTapeCount) (c:=roleCount)).surjective port
  rw [←portEquation]
  induction placedPort using Fin.addCases with
  | left placedPort =>
    have placedEquation : CompactComplexNonleafRoleSplit.placement (s:=10+stackTapeCount) (c:=roleCount)
        (Fin.castAdd _ placedPort)=CompactComplexNonleafRoleSplit.slot placedPort := by
      simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
    exact (retained_split port retained placedPort (portEquation.symm.trans placedEquation)).elim
  | right placedPort =>
    simp only [Placement.replace,Placement.combine_head_extra,Placement.combine_tape_extra,Placement.extra,and_self]

private def scalarPort (descriptorPort : Fin 43) : Fin (tapes stackTapeCount roleCount) :=
  Fin.castAdd 7 (Fin.castAdd 2 (CompactComplexNativeCodecFrame.originalSlot (s:=10+stackTapeCount) (c:=roleCount) descriptorPort))

private theorem scalar_projection_slot (descriptorPort : Fin 43) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackTapeCount roleCount).symm
      (Fin.castAdd 9 (CompactComplexNativeCodecFrame.originalSlot (s:=10+stackTapeCount) (c:=roleCount) descriptorPort))=
      scalarPort descriptorPort := Fin.ext rfl

private theorem controller_projection_slot (controllerPort : Fin 43) :
    control (s:=stackTapeCount) (c:=roleCount) controllerPort=
      Fin.castAdd 7 (CompactComplexNonleafRolePreparation.callerControl (s:=10+stackTapeCount) (c:=roleCount) controllerPort) :=
  Fin.ext rfl

section Physical
variable {shape : CompactGadgetReservationShape.Shape} {leftBoundary childExponent siteCount : ℕ}
    (rowCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+2))
    (activeFitsAxes : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rowCount logColumns metadataPrecision : ℕ)

/-- Actual selected-role parking and quotient setup preserve every retained
port of the literal input caller bank. -/
theorem source_ready_retained (selectedRole : Fin roleCount)
    (selectedData : CompactSpectatorVisitGeometry.Array shape (rowCount/roleCount) logColumns)
    (inputBank : Tapes (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roleCount) 2)
    (port : Fin (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val) :
    (CompactComplexNonleafRolePreparation.sourceReady selectedRole rowCoordinate visit activeFitsAxes pair
      rowCount logColumns metadataPrecision selectedData inputBank).head (Fin.castAdd 7 port)=inputBank.head port ∧
    (CompactComplexNonleafRolePreparation.sourceReady selectedRole rowCoordinate visit activeFitsAxes pair
      rowCount logColumns metadataPrecision selectedData inputBank).tape (Fin.castAdd 7 port)=inputBank.tape port := by
  have quotientFrame := CompactComplexNonleafRolePreparation.quotient_output_frame selectedRole shape
    rowCount logColumns metadataPrecision (parent rowCoordinate visit activeFitsAxes pair).rho
    (parent rowCoordinate visit activeFitsAxes pair).left (parent rowCoordinate visit activeFitsAxes pair).f
    (parent rowCoordinate visit activeFitsAxes pair).slots (parent rowCoordinate visit activeFitsAxes pair).right
    (parent rowCoordinate visit activeFitsAxes pair).source.val (parent rowCoordinate visit activeFitsAxes pair).target.val
    selectedData inputBank (Fin.castAdd 7 port) (retained_split _ retained)
  have entryFrame := CompactComplexNonleafRoleEntry.output_frame selectedRole shape
    rowCount logColumns metadataPrecision (parent rowCoordinate visit activeFitsAxes pair).rho
    (parent rowCoordinate visit activeFitsAxes pair).left (parent rowCoordinate visit activeFitsAxes pair).f
    (parent rowCoordinate visit activeFitsAxes pair).slots (parent rowCoordinate visit activeFitsAxes pair).right
    (parent rowCoordinate visit activeFitsAxes pair).source.val (parent rowCoordinate visit activeFitsAxes pair).target.val
    inputBank port (retained_numeric port retained) (retained_stack port retained)
    (retained_source port retained) (retained_role port retained)
  exact ⟨quotientFrame.1.trans (by simpa only [Tapes.append,Fin.addCases_left] using entryFrame.1),
    quotientFrame.2.trans (by simpa only [Tapes.append,Fin.addCases_left] using entryFrame.2)⟩

/-- Saving target/live/header/PC descriptors and synthesizing actual child
geometry preserves retained controller, scalar, count and clock ports. -/
theorem child_output_retained (inputBank : Tapes (tapes stackTapeCount roleCount) 2)
    (parentTarget parentLive nodeExponent : ℕ) (headerStack pcStack liveStack : Fin stackTapeCount)
    (site : Fin siteCount) (coordinate : Fin arity) (payload : Tapes (1+roleCount) 2)
    (port : Fin (tapes stackTapeCount roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val) :
    (CompactComplexNonleafRoleChildBank.output inputBank parentTarget parentLive nodeExponent
      headerStack pcStack liveStack site rowCoordinate visit activeFitsAxes pair coordinate
      rowCount logColumns metadataPrecision payload).head port=inputBank.head port ∧
    (CompactComplexNonleafRoleChildBank.output inputBank parentTarget parentLive nodeExponent
      headerStack pcStack liveStack site rowCoordinate visit activeFitsAxes pair coordinate
      rowCount logColumns metadataPrecision payload).tape port=inputBank.tape port := by
  have frame := replace_retained
    (CompactComplexNonleafRoleChildBank.descended
      (CompactComplexNonleafRoleChildBank.pcSaved
        (CompactComplexNonleafRoleChildBank.headersSaved
          (CompactComplexNonleafRoleChildBank.liveSaved
            (CompactComplexNonleafRoleChildBank.targetSaved inputBank parentTarget) liveStack parentLive) headerStack
          (CompactComplexControllerChildPrefix.data (parent rowCoordinate visit activeFitsAxes pair))) pcStack site coordinate)
      nodeExponent)
    (CompactNativeRoleOriginal.bank
      (CompactComplexNativeCodec.raw (CompactComplexChildHeadersData.child rowCoordinate visit activeFitsAxes pair coordinate)
        rowCount logColumns metadataPrecision) payload) port retained
  have pcDistinct := retained_storage port retained (Fin.natAdd 10 pcStack)
    (Or.inr (Or.inr (Or.inr (by simp only [Fin.val_natAdd];omega))))
  have headerDistinct := retained_storage port retained (Fin.natAdd 10 headerStack)
    (Or.inr (Or.inr (Or.inr (by simp only [Fin.val_natAdd];omega))))
  have liveStackDistinct := retained_storage port retained (Fin.natAdd 10 liveStack)
    (Or.inr (Or.inr (Or.inr (by simp only [Fin.val_natAdd];omega))))
  have targetDistinct := retained_storage port retained ⟨8,by omega⟩ (Or.inr (Or.inl rfl))
  have targetStackDistinct := retained_storage port retained ⟨9,by omega⟩ (Or.inr (Or.inr (Or.inl rfl)))
  constructor
  · apply frame.1.trans
    simp only [CompactComplexNonleafRoleChildBank.descended,CompactComplexNonleafRoleChildBank.pcSaved,
      FiniteReturnStackAt.pushed,CompactComplexNonleafRoleChildBank.headersSaved,
      CompactComplexNonleafRoleChildBank.liveSaved,CompactComplexNonleafRoleChildBank.targetSaved,
      CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.targetStack,
      SharedPlacementAlphabet.setTape,Function.update_of_ne (retained_control_one port retained),
      Function.update_of_ne pcDistinct,Function.update_of_ne headerDistinct,
      Function.update_of_ne liveStackDistinct,
      Function.update_of_ne targetDistinct,Function.update_of_ne targetStackDistinct]
  · apply frame.2.trans
    simp only [CompactComplexNonleafRoleChildBank.descended,CompactComplexNonleafRoleChildBank.pcSaved,
      FiniteReturnStackAt.pushed,CompactComplexNonleafRoleChildBank.headersSaved,
      CompactComplexNonleafRoleChildBank.liveSaved,CompactComplexNonleafRoleChildBank.targetSaved,
      CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.targetStack,
      SharedPlacementAlphabet.setTape,Function.update_of_ne (retained_control_one port retained),
      Function.update_of_ne pcDistinct,Function.update_of_ne headerDistinct,
      Function.update_of_ne liveStackDistinct,
      Function.update_of_ne targetDistinct,Function.update_of_ne targetStackDistinct]

/-- Abstract chronological entry bank, with selected role and child address
independent of the fixed compiler's concrete call table. -/
private def physicalOutput (selectedRole : Fin roleCount) (site : Fin siteCount) (coordinate : Fin arity)
    (selectedData : CompactSpectatorVisitGeometry.Array shape (rowCount/roleCount) logColumns)
    (inputBank : Tapes (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roleCount) 2)
    (parentTarget parentLive : ℕ) (headerStack pcStack liveStack : Fin stackTapeCount) :=
  CompactComplexNonleafRoleChildBank.output
    (CompactComplexNonleafRolePreparation.sourceReady selectedRole rowCoordinate visit activeFitsAxes pair
      rowCount logColumns metadataPrecision selectedData inputBank)
    parentTarget parentLive (childExponent+2) headerStack pcStack liveStack site
    rowCoordinate visit activeFitsAxes pair coordinate (rowCount/roleCount) logColumns metadataPrecision
    (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roleCount) logColumns selectedData roleCount)

private theorem physical_output_retained (selectedRole : Fin roleCount) (site : Fin siteCount) (coordinate : Fin arity)
    (selectedData : CompactSpectatorVisitGeometry.Array shape (rowCount/roleCount) logColumns)
    (inputBank : Tapes (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roleCount) 2)
    (parentTarget parentLive : ℕ) (headerStack pcStack liveStack : Fin stackTapeCount)
    (port : Fin (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val) :
    (physicalOutput rowCoordinate visit activeFitsAxes pair rowCount logColumns metadataPrecision selectedRole site coordinate
      selectedData inputBank parentTarget parentLive headerStack pcStack liveStack).head (Fin.castAdd 7 port)=inputBank.head port ∧
    (physicalOutput rowCoordinate visit activeFitsAxes pair rowCount logColumns metadataPrecision selectedRole site coordinate
      selectedData inputBank parentTarget parentLive headerStack pcStack liveStack).tape (Fin.castAdd 7 port)=inputBank.tape port := by
  have sourceFrame := source_ready_retained rowCoordinate visit activeFitsAxes pair
    rowCount logColumns metadataPrecision selectedRole selectedData inputBank port retained
  have childFrame := child_output_retained rowCoordinate visit activeFitsAxes pair
    (rowCount/roleCount) logColumns metadataPrecision
    (CompactComplexNonleafRolePreparation.sourceReady selectedRole rowCoordinate visit activeFitsAxes pair
      rowCount logColumns metadataPrecision selectedData inputBank)
    parentTarget parentLive (childExponent+2) headerStack pcStack liveStack site coordinate
    (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roleCount) logColumns selectedData roleCount)
    (Fin.castAdd 7 port) retained
  exact ⟨childFrame.1.trans sourceFrame.1,childFrame.2.trans sourceFrame.2⟩

private theorem public_output_eq (call : Networks.ComplexRecursiveCallSchema.Call)
    (selectedData : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (inputBank : Tapes (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roles) 2)
    (parentTarget parentLive : ℕ) (headerStack pcStack liveStack : Fin stackTapeCount) :
    CompactComplexSourceReadyChildEntryPath.publicOutput call rowCoordinate visit activeFitsAxes pair
      rowCount logColumns metadataPrecision selectedData inputBank parentTarget parentLive headerStack pcStack liveStack=
    physicalOutput rowCoordinate visit activeFitsAxes pair rowCount logColumns metadataPrecision
      (selected call) call.site call.slot selectedData inputBank parentTarget parentLive headerStack pcStack liveStack := rfl

/-- The fixed compiler's actual call uses the same abstract chronology; this
bridge keeps its concrete role and site enumeration out of port conversion. -/
theorem public_output_retained (call : Networks.ComplexRecursiveCallSchema.Call)
    (selectedData : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (inputBank : Tapes (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roles) 2)
    (parentTarget parentLive : ℕ) (headerStack pcStack liveStack : Fin stackTapeCount)
    (port : Fin (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roles))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roles) port.val) :
    (CompactComplexSourceReadyChildEntryPath.publicOutput call rowCoordinate visit activeFitsAxes pair
      rowCount logColumns metadataPrecision selectedData inputBank parentTarget parentLive headerStack pcStack liveStack).head
      (Fin.castAdd 7 port)=inputBank.head port ∧
    (CompactComplexSourceReadyChildEntryPath.publicOutput call rowCoordinate visit activeFitsAxes pair
      rowCount logColumns metadataPrecision selectedData inputBank parentTarget parentLive headerStack pcStack liveStack).tape
      (Fin.castAdd 7 port)=inputBank.tape port := by
  rw [public_output_eq]
  exact physical_output_retained rowCoordinate visit activeFitsAxes pair rowCount logColumns metadataPrecision
    (selected call) call.site call.slot selectedData inputBank parentTarget parentLive headerStack pcStack liveStack port retained

end Physical

section Reached
variable {shape : CompactGadgetReservationShape.Shape} {leftBoundary childExponent : ℕ}
    {levelCount frameCount returnedVolume rowCount logColumns metadataPrecision basePrecision growthConstant axesUsed baselinePrecision scalarPrefix parentLive : ℕ}
    (rowCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+2))
    (activeFitsAxes : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin stackTapeCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes stackTapeCount roles) 2}
    (parentReached : Reached (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision
      (childExponent+2) basePrecision growthConstant axesUsed baselinePrecision levelCount frameCount returnedVolume
      scalarPrefix parentLive pcStack stackOrigin savedCalls parentBank)
    (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackTapeCount)

/-- Literal retained ports of the actual captured child-entry endpoint read
back to the same physical parent caller ports. -/
theorem child_caller_port
    (port : Fin (CompactComplexNonleafRoleEntry.tapes (10+stackTapeCount) roles))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roles) port.val) :
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).head
      (Fin.castAdd 7 port)=(caller parentReached).head port ∧
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).tape
      (Fin.castAdd 7 port)=(caller parentReached).tape port := by
  exact public_output_retained rowCoordinate visit activeFitsAxes pair rowCount logColumns metadataPrecision call
    (CompactComplexSourceReadyReachedChildInvariant.selectedArray parentReached call) (caller parentReached)
    parentReached.targetValue parentLive headerStack pcStack liveStack port retained

/-- Controller workspace survives the complete actual child entry. -/
theorem child_control (controllerPort : Fin 43) (notExponent : controllerPort≠1) :
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).head
      (control controllerPort)=parentReached.control.head controllerPort ∧
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).tape
      (control controllerPort)=parentReached.control.tape controllerPort := by
  let callerPort := CompactComplexNonleafRolePreparation.callerControl (s:=10+stackTapeCount) (c:=roles) controllerPort
  have retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roles) callerPort.val := by
    apply Or.inl
    refine ⟨controllerPort.isLt,?_⟩
    intro portIsOne
    exact notExponent (Fin.ext portIsOne)
  have framed := child_caller_port rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack callerPort retained
  have callerValue := CompactComplexSourceReadyScalarChildReadiness.entry_control
    parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision)
    parentReached.tail parentReached.storage parentReached.payload parentReached.aux (SharedBank.empty 7 2) controllerPort
  rw [controller_projection_slot] at callerValue
  exact ⟨framed.1.trans (by simpa only [callerPort,caller,Tapes.append,Fin.addCases_left] using callerValue.1),
    framed.2.trans (by simpa only [callerPort,caller,Tapes.append,Fin.addCases_left] using callerValue.2)⟩

theorem child_control28 :
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).head (control 28)=0 ∧
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).tape (control 28)=(fun _ => blank) := by
  have framed := child_control rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack 28 (by decide)
  exact ⟨framed.1.trans parentReached.control28_blank.1,framed.2.trans parentReached.control28_blank.2⟩

theorem child_control29 :
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).head (control 29)=0 ∧
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).tape (control 29)=(fun _ => blank) := by
  have framed := child_control rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack 29 (by decide)
  exact ⟨framed.1.trans parentReached.control29_blank.1,framed.2.trans parentReached.control29_blank.2⟩

/-- The count header is still literally erased after saving all child frames. -/
theorem child_count_blank :
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).head
      (storage (⟨0,by omega⟩ : Fin (10+stackTapeCount)))=0 ∧
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).tape
      (storage (⟨0,by omega⟩ : Fin (10+stackTapeCount)))=(fun _ => blank) := by
  let callerPort := CompactComplexNonleafRoleReturnFrame.oldSlot (s:=10+stackTapeCount) (c:=roles) ⟨0,by omega⟩
  have framed := child_caller_port rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack
    callerPort (Or.inr (Or.inr (Or.inl rfl)))
  have callerPrefix := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload) parentReached.aux
    (CompactComplexSpectatorTargetBank.oldSlot (s:=10+stackTapeCount) (c:=roles) ⟨0,by omega⟩)
  have oldValue := CompactComplexSpectatorTargetBank.old_bank parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision)
    parentReached.tail parentReached.storage parentReached.payload (⟨0,by omega⟩ : Fin (10+stackTapeCount))
  exact ⟨framed.1.trans (callerPrefix.1.trans (oldValue.1.trans parentReached.count_blank.1)),
    framed.2.trans (callerPrefix.2.trans (oldValue.2.trans parentReached.count_blank.2))⟩

/-- Actual payload parking and child synthesis leave the reusable clock blank. -/
theorem child_clock_blank :
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).head (extra 1)=0 ∧
    (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack).tape (extra 1)=(fun _ => blank) := by
  let callerPort := Fin.natAdd (CompactComplexSourceReadyScalarWorkspace.permanentTapes stackTapeCount roles) (1 : Fin 2)
  have retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roles) callerPort.val := by
    apply Or.inr;apply Or.inr;apply Or.inr
    simp only [callerPort,Fin.val_natAdd,Fin.val_one,
      CompactComplexSourceReadyScalarWorkspace.permanentTapes,CompactComplexNativeCodecFrame.permanentTapes,
      CompactComplexNativeRoleBridge.publicTapes,CompactComplexControllerNativeFrame.tapes]
    omega
  have framed := child_caller_port rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack callerPort retained
  have callerValue := CompactComplexSourceReadyScalarChildReadiness.entry_aux
    (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent rowCoordinate visit activeFitsAxes pair) rowCount logColumns metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload) parentReached.aux 1
  exact ⟨framed.1.trans (callerValue.1.trans parentReached.clock_blank.1),
    framed.2.trans (callerValue.2.trans parentReached.clock_blank.2)⟩

/-- Immutable scalar metadata is retained on its literal projected bank. -/
theorem child_scalarPart :
    CompactComplexSourceReadyChildReturnPath.scalarPart
      (childOutput rowCoordinate visit activeFitsAxes pair parentReached call headerStack liveStack)=
      ActiveRepairRankHeadersCommands.bank (a:=2) parentReached.scalar := by
  have framed (descriptorPort : Fin 43) := child_caller_port rowCoordinate visit activeFitsAxes pair
    parentReached call headerStack liveStack
    (Fin.castAdd 2 (CompactComplexNativeCodecFrame.originalSlot (s:=10+stackTapeCount) (c:=roles) descriptorPort))
    (by
      apply Or.inr;apply Or.inl
      simp only [CompactComplexNativeCodecFrame.originalSlot,CompactComplexControllerNativeFrame.storageSlot,
        Fin.val_castAdd,Fin.val_natAdd]
      have descriptorBound := descriptorPort.isLt
      constructor <;> omega)
  have callerValue (descriptorPort : Fin 43) :
      (caller parentReached).head
        (Fin.castAdd 2 (CompactComplexNativeCodecFrame.originalSlot (s:=10+stackTapeCount) (c:=roles) descriptorPort))=
        (ActiveRepairRankHeadersCommands.bank (a:=2) parentReached.scalar).head descriptorPort ∧
      (caller parentReached).tape
        (Fin.castAdd 2 (CompactComplexNativeCodecFrame.originalSlot (s:=10+stackTapeCount) (c:=roles) descriptorPort))=
        (ActiveRepairRankHeadersCommands.bank (a:=2) parentReached.scalar).tape descriptorPort := by
    simp only [caller,CompactComplexSourceReadyScalarChildReadiness.entryBank,
      CompactComplexNativeCodecFrame.bank,CompactComplexNativeCodecFrame.originalSlot,
      CompactComplexNativeRoleBridge.bank,CompactComplexControllerNativeFrame.bank,
      CompactComplexControllerNativeFrame.storageSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,and_self]
  apply congrArg₂ Tapes.mk <;> funext descriptorPort
  · simpa only [CompactComplexSourceReadyChildReturnPath.scalarPart,
      CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,Tapes.reindex,
      scalar_projection_slot,scalarPort,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append] using (framed descriptorPort).1.trans (callerValue descriptorPort).1
  · simpa only [CompactComplexSourceReadyChildReturnPath.scalarPart,
      CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,Tapes.reindex,
      scalar_projection_slot,scalarPort,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append] using (framed descriptorPort).2.trans (callerValue descriptorPort).2

end Reached

section Stopped
open CompactComplexSourceReadyStoppedLeafCount (returned)

/-- Literal stopped-leaf return preserves every child-entry retained port. -/
theorem stopped_returned_retained (inputBank : Tapes (tapes stackTapeCount roleCount) 2)
    (childResultWord : ℤ → Fin 6) (childTarget : ℕ) (port : Fin (tapes stackTapeCount roleCount))
    (retained : Retained (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) port.val) :
    (returned inputBank childResultWord childTarget).head port=inputBank.head port ∧
    (returned inputBank childResultWord childTarget).tape port=inputBank.tape port := by
  apply CompactComplexSourceReadyStoppedSettledFrames.returned_frame
  · intro portsEqual
    have portValuesEqual := congrArg Fin.val portsEqual
    simp only [CompactComplexSourceReadyOrientedControlsFrame.source,CompactComplexNonleafRoleEntry.source,
      CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
      Fin.val_castAdd,Fin.val_natAdd] at portValuesEqual
    rcases retained with controlRange|scalarRange|countPort|clockPort <;> omega
  · exact retained_storage port retained ⟨7,by omega⟩ (Or.inl rfl)
  · exact retained_storage port retained ⟨8,by omega⟩ (Or.inr (Or.inl rfl))

/-- The stopped endpoint frames every actual public controller tape. -/
theorem stopped_returned_control (inputBank : Tapes (tapes stackTapeCount roleCount) 2)
    (childResultWord : ℤ → Fin 6) (childTarget : ℕ) (controllerPort : Fin 43) :
    (returned inputBank childResultWord childTarget).head (control controllerPort)=inputBank.head (control controllerPort) ∧
    (returned inputBank childResultWord childTarget).tape (control controllerPort)=inputBank.tape (control controllerPort) := by
  apply CompactComplexSourceReadyStoppedSettledFrames.returned_frame
  all_goals
    intro portsEqual
    have portValuesEqual := congrArg Fin.val portsEqual
    have controllerBound := controllerPort.isLt
    simp only [CompactComplexNonleafRoleChildBank.control,CompactComplexSourceReadyOrientedControlsFrame.source,
      CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
      CompactComplexControllerNativeFrame.nativeSlot,CompactComplexNonleafRoleChildBank.current,
      CompactComplexNonleafRoleChildBank.target,storage,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at portValuesEqual
    omega

/-- The erased count word and head are unchanged by stopped-leaf return. -/
theorem stopped_returned_count (inputBank : Tapes (tapes stackTapeCount roleCount) 2)
    (childResultWord : ℤ → Fin 6) (childTarget : ℕ) :
    (returned inputBank childResultWord childTarget).head (storage (⟨0,by omega⟩ : Fin (10+stackTapeCount)))=
      inputBank.head (storage (⟨0,by omega⟩ : Fin (10+stackTapeCount))) ∧
    (returned inputBank childResultWord childTarget).tape (storage (⟨0,by omega⟩ : Fin (10+stackTapeCount)))=
      inputBank.tape (storage (⟨0,by omega⟩ : Fin (10+stackTapeCount))) :=
  stopped_returned_retained inputBank childResultWord childTarget _ (Or.inr (Or.inr (Or.inl rfl)))

/-- The reusable clock is unchanged by the literal stopped-leaf return. -/
theorem stopped_returned_clock (inputBank : Tapes (tapes stackTapeCount roleCount) 2)
    (childResultWord : ℤ → Fin 6) (childTarget : ℕ) :
    (returned inputBank childResultWord childTarget).head (extra 1)=inputBank.head (extra 1) ∧
    (returned inputBank childResultWord childTarget).tape (extra 1)=inputBank.tape (extra 1) := by
  apply stopped_returned_retained inputBank childResultWord childTarget
  apply Or.inr;apply Or.inr;apply Or.inr
  simp only [extra,CompactComplexNativeCodecFrame.permanentTapes,CompactComplexNativeRoleBridge.publicTapes,
    CompactComplexControllerNativeFrame.tapes,Fin.val_castAdd,Fin.val_natAdd,Fin.val_one]
  omega

/-- Literal stopped-leaf return retains the immutable scalar-bank projection. -/
theorem stopped_returned_scalarPart (inputBank : Tapes (tapes stackTapeCount roleCount) 2)
    (childResultWord : ℤ → Fin 6) (childTarget : ℕ) :
    CompactComplexSourceReadyChildReturnPath.scalarPart (returned inputBank childResultWord childTarget)=
      CompactComplexSourceReadyChildReturnPath.scalarPart inputBank := by
  have framed (descriptorPort : Fin 43) := stopped_returned_retained inputBank childResultWord childTarget
    (scalarPort (stackTapeCount:=stackTapeCount) (roleCount:=roleCount) descriptorPort)
    (by
      apply Or.inr;apply Or.inl
      simp only [scalarPort,CompactComplexNativeCodecFrame.originalSlot,
        CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd]
      have descriptorBound := descriptorPort.isLt
      constructor <;> omega)
  apply congrArg₂ Tapes.mk <;> funext descriptorPort
  · simpa only [CompactComplexSourceReadyChildReturnPath.scalarPart,
      CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,Tapes.reindex,
      scalar_projection_slot] using (framed descriptorPort).1
  · simpa only [CompactComplexSourceReadyChildReturnPath.scalarPart,
      CompactComplexSourceReadyChildReturnPath.permanent,SharedBank.payload,Tapes.reindex,
      scalar_projection_slot] using (framed descriptorPort).2

/-- The exact stopped source word, committed live word and erased target are
computed by the physical endpoint, with their literal public heads. -/
theorem stopped_returned_ports (inputBank : Tapes (tapes stackTapeCount roleCount) 2)
    (childResultWord : ℤ → Fin 6) (childTarget : ℕ) :
    (returned inputBank childResultWord childTarget).head (CompactComplexSourceReadyLeafPhase.source (s:=10+stackTapeCount))=0 ∧
    (returned inputBank childResultWord childTarget).tape (CompactComplexSourceReadyLeafPhase.source (s:=10+stackTapeCount))=childResultWord ∧
    (returned inputBank childResultWord childTarget).head CompactComplexNonleafRoleChildBank.current=1 ∧
    (returned inputBank childResultWord childTarget).tape CompactComplexNonleafRoleChildBank.current=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits childTarget) ∧
    (returned inputBank childResultWord childTarget).head CompactComplexNonleafRoleChildBank.target=0 ∧
    (returned inputBank childResultWord childTarget).tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank) := by
  have sourceCurrentDistinct : CompactComplexSourceReadyLeafPhase.source (s:=10+stackTapeCount) (c:=roleCount)≠
      CompactComplexNonleafRoleChildBank.current := by
    intro portsEqual
    have portValuesEqual := congrArg Fin.val portsEqual
    simp only [CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
      CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
      CompactComplexNonleafRoleChildBank.current,storage,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at portValuesEqual
    omega
  have sourceTargetDistinct : CompactComplexSourceReadyLeafPhase.source (s:=10+stackTapeCount) (c:=roleCount)≠
      CompactComplexNonleafRoleChildBank.target := by
    intro portsEqual
    have portValuesEqual := congrArg Fin.val portsEqual
    simp only [CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
      CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
      CompactComplexNonleafRoleChildBank.target,storage,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at portValuesEqual
    omega
  have currentTargetDistinct : CompactComplexNonleafRoleChildBank.current (s:=stackTapeCount) (c:=roleCount)≠
      CompactComplexNonleafRoleChildBank.target := by
    intro portsEqual
    have portValuesEqual := congrArg Fin.val portsEqual
    simp only [CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.target,
      storage,CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
      Fin.val_castAdd,Fin.val_natAdd] at portValuesEqual
    omega
  simp only [returned,SharedPlacementAlphabet.setTape,Function.update_self,
    Function.update_of_ne sourceCurrentDistinct,Function.update_of_ne sourceTargetDistinct,
    Function.update_of_ne currentTargetDistinct,and_self]

end Stopped

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedChildEntryPorts
