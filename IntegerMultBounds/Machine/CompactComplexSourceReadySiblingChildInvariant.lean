module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingGuards
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedChildInvariant

/-! The actual sibling cursor enters the original child dependency Path once.
The selected grid and physical source ports come from current Reached; sibling
volumes already counted in that parent are not added again on descent. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildInvariant
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactSpectatorInheritedGrid (Grid)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready permanent)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller)
open CompactComplexSourceReadyReachedChildInvariant (Entered selectedArray selected_width selected_grid)
open CompactComplexChildHeadersData (parent child)
open CompactComplexSourceReadyChildEntryPath (publicOutput)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexDenominatorCapacity (ledger scalarRows)
open CompactComplexCompletedLiveLower (schedule childNames)
open Networks
variable {extraTapes : ℕ} {shape : Shape}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule

section Child
variable {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
    (phaseCoordinate : Fin shape.chunk)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume entryReturned)
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes extraTapes roles) 2}
    (parentReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision (childExponent+2) baselinePrecision growthConstant 0
      baselineLive dependencyLevels frameVolume (returnedCursor entryReturned eventIndex (arity^(childExponent+1))) scalarPrefix parentLive pcStack origin calls parentBank)
    (call : ComplexRecursiveCallSchema.Call)

def childPublic (headerStack liveStack : Fin extraTapes) :=
  publicOutput call phaseCoordinate entryPath.visit activeFits pair parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached)
    parentReached.targetValue parentLive headerStack pcStack liveStack

private theorem caller_storage (storageIndex : Fin (10+extraTapes)) :
    (caller parentReached).head (CompactComplexNonleafRoleReturnFrame.oldSlot storageIndex)=parentReached.storage.head storageIndex ∧
    (caller parentReached).tape (CompactComplexNonleafRoleReturnFrame.oldSlot storageIndex)=parentReached.storage.tape storageIndex := by
  have callerPrefixPorts := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload) parentReached.aux (CompactComplexSpectatorTargetBank.oldSlot storageIndex)
  have oldStackPorts := CompactComplexSpectatorTargetBank.old_bank parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision)
    parentReached.tail parentReached.storage parentReached.payload storageIndex
  exact ⟨callerPrefixPorts.1.trans oldStackPorts.1,callerPrefixPorts.2.trans oldStackPorts.2⟩

/-- Genuine current sibling readiness enters Path.child of the original
node-entry Path, with each preceding sibling volume counted exactly once. -/
theorem child_entered (headerStack liveStack : Fin extraTapes)
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack)
    (metadataFits : 2*shape.bits≤metadataPrecision) (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (ordinalEquation : (childNames (schedule.take eventIndex)).length=
      CompactRecursiveDependencyBudget.precedingCalls call) :
    Entered (child phaseCoordinate entryPath.visit activeFits pair call.slot) (parentRows/roles) polynomialExponent metadataPrecision (childExponent+1)
      (nodeLeft+call.slot.val*arity^(childExponent+1)) baselinePrecision growthConstant parentLive baselineLive (dependencyLevels+1) (frameVolume+arity^(childExponent+2))
      (entryReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1))
      pcStack origin (call::calls) (selectedArray parentReached call) (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack) := by
  have cursorEquation : returnedCursor entryReturned eventIndex (arity^(childExponent+1))=
      entryReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1) := by
    simp only [returnedCursor,ordinalEquation]
  have selectedWidth := selected_width parentReached call metadataFits
  have selectedGrid := selected_grid parentReached call metadataFits
  have prefixBound := CompactFramedScalarGrid.bound_le scalarPrefix
    (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
      (frameVolume+2*returnedCursor entryReturned eventIndex (arity^(childExponent+1)))) growthConstant growthReserve
  have nextLevelBound := prefixBound.trans_eq
    (CompactRecursiveGridBudget.scalar_step baselinePrecision growthConstant dependencyLevels
      (frameVolume+2*returnedCursor entryReturned eventIndex (arity^(childExponent+1))))
  have childGrid : Grid shape (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) parentLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant (dependencyLevels+1)
        (frameVolume+arity^(childExponent+2)+2*(entryReturned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1))))
      (selectedArray parentReached call) := by
    intro coefficient
    have childGrid := GaussianPrecision.bound_mono nextLevelBound
      (by simpa only [Nat.add_zero] using selectedGrid coefficient)
    apply GaussianPrecision.bound_mono _ childGrid
    rw [cursorEquation]
    unfold CompactRecursiveGridBudget.bound
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by decide : 0<4)
    omega
  have callerLivePort := caller_storage phaseCoordinate entryPath activeFits pair parentReached ⟨7,by omega⟩
  have enteredLivePort := CompactComplexChildInputReadiness.entered_current call phaseCoordinate entryPath.visit activeFits pair
    parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack
  have savedPorts := CompactComplexSourceReadyScalarSavedCallHistory.saved_permanent pcStack parentBank
  have permanentBankEquation := (congrArg permanent parentReached.canonical_bank).trans
    (CompactComplexSourceReadyReachedEventInvariant.canonical_permanent _ _)
  rw [permanentBankEquation] at savedPorts
  have oldStackPorts := CompactComplexSpectatorTargetBank.old_bank parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision)
    parentReached.tail parentReached.storage parentReached.payload (Fin.natAdd 10 pcStack)
  change (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload).head
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=parentReached.storage.head _ ∧
    (CompactComplexNativeCodecFrame.bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw (parent phaseCoordinate entryPath.visit activeFits pair) parentRows polynomialExponent metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload).tape
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=parentReached.storage.tape _ at oldStackPorts
  rw [oldStackPorts.1,oldStackPorts.2] at savedPorts
  change (ready parentBank).head _=parentReached.storage.head (Fin.natAdd 10 pcStack) ∧
    (ready parentBank).tape _=parentReached.storage.tape (Fin.natAdd 10 pcStack) at savedPorts
  -- The public caller exposes exactly the same genuinely associated stack.
  have savedAssociation : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((caller parentReached).tape (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack)))
      ((caller parentReached).head (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack))) := by
    have callerStackPorts := caller_storage phaseCoordinate entryPath activeFits pair parentReached (Fin.natAdd 10 pcStack)
    rw [callerStackPorts.1,callerStackPorts.2]
    have savedHistory := parentReached.saved_calls
    unfold CompactComplexSourceReadySavedCallHistory.Reached at savedHistory
    rw [savedPorts.1,savedPorts.2] at savedHistory
    exact savedHistory
  have pushedHistory := CompactComplexSourceReadySavedCallHistory.child_entry_push call phaseCoordinate entryPath.visit activeFits pair
    parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack pcHeaderDistinct pcLiveDistinct origin calls savedAssociation
  refine {
    path := CompactRecursiveDependencyBudget.Path.child entryPath call, width := selectedWidth, grid := childGrid,
    upper_ledger := ?_, headers := CompactComplexChildInputReadiness.entered_headers call phaseCoordinate entryPath.visit activeFits pair
      parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack,
    source := CompactComplexChildInputReadiness.entered_source call phaseCoordinate entryPath.visit activeFits pair
      parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack,
    source_support := ?_, stop_ready := CompactComplexChildInputReadiness.entered_stop_ready call phaseCoordinate entryPath.visit activeFits pair
      parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack,
    dimension := CompactComplexChildInputReadiness.entered_dimension call phaseCoordinate entryPath.visit activeFits pair
      parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack,
    live := ?_, target_blank := CompactComplexChildInputReadiness.entered_target call phaseCoordinate entryPath.visit activeFits pair
      parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack,
    exponent := CompactComplexChildInputReadiness.entered_exponent call phaseCoordinate entryPath.visit activeFits pair
      parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack,
    roles_blank := CompactComplexChildInputReadiness.entered_roles call phaseCoordinate entryPath.visit activeFits pair
      parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack,
    saved_calls := CompactComplexSourceReadySavedCallHistory.ready_associated pcStack origin (call::calls) _ _ pushedHistory }
  · have rowsFit := CompactComplexDenominatorCapacity.actual_prefix scalarPrefix
    have parentLedger := parentReached.upper_ledger
    rw [cursorEquation] at parentLedger
    unfold ledger at parentLedger ⊢
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  · apply CompactComplexChildInputReadiness.entered_source_supported call phaseCoordinate entryPath.visit activeFits pair
      parentRows polynomialExponent metadataPrecision (selectedArray parentReached call) (caller parentReached) parentReached.targetValue parentLive headerStack pcStack liveStack
    exact parentReached.width _
  · exact ⟨enteredLivePort.1.trans (callerLivePort.1.trans parentReached.live.1),enteredLivePort.2.trans (callerLivePort.2.trans parentReached.live.2)⟩

end Child
end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildInvariant
