module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildInvariant
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCapturedSettledFrames
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventFrameState

/-! The actual sibling child-entry bank has clean protected storage tails and
a reusable auxiliary suffix. Both are consequences of the parent's Settled
invariant and literal save/parking operations, without a child cleanliness oracle. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildCleanTails
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled protectedSlots)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexSourceReadySiblingChildInvariant (childPublic)
variable {stackCount : ℕ} {shape : Shape}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

section Child
variable {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex rowCount polynomialExponent
    metadataPrecision baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
    (phaseCoordinate : Fin shape.chunk)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
      dependencyLevels frameVolume entryReturned)
    (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes stackCount roles) 2}
    (parentReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair) rowCount polynomialExponent
      metadataPrecision (childExponent+2) baselinePrecision growthConstant 0 baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex (arity^(childExponent+1))) scalarPrefix parentLive pcStack origin savedCalls parentBank)
    (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackCount)

/-- Literal original storage ports for the recursive node entered at this sibling. -/
def childStorage : Tapes (10+stackCount) 2 :=
  SharedBank.payload (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
    CompactComplexNonleafRoleChildBank.storage

/-- The captured storage ports agree with the existing physical return extraction. -/
theorem childStorage_eq_storagePart :
    childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack=
      CompactComplexSourceReadyChildReturnPath.storagePart
        (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack) :=
  CompactComplexSourceReadyCapturedChildFrames.capture_storagePart headerStack pcStack liveStack
    (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)

/-- Literal parked payload and clock ports for that same child bank. -/
def childAuxiliary : Tapes 2 2 :=
  SharedBank.payload (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
    CompactComplexNonleafRoleParentPayloadContinuation.extra

/-- The actual new child snapshot and physical extracted ports are Settled,
with all cleanliness inherited through genuine saved-frame pushes and parking. -/
theorem child_settled
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack)
    (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack) (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack) :
    Settled
      (CompactComplexSourceReadyCapturedChildFrames.capture headerStack pcStack liveStack
        (childPublic phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack))
      (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack)
      (childAuxiliary phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack) := by
  exact CompactComplexSourceReadyCapturedSettledFrames.snapshot_settled_from_parent
    phaseCoordinate entryPath.visit activeFits pair parentReached call headerStack liveStack
    ancestorSnapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
    headerDistinctLive pcDistinctHeader pcDistinctLive

/-- The exact protected storage tails required by the original-input child
node theorem, at the actual advanced child-entry stack heads. -/
theorem original_protected_tails
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack)
    (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack) (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack) :
    ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
      ∀ cell,(childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).head storagePort≤cell →
        (childStorage phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack).tape storagePort cell=blank := by
  have actualChildSettled := child_settled phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack
    ancestorSnapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
    headerDistinctLive pcDistinctHeader pcDistinctLive
  exact actualChildSettled.storage_clean

/-- Actual payload parking leaves the clean reusable suffix required by
recursive input readiness; no auxiliary blank-tail hypothesis is added. -/
theorem auxiliary_free
    (ancestorSnapshot : Snapshot stackCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack)
    (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack) (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack) :
    CompactComplexSourceReadyPrefixReadiness.BlankAfter
      (childAuxiliary phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack) 0 := by
  have actualChildSettled := child_settled phaseCoordinate entryPath activeFits pair parentReached call headerStack liveStack
    ancestorSnapshot parentSettled snapshotHeaderStack snapshotLiveStack snapshotPcStack
    headerDistinctLive pcDistinctHeader pcDistinctLive
  exact actualChildSettled.aux_clean

end Child
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveChildCleanTails
