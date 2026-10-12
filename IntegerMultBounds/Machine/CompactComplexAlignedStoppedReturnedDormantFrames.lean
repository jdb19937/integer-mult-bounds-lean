module

public import IntegerMultBounds.Machine.CompactComplexAlignedStoppedReturnPath
public import IntegerMultBounds.Machine.CompactComplexAlignedReturnedDormantFrames

/-! The actual stopped branch restores the parent's captured older storage
ports and retains the ancestor Settled invariant on its numerical return and
inverse-basis witnesses. This specializes the balanced return theorem to the
computed stopped bank and installed child result, without a fresh frame premise. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedStoppedReturnedDormantFrames
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled)
open CompactComplexSourceReadyReachedReturnInvariant (returnedCaller)
open CompactComplexSourceReadyReachedBasisInvariant (replacementCaller)
open CompactComplexAlignedStoppedReturnPath (stoppedBank stoppedResult)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent)
variable {stackTapeCount : ℕ} {shape : CompactGadgetReservationShape.Shape}
  {leftBoundary childExponent : ℕ}
  {rowCount logColumns metadataPrecision basePrecision growthConstant axesUsed baselinePrecision levelCount frameCount
    returnedVolume scalarPrefix parentLive : ℕ}
  {pcStack : Fin stackTapeCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {parentBank : Tapes (nodeTapes stackTapeCount roles) 2}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

section Parent
variable (rowCoordinate : Fin shape.chunk) (parentVisit : Visit shape.active leftBoundary (childExponent+2))
  (activeFitsAxes : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
  (parentReached : Reached (parent rowCoordinate parentVisit activeFitsAxes pair) rowCount logColumns metadataPrecision
    (childExponent+2) basePrecision growthConstant axesUsed baselinePrecision levelCount frameCount returnedVolume
    scalarPrefix parentLive pcStack stackOrigin savedCalls parentBank)
  (call : Networks.ComplexRecursiveCallSchema.Call) (headerStack liveStack : Fin stackTapeCount)

/-- Computed storage of this stopped branch's actual balanced parent return,
using the literal stopped bank, original older PC stack and installed result. -/
def returnStorage (olderWord : ℤ → Fin 6) (olderHead : ℤ) :=
  CompactComplexAlignedReturnedDormantFrames.capturedStorage parentReached
    (CompactComplexRolePhaseSite.role call.site)
    (stoppedBank rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack)
    olderWord olderHead headerStack liveStack (arity^(childExponent+1))
    rowCoordinate parentVisit activeFitsAxes pair
    (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns
      (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call) roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word
      (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call)))

/-- Ancestor frames remain settled on the actual returned storage computation
of the stopped child, including the original older associated PC stack. -/
theorem return_storage_settled
    (olderWord : ℤ → Fin 6) (olderHead : ℤ)
    (olderAssociated : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls olderWord olderHead)
    (ancestorSnapshot : Snapshot stackTapeCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack)
    (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack) (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack) :
    Settled ancestorSnapshot
      (returnStorage rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack olderWord olderHead)
      parentReached.aux :=
  CompactComplexAlignedReturnedDormantFrames.captured_storage_settled parentReached
    (CompactComplexRolePhaseSite.role call.site)
    (stoppedBank rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack)
    olderWord olderHead olderAssociated headerStack liveStack ancestorSnapshot parentSettled
    snapshotHeaderStack snapshotLiveStack snapshotPcStack headerDistinctLive pcDistinctHeader pcDistinctLive
    (arity^(childExponent+1)) rowCoordinate parentVisit activeFitsAxes pair
    (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns
      (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call) roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word
      (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call)))

/-- The stopped wrapper's numerical return and inverse-basis Reached
witnesses retain Settled on those same witnesses. Their literal physical
endpoint determines the storage and auxiliary fields; no returned frame
invariant or equality of a complete dormant bank is assumed. -/
theorem witnesses_settled
    (olderWord : ℤ → Fin 6) (olderHead : ℤ)
    (olderAssociated : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin savedCalls olderWord olderHead)
    (ancestorSnapshot : Snapshot stackTapeCount) (parentSettled : Settled ancestorSnapshot parentReached.storage parentReached.aux)
    (snapshotHeaderStack : ancestorSnapshot.headerStack=headerStack)
    (snapshotLiveStack : ancestorSnapshot.liveStack=liveStack) (snapshotPcStack : ancestorSnapshot.pcStack=pcStack)
    (headerDistinctLive : headerStack≠liveStack) (pcDistinctHeader : pcStack≠headerStack) (pcDistinctLive : pcStack≠liveStack)
    (restoredControl : Tapes 43 2) (restoredQueue : Tapes 1 2) (restoredTail : Tapes 22 2)
    (returnedReached : Reached (parent rowCoordinate parentVisit activeFitsAxes pair) rowCount logColumns metadataPrecision
      (childExponent+2) basePrecision growthConstant axesUsed baselinePrecision levelCount frameCount
      (returnedVolume+arity^(childExponent+1)) scalarPrefix (parentLive+arity^(childExponent+1)) pcStack stackOrigin savedCalls
      (canonical (returnedCaller parentReached (CompactComplexRolePhaseSite.role call.site) (arity^(childExponent+1))
        (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call)
        restoredControl restoredQueue parentReached.scalar restoredTail
        (returnStorage rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack olderWord olderHead))
        parentReached.aux))
    (afterBasisArray : CompactSpectatorVisitGeometry.Array shape (rowCount/roles) logColumns)
    (finalReached : Reached (parent rowCoordinate parentVisit activeFitsAxes pair) rowCount logColumns metadataPrecision
      (childExponent+2) basePrecision growthConstant axesUsed baselinePrecision levelCount frameCount
      (returnedVolume+arity^(childExponent+1)) scalarPrefix (parentLive+arity^(childExponent+1)) pcStack stackOrigin savedCalls
      (canonical (replacementCaller returnedReached (CompactComplexRolePhaseSite.role call.site) afterBasisArray) returnedReached.aux)) :
    Settled ancestorSnapshot returnedReached.storage returnedReached.aux ∧
    Settled ancestorSnapshot finalReached.storage finalReached.aux :=
  CompactComplexAlignedReturnedDormantFrames.captured_final_settled parentReached
    (CompactComplexRolePhaseSite.role call.site)
    (stoppedBank rowCoordinate parentVisit activeFitsAxes pair parentReached call headerStack liveStack)
    olderWord olderHead olderAssociated headerStack liveStack ancestorSnapshot parentSettled
    snapshotHeaderStack snapshotLiveStack snapshotPcStack headerDistinctLive pcDistinctHeader pcDistinctLive
    (arity^(childExponent+1)) (arity^(childExponent+1)) rowCoordinate parentVisit activeFitsAxes pair
    (CompactNativeRoleReservedBridge.sourcePayload shape (rowCount/roles) logColumns
      (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call) roles)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word
      (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call)))
    (stoppedResult rowCoordinate parentVisit activeFitsAxes pair parentReached call)
    restoredControl restoredQueue parentReached.scalar restoredTail returnedReached afterBasisArray finalReached

end Parent

end
end IntegerMultBounds.Machine.CompactComplexAlignedStoppedReturnedDormantFrames
