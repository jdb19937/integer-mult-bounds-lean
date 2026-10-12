module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedChildTensor
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingStoppedGrid
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingChildEventSemantics

/-! The literal stopped result of the actual forward Reached witness supplies
the original parent's child tensor semantics after counted sibling calls.
Forward width/grid and the signed guard derive from real readiness and the
original entry Path, so no child tensor callback remains in this base case. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingStoppedChildSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedReturnInvariant (roleData returnedCaller returnedData)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData)
open CompactComplexSourceReadyChildEventSemantics (ChildTensor stored)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexCorrectedStoppedChildGridSemantics (installed)
open CompactComplexChildHeadersData (parent)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule

section Parent
variable {stackCount : ℕ} {shape : Shape}
    {nodeLeft childExponent dependencyLevels frameVolume entryReturned eventIndex : ℕ}
    {parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant baselineLive scalarPrefix parentLive : ℕ}
    (phaseCoordinate : Fin shape.chunk)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
      dependencyLevels frameVolume entryReturned)
    (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin stackCount} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes stackCount roles) 2}
    (parentReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair)
      parentRows polynomialExponent metadataPrecision (childExponent+2) baselinePrecision growthConstant 0
      baselineLive dependencyLevels frameVolume (returnedCursor entryReturned eventIndex (arity^(childExponent+1)))
      scalarPrefix parentLive pcStack origin calls parentBank)
    (call : Networks.ComplexRecursiveCallSchema.Call)

/-- The computed leaf of the actual forward-basis readiness witness proves
ChildTensor for the original parent data at all rows, polynomial indices and
global addresses. Every numerical input is derived rather than supplied. -/
theorem child_tensor (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (childRowsPositive : 0<parentRows/roles)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : arity^(childExponent+1)≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk) :
    let selectedRole := CompactComplexRolePhaseSite.role call.site
    let forwardArray := basisArray (parent phaseCoordinate entryPath.visit activeFits pair)
      (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive parentSlots
      (CompactComplexRolePhaseSite.pc call.site) false
      (parentReached.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
    ∀ forwardReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair)
      parentRows polynomialExponent metadataPrecision (childExponent+2) baselinePrecision growthConstant 0
      baselineLive dependencyLevels frameVolume (returnedCursor entryReturned eventIndex (arity^(childExponent+1)))
      scalarPrefix parentLive pcStack origin calls
      (canonical (replacementCaller parentReached selectedRole forwardArray) parentReached.aux),
      forwardReached.data=replacementData parentReached selectedRole forwardArray →
    ChildTensor phaseCoordinate entryPath.visit activeFits pair (parentRows/roles) polynomialExponent
      metadataPrecision guardPositive guardFitsChunk childRowsPositive call (metadataPrecision-2*shape.bits)
      parentLive (arity^(childExponent+1)) parentReached.data
      (installed call (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
        phaseCoordinate (Visit.child entryPath.visit call.slot)
        (oriented call (roleData forwardReached selectedRole))) := by
  dsimp only
  intro forwardReached forwardDataEquation
  have selectedIndex : CompactComplexScalarRolePorts.roleIndex.symm
      (CompactComplexRolePhaseSite.role call.site)=CompactComplexScalarIntegerRows.wireIndex call.role := by
    rw [←CompactComplexSourceReadyChildEventSemantics.selected_role_index call,Equiv.symm_apply_apply]
  have selectedForward : roleData forwardReached (CompactComplexRolePhaseSite.role call.site)=
      basisArray (parent phaseCoordinate entryPath.visit activeFits pair)
        (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive parentSlots
        (CompactComplexRolePhaseSite.pc call.site) false
        (parentReached.data (CompactComplexScalarIntegerRows.wireIndex call.role)) := by
    simp only [roleData,forwardDataEquation,replacementData,Function.update_self,selectedIndex]
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  have forwardWidth := CompactComplexSourceReadyReachedReturnInvariant.role_width forwardReached metadataFits
    (CompactComplexRolePhaseSite.role call.site)
  have forwardGrid := CompactComplexSourceReadyReachedReturnInvariant.role_grid forwardReached metadataFits
    (CompactComplexRolePhaseSite.role call.site)
  rw [selectedForward] at forwardWidth forwardGrid
  have childFitsNode : arity^(childExponent+1)≤arity^(childExponent+2) :=
    Nat.pow_le_pow_right (by decide : 0<arity) (by omega)
  have signedGuard := CompactComplexSourceReadySiblingStoppedGrid.stopped_guard entryPath
    eventIndex (arity^(childExponent+1)) scalarPrefix baselinePrecision growthConstant 0
    (arity^(childExponent+1)) metadataPrecision childFitsNode activePositive precisionReserve
    (by simpa only [Nat.zero_add] using axesFit) growthReserve chunkRoom
  rw [selectedForward]
  exact CompactComplexSourceReadyStoppedChildTensor.child_tensor phaseCoordinate entryPath.visit activeFits pair
    (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive call
    (metadataPrecision-2*shape.bits) parentLive
    (CompactFramedScalarGrid.bound scalarPrefix
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
        (frameVolume+2*returnedCursor entryReturned eventIndex (arity^(childExponent+1))+0)))
    parentReached.data forwardWidth forwardGrid signedGuard

/-- Actual forward, restored and inverse readiness witnesses for the literal
stopped result realize the original decoded child instruction. No supplied
tensor equality remains: child_tensor derives it from the forward witness. -/
theorem reached_event_semantics (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (childRowsPositive : 0<parentRows/roles)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : arity^(childExponent+1)≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (aux : Tapes 2 2) :
    let selectedRole := CompactComplexRolePhaseSite.role call.site
    let forwardArray := basisArray (parent phaseCoordinate entryPath.visit activeFits pair)
      (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive parentSlots
      (CompactComplexRolePhaseSite.pc call.site) false
      (parentReached.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
    ∀ forwardReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair)
      parentRows polynomialExponent metadataPrecision (childExponent+2) baselinePrecision growthConstant 0
      baselineLive dependencyLevels frameVolume (returnedCursor entryReturned eventIndex (arity^(childExponent+1)))
      scalarPrefix parentLive pcStack origin calls
      (canonical (replacementCaller parentReached selectedRole forwardArray) parentReached.aux),
      forwardReached.data=replacementData parentReached selectedRole forwardArray →
    let childResult := installed call (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
      phaseCoordinate (Visit.child entryPath.visit call.slot) (oriented call (roleData forwardReached selectedRole))
    ∀ restoredReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair)
      parentRows polynomialExponent metadataPrecision (childExponent+2) baselinePrecision growthConstant 0
      baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
      (parentLive+arity^(childExponent+1)) pcStack origin calls
      (canonical (returnedCaller forwardReached selectedRole (arity^(childExponent+1)) childResult
        control queue scalar tail storage) aux),
      restoredReached.data=returnedData forwardReached selectedRole (arity^(childExponent+1)) childResult →
    let inverseArray := basisArray (parent phaseCoordinate entryPath.visit activeFits pair)
      (parentRows/roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk childRowsPositive parentSlots
      (CompactComplexRolePhaseSite.pc call.site) true
      (restoredReached.data (CompactComplexScalarRolePorts.roleIndex.symm selectedRole))
    ∀ finalReached : Reached (parent phaseCoordinate entryPath.visit activeFits pair)
      parentRows polynomialExponent metadataPrecision (childExponent+2) baselinePrecision growthConstant 0
      baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex (arity^(childExponent+1))+arity^(childExponent+1)) scalarPrefix
      (parentLive+arity^(childExponent+1)) pcStack origin calls
      (canonical (replacementCaller restoredReached selectedRole inverseArray) restoredReached.aux),
      finalReached.data=replacementData restoredReached selectedRole inverseArray →
    ∀ (row : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent))
      (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
      stored phaseCoordinate entryPath.visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
        (parentLive+arity^(childExponent+1)) finalReached.data row polynomialIndex globalAnchor=
      Networks.FramedFactorExecution.run
        [CompactComplexActualEventNetwork.childInstruction (arity^(childExponent+1)) call]
        (stored phaseCoordinate entryPath.visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
          parentLive parentReached.data row polynomialIndex globalAnchor) := by
  dsimp only
  intro forwardReached forwardDataEquation restoredReached restoredDataEquation finalReached finalDataEquation
    row polynomialIndex globalAnchor
  have stoppedTensor := child_tensor phaseCoordinate entryPath activeFits pair parentReached call
    guardPositive guardFitsChunk childRowsPositive parentSlots activePositive precisionReserve axesFit growthReserve chunkRoom
    forwardReached forwardDataEquation
  have childFitsNode : arity^(childExponent+1)≤arity^(childExponent+2) :=
    Nat.pow_le_pow_right (by decide : 0<arity) (by omega)
  exact CompactComplexSourceReadySiblingChildEventSemantics.reached_child_semantics parentReached
    phaseCoordinate entryPath.visit activeFits pair rfl rfl call guardPositive guardFitsChunk childRowsPositive parentSlots
    entryPath childFitsNode activePositive precisionReserve (by simpa only [Nat.zero_add] using axesFit)
    growthReserve chunkRoom
    (installed call (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
      phaseCoordinate (Visit.child entryPath.visit call.slot)
      (oriented call (roleData forwardReached (CompactComplexRolePhaseSite.role call.site))))
    control queue scalar tail storage aux stoppedTensor forwardReached forwardDataEquation
    restoredReached restoredDataEquation finalReached finalDataEquation row polynomialIndex globalAnchor

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingStoppedChildSemantics
