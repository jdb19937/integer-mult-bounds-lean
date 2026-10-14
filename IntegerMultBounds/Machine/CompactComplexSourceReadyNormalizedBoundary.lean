module

public import IntegerMultBounds.Machine.CompactComplexSinkSliceValues
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRoleRejoin
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedChildBoundary
public import IntegerMultBounds.Machine.CompactComplexAlignedPoppedReturnReadiness

/-! The normalized tensor array uses the exact cyclic role order of physical
finalization. Its post-oriented source word is the literal completed child
boundary's source, before the genuine saved-PC pop. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedBoundary
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyReachedStoppedNodeNormalizedValues (normalized)
open CompactComplexSourceReadyCompletedChildBoundary (joined completed result)
variable {stackCount : ℕ} {shape : CompactGadgetReservationShape.Shape}
  {stage : ActivePrefixStageParameters.Stage shape}
  {rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume returnedCount scalarPrefix currentLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  {actualBank : Tapes (nodeTapes stackCount roles) 2}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites CompactComplexCompletedLiveLower.schedule

/-- Both serialization orders are joined through the actual role-port adapter. -/
theorem joined_eq_normalized
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedCount scalarPrefix currentLive pcStack origin savedCalls actualBank)
    (stageSlots : stage.slots=NativeEndpointCharacterRoles.arity) (rolesDivide : roles∣rowCount) :
    joined reached stageSlots rolesDivide =
      normalized rowCount polynomialExponent currentLive reached.targetValue rolesDivide
        (CompactComplexSinkSliceValues.scalarOutputRoles stage stageSlots metadataPrecision reached.data) := by
  unfold joined normalized CompactComplexSourceReadyCompletedChildBoundary.sinkFamily
    CompactComplexSinkSliceValues.scalarOutputRoles CompactComplexSourceReadyCompletedChildBoundary.before
  congr 1
  funext rolePort
  rw [Equiv.apply_symm_apply]

/-- The exact normalized array, after the saved call's orientation, is the
source word of the same completed physical bank used by real parent return. -/
theorem completed_normalized_source
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedCount scalarPrefix currentLive pcStack origin savedCalls actualBank)
    (stageSlots : stage.slots=NativeEndpointCharacterRoles.arity) (rolesDivide : roles∣rowCount)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    (completed reached stageSlots rolesDivide call).head
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles)))=0 ∧
    (completed reached stageSlots rolesDivide call).tape
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles)))=
      CompactSpectatorLeafAxis.word (CompactComplexSourceReadyOrientationInvariants.oriented call
        (normalized rowCount polynomialExponent currentLive reached.targetValue rolesDivide
          (CompactComplexSinkSliceValues.scalarOutputRoles stage stageSlots metadataPrecision reached.data))) := by
  have sourceReady := CompactComplexSourceReadyCompletedChildBoundary.completed_source reached stageSlots rolesDivide call
  unfold result at sourceReady
  rw [joined_eq_normalized] at sourceReady
  exact sourceReady

/-- Popping the genuine saved-PC port retains the exact normalized source. -/
theorem popped_normalized_source
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedCount scalarPrefix currentLive pcStack origin savedCalls actualBank)
    (stageSlots : stage.slots=NativeEndpointCharacterRoles.arity) (rolesDivide : roles∣rowCount)
    (call : Networks.ComplexRecursiveCallSchema.Call) (older : ℤ → Fin 6) (top : ℤ) :
    let returnedBank := CompactComplexAlignedPoppedReturnReadiness.popped
      (completed reached stageSlots rolesDivide call) pcStack older top
    returnedBank.head
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles)))=0 ∧
    returnedBank.tape
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles)))=
      CompactSpectatorLeafAxis.word (CompactComplexSourceReadyOrientationInvariants.oriented call
        (normalized rowCount polynomialExponent currentLive reached.targetValue rolesDivide
          (CompactComplexSinkSliceValues.scalarOutputRoles stage stageSlots metadataPrecision reached.data))) := by
  have sourceDifferent :
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles)) ≠
        CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack := by
    intro portsEqual
    apply CompactComplexSourceReadyCompletedChildBoundary.storage_ne_source (s:=stackCount) (c:=roles)
      (Fin.natAdd 10 pcStack)
    change Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles)) =
      Fin.castAdd 7 (CompactComplexSourceReadyCompletedChildBoundary.storageSlot
        (s:=stackCount) (c:=roles) (Fin.natAdd 10 pcStack)) at portsEqual
    exact (Fin.castAdd_injective _ _ portsEqual).symm
  dsimp only
  simpa only [CompactComplexAlignedPoppedReturnReadiness.popped,SharedPlacementAlphabet.setTape,
    Function.update_of_ne sourceDifferent] using
    completed_normalized_source reached stageSlots rolesDivide call

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedBoundary
