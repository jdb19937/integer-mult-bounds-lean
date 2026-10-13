module

public import IntegerMultBounds.Machine.CompactComplexAlignedReachedFinalReturn

/-! The actual completed root installs its semantic target into live storage7.
This literal descriptor is the one normalization must advance; an output grid
alone is not a proof of physical live-word readiness. Source phase replacement
preserves this readiness on the same returned bank. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationRootLive
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyWorkspace (tapes leafTapes)
open SharedPlacementAlphabet (setTape)
variable {stackCount : ℕ} {shape : Shape}

def slot : Fin (tapes stackCount roles) :=
  Fin.castAdd 10 (Fin.castAdd leafTapes
    (CompactComplexNonleafRoleChildBank.storage (s:=stackCount) (c:=roles) ⟨7,by omega⟩))

def Ready (live : ℕ) (outputBank : Tapes (tapes stackCount roles) 2) : Prop :=
  outputBank.head slot=1 ∧ outputBank.tape slot=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live)

theorem slot_ne_source : (slot (stackCount:=stackCount))≠CompactComplexSourceReadyOrientation.source := by
  intro equality
  have values := congrArg Fin.val equality
  simp only [slot,CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexSourceReadyOrientation.source,
    NativePolynomialConjugationWorkspace.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at values
  omega

theorem source_update (live : ℕ) (outputBank : Tapes (tapes stackCount roles) 2)
    (liveReady : Ready live outputBank) (word : ℤ → Fin 6) (head : ℤ) :
    Ready live (setTape outputBank CompactComplexSourceReadyOrientation.source word head) := by
  simpa only [Ready,setTape,Function.update_of_ne slot_ne_source] using liveReady

theorem endpoint_ready (stage : ActivePrefixStageParameters.Stage shape) (rows ell metadataPrecision live : ℕ)
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (payload : Tapes (1+roles) 2)
    (auxiliary : Tapes 2 2) (leaf : Tapes leafTapes 2) :
    Ready live (CompactComplexSourceReadyNonleafFinalPorts.endpoint shape rows ell metadataPrecision
      stage.rho stage.left stage.f stage.slots stage.right stage.source.val stage.target.val coefficients
      ((CompactComplexNativeCodecFrame.bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataPrecision)
        tail (CompactComplexControllerExactReturn.committed storage live) payload).append auxiliary) leaf) := by
  have retained := CompactComplexSourceReadyNonleafFinalPorts.storage shape rows ell metadataPrecision
    stage.rho stage.left stage.f stage.slots stage.right stage.source.val stage.target.val coefficients
    ((CompactComplexNativeCodecFrame.bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataPrecision)
      tail (CompactComplexControllerExactReturn.committed storage live) payload).append auxiliary) leaf ⟨7,by omega⟩
  have current := CompactComplexSpectatorTargetBank.old_bank control queue scalar
    (CompactComplexNativeCodec.raw stage rows ell metadataPrecision) tail
    (CompactComplexControllerExactReturn.committed storage live) payload ⟨7,by omega⟩
  have committedHead : (CompactComplexControllerExactReturn.committed storage live).head ⟨7,by omega⟩=1 := by
    simp [CompactComplexControllerExactReturn.committed,setTape]
  have committedTape : (CompactComplexControllerExactReturn.committed storage live).tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live) := by
    simp [CompactComplexControllerExactReturn.committed,setTape]
  unfold Ready
  constructor
  · apply retained.1.trans
    simpa only [Tapes.append,Fin.addCases_left] using current.1.trans committedHead
  · apply retained.2.trans
    simpa only [Tapes.append,Fin.addCases_left] using current.2.trans committedTape

section Root
variable {stage : ActivePrefixStageParameters.Stage shape}
    {rows ell metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
      dependencyLevels frameVolume returnedVolume scalarPrefix current : ℕ}
    {pcStack : Fin stackCount} {stackOrigin : ℤ}
    {nodeBank : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes stackCount roles) 2}
    (reached : CompactComplexSourceReadyReachedEventInvariant.Reached stage rows ell metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedVolume scalarPrefix current pcStack stackOrigin [] nodeBank)
    (slotsCorrect : stage.slots=NativeEndpointCharacterRoles.arity) (rowsDivisible : roles∣rows)

/-- The same reached root witness supplies the literal completed live word;
there is no post-root readiness hypothesis or reconstructed canonical bank. -/
theorem root_ready : Ready reached.targetValue
    (CompactComplexAlignedReachedFinalReturn.rootEndpoint reached slotsCorrect rowsDivisible) := by
  exact endpoint_ready stage rows ell metadataPrecision reached.targetValue
    (CompactComplexSourceReadyCompletedChildBoundary.joined reached slotsCorrect rowsDivisible)
    reached.control reached.queue reached.scalar reached.tail reached.storage
    (CompactComplexSourceReadyCompletedChildBoundary.returnedPayload reached slotsCorrect) reached.aux
    (SharedBank.empty leafTapes 2)


end Root

/-- The original root Path and initial live ledger pay the actual completed
network target in the existing native word volume. This discharges the caller
normalization budget from original hypotheses, not a post-root time envelope. -/
theorem network_live_volume {left childExponent levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active left (childExponent+2) levels frames returned)
    (baselineLive precision initialLive rows ell : ℕ)
    (baselineFits : baselineLive≤precision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (initialLedger : initialLive≤CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive levels frames returned (CompactFramedScalarGrid.rows 0).length)
    (rowsPositive : 0<rows) :
    CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)≤
      CompactNativeRoleTransferBudget.volume rows shape ell (ButterflyIndependentGuardHeaders.reservation shape.bits precision) := by
  have targetFits : CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)≤
      initialLive+2*CompactComplexRecursiveGeometry.arity^(childExponent+2) := by
    simp only [CompactComplexDenominatorPolicy.networkTarget,Nat.add_assoc]
    exact le_rfl
  have targetVolume := CompactComplexDenominatorCapacity.target_volume path CompactComplexDenominatorCapacity.scalarRows
    baselineLive precision (CompactFramedScalarGrid.rows 0).length initialLive
    (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rows ell baselineFits
    (CompactComplexDenominatorCapacity.actual_prefix 0) denominatorRoom initialLedger targetFits rowsPositive
  have volumeEquation : ButterflySpectatorGeometry.Size rows shape.bits (2^ell)*
      (2*(CompactSpectatorInheritedGrid.half shape precision+2))=
      CompactNativeRoleTransferBudget.volume rows shape ell (ButterflyIndependentGuardHeaders.reservation shape.bits precision) := by
    rw [CompactSpectatorVisitGeometry.coefficient_count]
    unfold CompactNativeRoleTransferBudget.volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner
      CompactNativeRoleHeaders.recordWidth ButterflyGuard.width CompactSpectatorInheritedGrid.half
      ButterflyIndependentGuardHeaders.reservation ButterflyGuard.halfWidth
    ring
  rwa [volumeEquation] at targetVolume

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationRootLive
