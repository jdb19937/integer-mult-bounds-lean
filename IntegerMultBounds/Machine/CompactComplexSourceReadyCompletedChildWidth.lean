import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedChildBoundary
import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedReturnInvariant

/-! Stored widths of the actual completed nonroot child. The sink corrections,
contraction, cyclic recombination and saved-call orientation preserve the width
already present in the child's Reached certificate. No output-width hypothesis
or recursive semantic equality is supplied. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedChildWidth
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorInheritedGrid (Width)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyCompletedChildBoundary (before sinkFamily joined result)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule

variable {stage : Stage sh} {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)

theorem before_width :
    ∀ a i,(before h a i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (before h a i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1 :=
  fun a i => h.width (CompactComplexScalarIntegerRows.wireIndex a) i

theorem sink_width (hslots : stage.slots=NativeEndpointCharacterRoles.arity) :
    ∀ j i,(sinkFamily h hslots j i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (sinkFamily h hslots j i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1 :=
  CompactComplexSourceReadyCorrectedFinal.family_width stage hslots ell metadataP
    (ButterflyGuard.halfWidth metadataP sh.bits+1) (before h) (before_width h)

theorem joined_width (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows) :
    ∀ i,(joined h hslots hd i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (joined h hslots hd i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1 := by
  apply CompactNativeRoleRecombine.width sh rows roles ell
    (ButterflyGuard.halfWidth metadataP sh.bits+1) hd
  intro j i
  simpa only [CompactComplexControllerExactReturn.contracted,NativeSignedGapScan.result_length]
    using sink_width h hslots j i

theorem joined_inherited_width (hslots : stage.slots=NativeEndpointCharacterRoles.arity)
    (hd : roles∣rows) (hmetadata : 2*sh.bits≤metadataP) :
    Width sh rows ell (metadataP-2*sh.bits) (joined h hslots hd) := by
  intro i
  simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq,
    CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq hmetadata]
    using joined_width h hslots hd i

/-- The actual completed child's result has inherited width, derived solely
from the child's Reached width and the metadata guard. -/
theorem result_width (hslots : stage.slots=NativeEndpointCharacterRoles.arity)
    (hd : roles∣rows) (hmetadata : 2*sh.bits≤metadataP)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    Width sh rows ell (metadataP-2*sh.bits) (result h hslots hd call) :=
  CompactComplexSourceReadyOrientationInvariants.oriented_width call sh rows ell
    (metadataP-2*sh.bits) (joined h hslots hd) (joined_inherited_width h hslots hd hmetadata)

theorem result_lengths (hslots : stage.slots=NativeEndpointCharacterRoles.arity)
    (hd : roles∣rows) (hmetadata : 2*sh.bits≤metadataP)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    ∀ i,(result h hslots hd call i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (result h hslots hd call i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1 := by
  intro i
  simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq,
    CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq hmetadata]
    using result_width h hslots hd hmetadata call i

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedChildWidth
