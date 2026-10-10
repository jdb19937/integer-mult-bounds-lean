import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedBasisInvariant
import IntegerMultBounds.Machine.CompactComplexBasisTensorConjugation

/-! The actual selected-role coefficient permutation and its decoded values
follow the literal ambient basis coordinate map. All equalities below use the
computed native row destination; no local input-alignment premise is supplied. -/
namespace IntegerMultBounds.Machine.CompactComplexActualBasisCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageNativePairCoordinates (start)
open CompactComplexSourceReadyReachedBasisInvariant (cardinality polynomial basisArray)
open CompactAllAxisPhaseDispatch (count edge)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexBasisTensorConjugation (coordinateMap)

section Native
variable {sh : Shape} (d : ActivePrefixStageFullData.Inputs sh)
    (hslots : d.stage.slots=25^3) (pc : Fin count)

/-- Every native row coordinate is the actual original basis map, independently
in each parent column. The physical row ordinal is the computed destination. -/
theorem destination_coordinates (r : Fin (ActivePrefixStageTripleWords.count d))
    (axis : Fin d.stage.f) :
    CompactComplexPhasePhysical.originalCoordinates d hslots
      (start d (ActivePrefixStageNativePairCoordinates.run d (CompactNativeConjugatedPhase.ops d hslots pc) r)) axis=
    coordinateMap (edge pc)
      (CompactComplexPhasePhysical.originalCoordinates d hslots (start d r) axis) := by
  have h := CompactComplexPhasePhysical.coordinate_run d hslots (edge pc) (start d r) axis
  rw [CompactComplexPhasePhysical.destination,ActivePrefixStageNativePairCoordinates.run_start] at h
  rw [CompactComplexBasisTensorConjugation.coordinateMap_word] at h
  funext i
  have hi := congrFun h (finCongr hslots.symm i)
  simpa only [CompactComplexPhasePhysical.originalCoordinates,Function.comp_apply,
    CompactNativeConjugatedPhase.ops,finCongr_apply,Fin.cast_cast,Fin.cast_eq_self] using hi

/-- The inverse map recovers the original coordinates at that same literal
output row, as required by the pullback convention of tensor conjugation. -/
theorem destination_inverse_coordinates (r : Fin (ActivePrefixStageTripleWords.count d))
    (axis : Fin d.stage.f) :
    (coordinateMap (edge pc)).symm
      (CompactComplexPhasePhysical.originalCoordinates d hslots
        (start d (ActivePrefixStageNativePairCoordinates.run d (CompactNativeConjugatedPhase.ops d hslots pc) r)) axis)=
    CompactComplexPhasePhysical.originalCoordinates d hslots (start d r) axis := by
  rw [destination_coordinates,LinearEquiv.symm_apply_apply]

end Native

section Arrays
variable {sh : Shape} (stage : Stage sh) (m ell metadataP : ℕ)
    (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m)

def coefficientIndex
    (r : Fin (ActivePrefixStageTripleWords.count (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm)))
    (j : Fin (2^ell)) : Fin (ButterflySpectatorGeometry.Size m sh.bits (2^ell)) :=
  Fin.cast (cardinality stage m ell metadataP hG hGK hm) (finProdFinEquiv (r,j))

/-- A physical forward basis pass retains the literal stored coefficient at
its computed row destination, including the immutable polynomial index. -/
theorem basisArray_destination (hslots : stage.slots=25^3) (pc : Fin count)
    (f : Array sh m ell)
    (r : Fin (ActivePrefixStageTripleWords.count (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm)))
    (j : Fin (2^ell)) :
    basisArray stage m ell metadataP hG hGK hm hslots pc false f
      (coefficientIndex stage m ell metadataP hG hGK hm
        (ActivePrefixStageNativePairCoordinates.run (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm)
          (CompactNativeConjugatedPhase.ops (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm) hslots pc) r) j)=
    f (coefficientIndex stage m ell metadataP hG hGK hm r j) := by
  unfold basisArray coefficientIndex
  simp only [Fin.cast_cast,Fin.cast_refl,ActivePrefixStageNativePolynomial.flattenArray,
    id_eq,Equiv.symm_apply_apply]
  change ActivePrefixStageNativePolynomialWord.word _
    (CompactNativeConjugatedPhase.ops _ hslots pc) _
    (ActivePrefixStageNativePairCoordinates.run _ (CompactNativeConjugatedPhase.ops _ hslots pc) r) j=_
  rw [ActivePrefixStageNativePolynomialWord.word_destination]
  rfl

/-- Decoding the actual serialized basis output gives exactly the original
value at its native destination, at every inherited denominator. -/
theorem decoded_destination (hslots : stage.slots=25^3) (pc : Fin count)
    (f : Array sh m ell) (q n : ℕ)
    (r : Fin (ActivePrefixStageTripleWords.count (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm)))
    (j : Fin (2^ell)) :
    CompactSpectatorInheritedGrid.decoded sh m ell q n
      (basisArray stage m ell metadataP hG hGK hm hslots pc false f)
      (coefficientIndex stage m ell metadataP hG hGK hm
        (ActivePrefixStageNativePairCoordinates.run (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm)
          (CompactNativeConjugatedPhase.ops (CompactComplexSourceReadyReachedBasisInvariant.input stage m ell metadataP hG hGK hm) hslots pc) r) j)=
    CompactSpectatorInheritedGrid.decoded sh m ell q n f
      (coefficientIndex stage m ell metadataP hG hGK hm r j) := by
  unfold CompactSpectatorInheritedGrid.decoded
  rw [basisArray_destination]

end Arrays
end
end IntegerMultBounds.Machine.CompactComplexActualBasisCoordinates
