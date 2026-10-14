module

public import IntegerMultBounds.Machine.ActivePrefixEarlySequenceGlobal
public import IntegerMultBounds.Machine.ActivePrefixDirtyControlLateGlobal

/-! Both literal compact control schedules act on one unchanged original
active-target layout. Their actual global destinations and payload endpoints
are linked at the same address, and chronological early/later composition
moves the original payload through the two actual permutations. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ActivePrefixControlScheduleGlobal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters Address)
variable {shape : Shape} {rowCount : ℕ}

/-- Early and late programs use the same original physical address index.
This equality follows from their concrete index definitions. -/
theorem original_index (parameters : Parameters shape) (address : Address shape parameters rowCount) :
    ActivePrefixDirtyControlGlobalSwap.index shape parameters address=
      ActivePrefixEarlySequenceSemantics.index shape parameters address := rfl

/-- The complete early and later compact-control schedules, on the SAME
original layout and payload, realize their actual global permutations. The
chronological composition endpoint includes both actions on that same bank,
so no serialization bridge or separately prepared later input is assumed. -/
theorem destinations_actual (shape : Shape) (parameters : Parameters shape) (rowCount earlyOffset lateOffset : ℕ)
    (earlySourceFits : earlyOffset+parameters.f*parameters.q≤parameters.before)
    (lateSourceFits : lateOffset+parameters.f*parameters.q≤parameters.after)
    (digitsPositive : 0 < parameters.n) (radixAtLeastTwo : 2 ≤ parameters.b)
    (recordFits : shape.bits+1≤shape.payload) (rowsPositive : 0 < rowCount)
    (chunkPositive : 0 < shape.chunk) (axesPositive : 0 < shape.axes) (guardPositive : 0 < shape.guard)
    (originalPayload : Fin (rowCount*shape.recordWidth) → Bool) :
    let positiveRadixExponent := ActivePrefixEarlySequenceGlobal.positive shape parameters
    let earlyActual := ActiveRepairLayoutPermutation.earlyActual shape parameters.q parameters.b parameters.n
      parameters.before parameters.after rowCount parameters.rho earlyOffset (parameters.f*parameters.q)
      ActiveRepairRankHeadersData.SourceSide.before positiveRadixExponent
    let lateActual := ActiveRepairLayoutPermutation.lateActual shape parameters.q parameters.b parameters.n
      parameters.before parameters.after rowCount parameters.rho lateOffset (parameters.f*parameters.q)
      ActiveRepairRankHeadersData.SourceSide.after positiveRadixExponent
    let lateGeometry := ActivePrefixDirtyControlSequenceGeometry.geometry shape parameters rowCount lateOffset lateSourceFits
      digitsPositive radixAtLeastTwo recordFits rowsPositive chunkPositive axesPositive guardPositive
    let earlyOutput := ActivePrefixEarlySequenceData.result shape parameters earlyOffset earlySourceFits rowCount originalPayload
    let lateOutput := ActivePrefixDirtyControlSequenceData.later lateGeometry originalPayload
    ∀ originalAddress : Address shape parameters rowCount,
      ActivePrefixEarlySequenceSemantics.destination shape parameters earlyOffset originalAddress=earlyActual originalAddress ∧
      ActivePrefixDirtyControlGlobalSequence.destination shape parameters rowCount lateOffset lateSourceFits originalAddress=lateActual originalAddress ∧
      earlyOutput (ActivePrefixEarlySequenceSemantics.index shape parameters (earlyActual originalAddress))=
        originalPayload (ActivePrefixEarlySequenceSemantics.index shape parameters originalAddress) ∧
      lateOutput (ActivePrefixEarlySequenceSemantics.index shape parameters (lateActual originalAddress))=
        originalPayload (ActivePrefixEarlySequenceSemantics.index shape parameters originalAddress) ∧
      ActivePrefixDirtyControlSequenceData.later lateGeometry earlyOutput
        (ActivePrefixEarlySequenceSemantics.index shape parameters (lateActual (earlyActual originalAddress)))=
        originalPayload (ActivePrefixEarlySequenceSemantics.index shape parameters originalAddress) := by
  dsimp only
  intro originalAddress
  have earlyDestination := ActivePrefixEarlySequenceGlobal.destination_actual shape parameters earlyOffset originalAddress
  have lateDestination := ActivePrefixDirtyControlLateGlobal.destination_actual shape parameters lateOffset lateSourceFits originalAddress
  have earlyEndpoint := ActivePrefixEarlySequenceGlobal.entry shape parameters earlyOffset earlySourceFits originalPayload originalAddress
  have lateEndpoint := ActivePrefixDirtyControlLateGlobal.entry shape parameters lateOffset lateSourceFits
    digitsPositive radixAtLeastTwo recordFits rowsPositive chunkPositive axesPositive guardPositive originalPayload originalAddress
  have chronologicalEndpoint := ActivePrefixDirtyControlLateGlobal.entry shape parameters lateOffset lateSourceFits
    digitsPositive radixAtLeastTwo recordFits rowsPositive chunkPositive axesPositive guardPositive
    (ActivePrefixEarlySequenceData.result shape parameters earlyOffset earlySourceFits rowCount originalPayload)
    (ActiveRepairLayoutPermutation.earlyActual shape parameters.q parameters.b parameters.n parameters.before parameters.after
      rowCount parameters.rho earlyOffset (parameters.f*parameters.q) ActiveRepairRankHeadersData.SourceSide.before
      (ActivePrefixEarlySequenceGlobal.positive shape parameters) originalAddress)
  simp only [original_index] at lateEndpoint chronologicalEndpoint
  exact ⟨earlyDestination,lateDestination,earlyEndpoint,lateEndpoint,chronologicalEndpoint.trans earlyEndpoint⟩

end
end IntegerMultBounds.Machine.ActivePrefixControlScheduleGlobal
