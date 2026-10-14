module

public import IntegerMultBounds.Machine.CompactActualStageInputs
public import IntegerMultBounds.Machine.CompactActualNativeBudget

@[expose] public section
namespace IntegerMultBounds.Machine.CompactActualStagePadding
noncomputable section
open Sizes
open CompactGlobalRowPadding CompactReservationCutoff
open CompactActualStageAllowance (actualShape)
open CompactActualStageGeometry (Ready)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageHeadersData (Order)

def paddingConstant (roleCount arity : ℕ) :=
  2*(CompactGlobalRowInitialBudget.headerConstant roleCount arity+2415)

structure Prepared (roleCount arity inputSize selectedAxes payload depthIndex : ℕ) : Prop where
  reservationFits : CompactReservationGrowth.reserved roleCount arity inputSize < selectedAxes
  activeHalf : selectedAxes ≤ 2*active roleCount arity inputSize selectedAxes
  rowsPositive : 0 < rowsAt roleCount arity (d inputSize) (K inputSize) depthIndex
  roleDivisor : roleCount^(depth arity (d inputSize)-depthIndex) ∣
    rowsAt roleCount arity (d inputSize) (K inputSize) depthIndex
  rowBound : rowsAt roleCount arity (d inputSize) (K inputSize) depthIndex ≤
    2*originalRows roleCount arity (d inputSize) (K inputSize)
  noRepadding : depthIndex < depth arity (d inputSize) →
    Compact.Layout.paddedRows (rowsAt roleCount arity (d inputSize) (K inputSize) depthIndex) roleCount =
      rowsAt roleCount arity (d inputSize) (K inputSize) depthIndex
  reservedVolume :
    2^(selectedAxes*K inputSize)*payload ≤
      initialRows roleCount arity (d inputSize) (K inputSize)*(actualShape inputSize roleCount arity selectedAxes payload).recordWidth ∧
    initialRows roleCount arity (d inputSize) (K inputSize)*(actualShape inputSize roleCount arity selectedAxes payload).recordWidth ≤
      2*(2^(selectedAxes*K inputSize)*payload)
  paddingCost : CompactGlobalRowInitialRun.cost roleCount arity (d inputSize) selectedAxes (K inputSize) payload ≤
    paddingConstant roleCount arity*(2^(selectedAxes*K inputSize)*payload)
  stageReady : ∀ stage : Stage (actualShape inputSize roleCount arity selectedAxes payload),
    Ready (actualShape inputSize roleCount arity selectedAxes payload) stage
      (rowsAt roleCount arity (d inputSize) (K inputSize) depthIndex)
  stageAllowances : ∀ (stage : Stage (actualShape inputSize roleCount arity selectedAxes payload)) (order : Order),
    let input := CompactActualStageInputs.inputs stage
      (rowsAt roleCount arity (d inputSize) (K inputSize) depthIndex) (stageReady stage)
    let descriptors := ActivePrefixStageFullData.descriptors order input
    (ActiveRepairLayoutRecordsHeadersData.geom descriptors).addressBits+1 ≤ payload ∧
      VaryingControlRepairDensity.earlyDensity (K inputSize) (4*CompactScalarAllowances.guardLog inputSize+6) (stage.f-1)*
        ((ActiveRepairLayoutRecordsHeadersData.geom descriptors).addressBits+1) ≤ 1 ∧
      VaryingControlRepairDensity.lateDensity (K inputSize) (4*CompactScalarAllowances.guardLog inputSize+6) (stage.f-1)*
        ((ActiveRepairLayoutRecordsHeadersData.geom descriptors).addressBits+1) ≤ 1
  nativeChargedVolume : ∀ (wordWidth widthFactor : ℕ), wordWidth ≤ widthFactor*b inputSize →
    rowsAt roleCount arity (d inputSize) (K inputSize) depthIndex*
      (actualShape inputSize roleCount arity selectedAxes (CompactActualNativeWidth.payload inputSize wordWidth)).recordWidth*
      roleCount^depthIndex ≤ 12*(widthFactor+1)*CompactActualNativeBudget.volume inputSize selectedAxes

theorem eventually_ready_allowances (roleCount arity : ℕ) (rolesPositive : 2 ≤ roleCount) (arityPositive : 2 ≤ arity)
    (arityFits : arity ≤ roleCount) :
    0 < paddingConstant roleCount arity ∧
      ∀ᶠ inputSize : ℕ in Filter.atTop,
        cutoff roleCount arity inputSize ≤ d inputSize ∧
        ∀ (selectedAxes payload depthIndex : ℕ), cutoff roleCount arity inputSize ≤ selectedAxes →
          selectedAxes ≤ d inputSize → 6*b inputSize*2^ℓ inputSize ≤ payload →
          depthIndex ≤ depth arity (d inputSize) → Prepared roleCount arity inputSize selectedAxes payload depthIndex := by
  constructor
  · unfold paddingConstant
    omega
  filter_upwards [CompactActualStageGeometry.eventually_ready roleCount arity rolesPositive arityPositive,
    CompactActualStageInputs.eventually_allowances roleCount arity rolesPositive arityPositive,
    eventually_cutoff_le_dimension roleCount arity arityPositive] with inputSize ready allowances cutoffFits
  refine ⟨cutoffFits, ?_⟩
  intro selectedAxes payload depthIndex selectedLower selectedUpper payloadLower depthFits
  have cutoffReady := cutoff_ready roleCount arity inputSize selectedAxes rolesPositive arityPositive selectedLower
  have reservationFits := (nonfallback roleCount arity inputSize selectedAxes cutoffReady.1).2.2
  have rolesNonzero : 0 < roleCount := by omega
  have chunkPositive := positive_chunk inputSize
  have payloadPositive : 0 < payload := by
    have precisionPositive := one_le_b inputSize
    have minimumPositive : 0 < 6*b inputSize*2^ℓ inputSize := by positivity
    omega
  let stageReady := fun stage => ready selectedAxes payload depthIndex selectedLower selectedUpper payloadLower depthFits stage
  refine {
    reservationFits := cutoffReady.1
    activeHalf := cutoffReady.2
    rowsPositive := rowsAt_positive roleCount arity (d inputSize) (K inputSize) depthIndex rolesNonzero chunkPositive depthFits
    roleDivisor := rowsAt_divisible roleCount arity (d inputSize) (K inputSize) depthIndex rolesNonzero chunkPositive depthFits
    rowBound := rowsAt_le_twice_original roleCount arity (d inputSize) (K inputSize) depthIndex rolesNonzero chunkPositive
    noRepadding := fun beforeLeaf => no_repadding roleCount arity (d inputSize) (K inputSize) depthIndex rolesNonzero chunkPositive beforeLeaf
    reservedVolume := CompactGlobalReservation.padded_volume roleCount arity (d inputSize) selectedAxes
      (4*CompactScalarAllowances.guardLog inputSize+6) (K inputSize) payload rolesNonzero chunkPositive reservationFits
    paddingCost := CompactReservationCutoff.padding_cost roleCount arity inputSize selectedAxes payload rolesPositive arityPositive
      arityFits cutoffReady.1 selectedUpper payloadPositive
    stageReady := stageReady
    stageAllowances := ?_
    nativeChargedVolume := ?_ }
  · intro stage order
    exact allowances selectedAxes payload depthIndex selectedLower selectedUpper payloadLower stage (stageReady stage) order
  · intro wordWidth widthFactor widthBound
    exact CompactActualNativeBudget.charged_volume roleCount arity inputSize selectedAxes depthIndex wordWidth widthFactor
      rolesPositive arityPositive selectedLower depthFits widthBound

end
end IntegerMultBounds.Machine.CompactActualStagePadding
