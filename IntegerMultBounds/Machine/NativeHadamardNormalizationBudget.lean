module

public import IntegerMultBounds.Machine.NativeHadamardNormalizationLifecycle

/-! The complete normalization lifecycle has one fixed native-volume allowance.
Original geometry pays descriptor construction; exponential address volume pays
binary division, and the true live ledger pays denominator copy/commit traffic.
No count-times-native-width normalization loop is introduced. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyAxisHeadersArithmetic
open NativeHadamardNormalizationHeaders
variable {shape : Shape}

private theorem count_cost (stage : Stage shape) (rows ell metadataPrecision live : ℕ) (rowsPositive : 0<rows) :
    scheduleCost countSchedule (geometryReady stage rows ell metadataPrecision live)≤
      2000*(count rows shape.bits ell+shape.bits+1) := by
  have twoPowerConstant : FixedBasePowerDescriptor.constant 2≤400 := by decide
  have weightedAddress := Nat.mul_le_mul_right (2^shape.bits) twoPowerConstant
  have weightedPolynomial := Nat.mul_le_mul_right (2^ell) twoPowerConstant
  have exponentVolume : 2^shape.bits≤count rows shape.bits ell := by
    unfold count
    have polynomialPositive : 0<2^ell := pow_pos (by decide) _
    nlinarith [Nat.le_mul_of_pos_right (2^shape.bits) polynomialPositive,
      Nat.le_mul_of_pos_left (2^shape.bits*2^ell) rowsPositive]
  have polynomialVolume : 2^ell≤count rows shape.bits ell := by
    unfold count
    have addressPositive : 0<2^shape.bits := pow_pos (by decide) _
    nlinarith [Nat.le_mul_of_pos_left (2^ell) addressPositive,
      Nat.le_mul_of_pos_left (2^shape.bits*2^ell) rowsPositive]
  have polynomialPairVolume : 2^shape.bits*2^ell≤count rows shape.bits ell := Nat.le_mul_of_pos_left _ rowsPositive
  have capacityFits : shape.H≤shape.bits := by unfold Shape.bits; omega
  have frontFits : shape.F≤shape.bits := by unfold Shape.bits; omega
  have backFits : shape.B≤shape.bits := by unfold Shape.bits; omega
  simp [countSchedule,scheduleCost,ButterflyAxisHeadersArithmetic.cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,geometryReady,CompactSpectatorLeafSetup.state,ActiveRepairRankHeadersCommands.put,
    Function.update]
  unfold count at *
  nlinarith

private theorem increase_cost (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    scheduleCost increaseSchedule (counted stage rows ell metadataPrecision live)≤20000*(stage.slots*stage.f+2)^2 := by
  let selectedCount := stage.slots*stage.f
  have divisionBudget := BinaryDescriptorDivision.cost_le (RecursiveChildQuotientsConstant.bits (selectedCount+1))
    (RecursiveChildQuotientsConstant.bits 2)
  have numeratorLength := ActiveRepairRankHeadersCommands.bits_length (selectedCount+1)
  have divisorLength : (RecursiveChildQuotientsConstant.bits 2).length≤3 := by decide
  have divisionBound : BinaryDescriptorDivision.cost (RecursiveChildQuotientsConstant.bits (selectedCount+1))
      (RecursiveChildQuotientsConstant.bits 2)≤32*((selectedCount+2)*(4*(selectedCount+2)+48))+710 := by
    nlinarith
  have oneCost : RecursiveChildQuotientsConstant.cost 1≤12 := by decide
  have twoCost : RecursiveChildQuotientsConstant.cost 2≤15 := by decide
  have increaseBound : increase stage≤selectedCount+1 := by unfold increase NativeHadamardNormalizationFactor.denominatorIncrease; dsimp [selectedCount]; omega
  simp [increaseSchedule,scheduleCost,ButterflyAxisHeadersArithmetic.cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,counted,original,NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,
    ActiveRepairRankHeadersCommands.put,Function.update]
  dsimp [selectedCount] at divisionBound
  rw [Nat.mul_comm stage.f stage.slots] at *
  dsimp only [selectedCount] at *
  generalize stage.slots*stage.f=selectedWidth at *
  nlinarith

private theorem target_cleanup_cost (stage : Stage shape) (rows ell metadataPrecision live : ℕ) :
    scheduleCost targetSchedule (scaled stage rows ell metadataPrecision live)+
      scheduleCost cleanupSchedule (targeted stage rows ell metadataPrecision live)≤
      1000*(count rows shape.bits ell+live+stage.slots*stage.f+1) := by
  have increaseBound : increase stage≤stage.slots*stage.f+1 := by unfold increase NativeHadamardNormalizationFactor.denominatorIncrease; omega
  simp [targetSchedule,cleanupSchedule,scheduleCost,ButterflyAxisHeadersArithmetic.cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,scaled,targeted,counted,original,NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,
    ActiveRepairRankHeadersCommands.put,Function.update]
  omega

private theorem square_power (dimension : ℕ) : (dimension+1)^2≤4*2^dimension := by
  induction dimension with
  | zero => norm_num
  | succ dimension inductionBound =>
    by_cases zeroDimension : dimension=0
    · subst dimension; norm_num
    by_cases unitDimension : dimension=1
    · subst dimension; norm_num
    have dimensionAtLeastTwo : 2≤dimension := by omega
    rw [show 2^(dimension+1)=2^dimension*2 from pow_succ 2 dimension]
    nlinarith

/-- All native-header setup and cleanup, stream traversal, true EOF returns,
source installation and live-denominator update share one fixed coefficient.
The input live bound is a genuine ledger condition, not a time certificate. -/
theorem cost_le_volume (stage : Stage shape) (rows ell metadataPrecision live wordWidth : ℕ)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (selectedFits : stage.slots*stage.f≤shape.bits)
    (liveFits : live≤count rows shape.bits ell*(2*(wordWidth+1))) :
    NativeHadamardNormalizationLifecycle.cost (rows:=rows) (ell:=ell) stage metadataPrecision live wordWidth≤
      20000000*(count rows shape.bits ell*(2*(wordWidth+1))) := by
  let coefficientCount := count rows shape.bits ell
  let volume := coefficientCount*(2*(wordWidth+1))
  have countPositive : 0<coefficientCount := by unfold coefficientCount count; positivity
  have countFits : coefficientCount≤volume := by dsimp [volume]; nlinarith
  have addressFits : 2^shape.bits≤coefficientCount := by
    unfold coefficientCount count
    have polynomialPositive : 0<2^ell := pow_pos (by decide) _
    nlinarith [Nat.le_mul_of_pos_right (2^shape.bits) polynomialPositive,
      Nat.le_mul_of_pos_left (2^shape.bits*2^ell) rowsPositive]
  have bitsFits : shape.bits≤coefficientCount := by have depthBound := FixedBasePowerDescriptor.depth_le_power 2 shape.bits (by decide); omega
  have squareBound : (stage.slots*stage.f+2)^2≤8*coefficientCount := by
    have square := square_power (shape.bits+1)
    rw [show 2^(shape.bits+1)=2^shape.bits*2 from pow_succ 2 shape.bits] at square
    have monotone := Nat.pow_le_pow_left (by omega : stage.slots*stage.f+2≤shape.bits+2) 2
    nlinarith
  have geometryBound := CompactSpectatorLeafSetupBudget.geometry_cost_eq shape rows ell metadataPrecision
    stage.rho stage.left stage.f stage.slots stage.right stage.source.val stage.target.val
    (by unfold Shape.H CompactGadgetReservationCapacity.capacity; positivity) chunkPositive
  have geometryBudget : scheduleCost CompactSpectatorLeafSetup.geometry
      (NativeEndpointCharacterPrepare.raw stage rows ell metadataPrecision)≤50000*(shape.bits+1) := by
    unfold NativeEndpointCharacterPrepare.raw
    rw [geometryBound]
    unfold Shape.bits
    omega
  have liveLength := ActiveRepairRankHeadersCommands.bits_length live
  have targetLength := ActiveRepairRankHeadersCommands.bits_length (live+increase stage)
  have countLength := ActiveRepairRankHeadersCommands.bits_length coefficientCount
  have increaseBound : increase stage≤stage.slots*stage.f+1 := by unfold increase NativeHadamardNormalizationFactor.denominatorIncrease; omega
  have countBudget := count_cost stage rows ell metadataPrecision live rowsPositive
  have increaseBudget := increase_cost stage rows ell metadataPrecision live
  have cleanupBudget := target_cleanup_cost stage rows ell metadataPrecision live
  unfold NativeHadamardNormalizationLifecycle.cost NativeHadamardNormalizationHeaders.cost setupCost prepareCost
  change _≤20000000*volume
  dsimp only [volume,coefficientCount,count] at *
  nlinarith


/-- Complete physical normalization with one fixed coefficient, exact source
readout and the true increased-denominator grid. The original Path derives both
the selected-width fit and signed guard; the live ledger pays descriptor traffic.
There is no count/target/execution/result or total-time premise. -/
theorem runs_from_path {rows ell left exponent levels frames returned : ℕ}
    (stage : Stage shape) (precision baseline growthConstant live pendingAxes : ℕ)
    (path : CompactRecursiveDependencyBudget.Path shape.active left exponent levels frames returned)
    (stageWidth : stage.slots*stage.f=CompactComplexRecursiveGeometry.arity^exponent)
    (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (pendingFits : pendingAxes≤shape.bits)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk)
    (coefficients : CompactSpectatorVisitGeometry.Array shape rows ell)
    (inputWidth : CompactSpectatorInheritedGrid.Width shape rows ell precision coefficients)
    (inputGrid : CompactSpectatorInheritedGrid.Grid shape rows ell precision live
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes) coefficients)
    (liveFits : live≤count rows shape.bits ell*(2*(CompactSpectatorInheritedGrid.half shape precision+2))) :
    let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits precision
    let bound := CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes
    HoareTime NativeHadamardNormalizationLifecycle.program
      (fun storage => storage=NativeHadamardNormalizationLifecycle.input stage metadataPrecision live coefficients)
      (fun storage => storage=NativeHadamardNormalizationLifecycle.output stage metadataPrecision live coefficients ∧
        CompactSpectatorInheritedGrid.Grid shape rows ell precision
          (live+NativeHadamardNormalizationFactor.denominatorIncrease (CompactComplexRecursiveGeometry.arity^exponent))
          (2*bound) (NativeHadamardNormalizationArray.result coefficients) ∧
        ∀ index,CompactSpectatorInheritedGrid.decoded shape rows ell precision
          (live+NativeHadamardNormalizationFactor.denominatorIncrease (CompactComplexRecursiveGeometry.arity^exponent))
          (NativeHadamardNormalizationArray.result coefficients) index=
          Networks.GaussianHadamardBridge.normalization^(CompactComplexRecursiveGeometry.arity^exponent)*
            CompactSpectatorInheritedGrid.decoded shape rows ell precision live coefficients index)
      (20000000*(count rows shape.bits ell*(2*(CompactSpectatorInheritedGrid.half shape precision+2)))) := by
  have selectedFits : stage.slots*stage.f≤shape.bits := by
    rw [stageWidth]
    have visitFits := path.visit.fits
    unfold Shape.bits
    nlinarith
  have runtimeBound := cost_le_volume stage rows ell
    (ButterflyIndependentGuardHeaders.reservation shape.bits precision) live
    (CompactSpectatorInheritedGrid.half shape precision+1) rowsPositive guardPositive axesPositive chunkPositive selectedFits
    (by simpa only [Nat.add_assoc] using liveFits)
  apply (NativeHadamardNormalizationLifecycle.runs_from_path stage precision baseline growthConstant live pendingAxes
    path stageWidth baselineFits dependencyFits pendingFits guardPositive axesPositive chunkPositive coefficients inputWidth
    inputGrid).consequence (fun _ equality => equality) _ (by simpa only [Nat.add_assoc] using runtimeBound)
  intro storage certificate
  rcases certificate with ⟨outputEqual,_,_,_,_,outputGrid,outputReadout⟩
  exact ⟨outputEqual,outputGrid,outputReadout⟩

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationBudget
