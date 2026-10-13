module

public import IntegerMultBounds.Machine.NativeHadamardPhaseOutputBank

/-! The actual completed-root grid, including its paid two-pass numerator
growth, supplies output-phase signed guards in the unchanged reservation. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardPhaseCompletedGrid
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Grid Width half decoded)
open CompactComplexRecursiveGeometry (arity Visit)
variable {shape : Shape} {rows ell left exponent levels frames returned : ℕ}

theorem double_visit_le_bits (visit : Visit shape.active left exponent) (twoFits : 2≤shape.chunk) :
    2*arity^exponent≤shape.bits := by
  have visitFits := visit.fits
  have activeBits := Nat.mul_le_mul_left shape.active twoFits
  unfold Shape.bits
  nlinarith

/-- The output's actual two-pass growth fits the same stored signed fields.
No post-root numerical-safety assertion is assumed. -/
theorem signed_guards_from_growth (precision baseline growthConstant denominator pendingAxes : ℕ)
    (path : CompactRecursiveDependencyBudget.Path shape.active left exponent levels frames returned)
    (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (pendingFits : pendingAxes≤shape.bits) (input : Array shape rows ell)
    (inputGrid : Grid shape rows ell precision denominator
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes) input)
    (index : Fin (rows*(2^shape.bits*2^ell))) :
    |ButterflySigned.signedValue (half shape precision) (input index).1|<(2^(half shape precision) : ℕ) ∧
      |ButterflySigned.signedValue (half shape precision) (input index).2|<(2^(half shape precision) : ℕ) := by
  have numeratorBound := ButterflyGuard.represented_bound _ _ denominator _ (inputGrid index)
  have guard := CompactSpectatorInheritedGrid.guard_from_path shape precision path baseline growthConstant pendingAxes
    baselineFits dependencyFits pendingFits
  have boundFits : CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes <
      2^(half shape precision) := by omega
  have signedFits : (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes : ℤ) <
      (2^(half shape precision) : ℕ) := by exact_mod_cast boundFits
  exact ⟨numeratorBound.1.trans_lt signedFits,numeratorBound.2.trans_lt signedFits⟩

/-- The physically emitted output-phase word retains the true completed
denominator and bounded grid, including all original network numerator growth. -/
theorem grid_from_growth (stage : ActivePrefixStageParameters.Stage shape)
    (precision baseline growthConstant denominator pendingAxes : ℕ)
    (path : CompactRecursiveDependencyBudget.Path shape.active left exponent levels frames returned)
    (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (pendingFits : pendingAxes≤shape.bits) (input : Array shape rows ell)
    (inputWidth : Width shape rows ell precision input)
    (inputGrid : Grid shape rows ell precision denominator
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes) input) :
    Grid shape rows ell precision denominator
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes)
      (NativeHadamardPhaseOriginal.result stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) input) := by
  intro index
  rw [decoded,NativeHadamardPhaseOriginal.signed_decoded]
  · exact Networks.GaussianPrecision.bounded_I_pow_mul _ (inputGrid index)
  · intro coefficient
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth coefficient
  · exact fun coefficient => signed_guards_from_growth precision baseline growthConstant denominator pendingAxes path
      baselineFits dependencyFits pendingFits input inputGrid coefficient

/-- Exact output tensor correction at the original root address, derived from
the actual completed grid rather than an assumed corrected-output assertion. -/
theorem decoded_at_node_from_growth {nodeExponent : ℕ} (phaseCoordinate : Fin shape.chunk)
    (path : CompactRecursiveDependencyBudget.Path shape.active left (nodeExponent+1) levels frames returned)
    (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (precision baseline growthConstant denominator pendingAxes : ℕ) (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (pendingFits : pendingAxes≤shape.bits) (input : Array shape rows ell)
    (inputWidth : Width shape rows ell precision input)
    (inputGrid : Grid shape rows ell precision denominator
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes) input)
    (rawRow : Fin rows) (polynomialIndex : Fin (2^ell)) (globalAnchor : Networks.BinaryWalsh.Address shape.bits) :
    decoded shape rows ell precision denominator
      (NativeHadamardPhaseOriginal.result
        (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node phaseCoordinate path.visit activeFits) pair)
        (ButterflyIndependentGuardHeaders.reservation shape.bits precision) input)
      (RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) =
      (∏ column : Fin (arity^nodeExponent), Networks.BinaryPhase.phase (Networks.BinaryPhase.weightPhase
        (CompactComplexNonleafChildAddress.address phaseCoordinate path.visit globalAnchor column))) *
      decoded shape rows ell precision denominator input
        (RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) := by
  rw [decoded,NativeHadamardPhaseOriginal.signed_decoded]
  · rw [NativeHadamardPhaseRootBank.phase_at_node]
    rfl
  · intro coefficient
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth coefficient
  · exact fun coefficient => signed_guards_from_growth precision baseline growthConstant denominator pendingAxes path
      baselineFits dependencyFits pendingFits input inputGrid coefficient

end
end IntegerMultBounds.Machine.NativeHadamardPhaseCompletedGrid
