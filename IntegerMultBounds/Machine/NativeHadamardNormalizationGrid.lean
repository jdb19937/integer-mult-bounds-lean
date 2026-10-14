module

public import IntegerMultBounds.Machine.NativeHadamardNormalizationStream
public import IntegerMultBounds.Machine.NativeHadamardPhaseCompletedGrid

/-! Genuine recursive Paths and the actual completed grid certify the
normalization pass inside the unchanged signed reservation. The true increased
dyadic denominator and doubled numerator bound describe the installed words;
physical installation of the live-denominator descriptor remains separate. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationGrid
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Grid Width half decoded)
open NativeHadamardNormalizationArray (result components)
open NativeHadamardNormalizationFactor (denominatorIncrease)
open CompactComplexRecursiveGeometry (arity)
variable {shape : Shape} {rows ell left exponent levels frames returned : ℕ}

private theorem coefficient_widths (precision : ℕ) (input : Array shape rows ell)
    (inputWidth : Width shape rows ell precision input) :
    ∀ index,(input index).1.length=half shape precision+1 ∧ (input index).2.length=half shape precision+1 := by
  intro index
  simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth index

private theorem coefficient_bounds (precision denominator bound : ℕ) (input : Array shape rows ell)
    (inputGrid : Grid shape rows ell precision denominator bound input) :
    ∀ index,|ButterflySigned.signedValue (half shape precision) (input index).1|≤(bound : ℤ) ∧
      |ButterflySigned.signedValue (half shape precision) (input index).2|≤(bound : ℤ) :=
  fun index => ButterflyGuard.represented_bound _ _ denominator bound (inputGrid index)

/-- Exact readout and inherited-grid bounds for the actual normalized words. -/
theorem result_grid (precision denominator bound : ℕ) (input : Array shape rows ell)
    (inputWidth : Width shape rows ell precision input)
    (inputGrid : Grid shape rows ell precision denominator bound input)
    (signedGuard : 2*bound<2^(half shape precision)) :
    Grid shape rows ell precision (denominator+denominatorIncrease (arity^exponent)) (2*bound) (result input) := by
  have widths := coefficient_widths precision input inputWidth
  have bounds := coefficient_bounds precision denominator bound input inputGrid
  have integerGuard : 2*(bound : ℤ)<(2^(half shape precision) : ℕ) := by exact_mod_cast signedGuard
  intro index
  let values : Fin 2 → ℤ := fun coordinate => ButterflySigned.signedValue (half shape precision)
    (components (input index) coordinate.val)
  have sourceWidths : ∀ sourceIndex,(components (input index) sourceIndex).length=half shape precision+1 := by
    intro sourceIndex
    unfold components
    split_ifs <;> first | exact (widths index).1 | exact (widths index).2
  have sourceBounds : ∀ coordinate,|values coordinate|≤(bound : ℤ) := by
    intro coordinate
    fin_cases coordinate
    · exact (bounds index).1
    · exact (bounds index).2
  have signedResult (coordinate : Fin 2) := NativeHadamardNormalizationNumerator.words_signed coordinate
    (components (input index)) (half shape precision) sourceWidths values
    (fun sourceIndex => (ButterflySigned.signed_cast _ _).symm) (bound : ℤ) sourceBounds integerGuard
  refine ⟨NativeHadamardNormalizationNumerator.numerator values 0,
    NativeHadamardNormalizationNumerator.numerator values 1,?_,?_,?_⟩
  · change ButterflySigned.complexValue
      (ButterflySigned.signedValue _ (NativeHadamardNormalizationNumerator.words 0 (components (input index))))
      (ButterflySigned.signedValue _ (NativeHadamardNormalizationNumerator.words 1 (components (input index)))) _ * _ = _
    rw [signedResult 0,signedResult 1]
    unfold ButterflySigned.complexValue
    field_simp
  · exact_mod_cast NativeHadamardNormalizationNumerator.numerator_bound values (bound : ℤ) sourceBounds 0
  · exact_mod_cast NativeHadamardNormalizationNumerator.numerator_bound values (bound : ℤ) sourceBounds 1

/-- Complete in-place scan with exact normalization and a true output grid.
The genuine Path supplies the signed guard; no additional safety, execution,
normalized-output or larger reservation premise is required. The count header
is retained, and the live denominator still must be updated by the root wrapper. -/
theorem runs_from_path (precision baseline growthConstant denominator pendingAxes : ℕ)
    (path : CompactRecursiveDependencyBudget.Path shape.active left exponent levels frames returned)
    (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (pendingFits : pendingAxes≤shape.bits) (input : Array shape rows ell)
    (inputWidth : Width shape rows ell precision input)
    (inputGrid : Grid shape rows ell precision denominator
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes) input) :
    let bound := CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes
    HoareTime NativeHadamardNormalizationStream.program
      (fun bank => bank=NativeHadamardNormalizationStream.initial input)
      (fun bank => bank=NativeHadamardNormalizationStream.output input ∧
        Grid shape rows ell precision (denominator+denominatorIncrease (arity^exponent)) (2*bound) (result input) ∧
        ∀ index,decoded shape rows ell precision (denominator+denominatorIncrease (arity^exponent)) (result input) index=
          Networks.GaussianHadamardBridge.normalization^(arity^exponent)*
            decoded shape rows ell precision denominator input index)
      (220*(rows*(2^shape.bits*2^ell)*(2*(half shape precision+2))+
        (RecursiveChildQuotientsConstant.bits (rows*(2^shape.bits*2^ell))).length+1)) := by
  let bound := CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^pendingAxes
  have guard := CompactSpectatorInheritedGrid.guard_from_path shape precision path baseline growthConstant pendingAxes
    baselineFits dependencyFits pendingFits
  have signedGuard : 2*bound<2^(half shape precision) := by dsimp only [bound]; omega
  have integerGuard : 2*(bound : ℤ)<(2^(half shape precision) : ℕ) := by exact_mod_cast signedGuard
  have widths := coefficient_widths precision input inputWidth
  have bounds := coefficient_bounds precision denominator bound input inputGrid
  apply (NativeHadamardNormalizationStream.runs input (half shape precision+1) widths).consequence
    (fun _ equality => equality) _ (by simp only [Nat.add_assoc]; rfl)
  intro bank equality
  exact ⟨equality,result_grid precision denominator bound input inputWidth inputGrid signedGuard,
    NativeHadamardNormalizationArray.result_normalization input (half shape precision) denominator exponent
      widths (bound : ℤ) bounds integerGuard⟩

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationGrid
