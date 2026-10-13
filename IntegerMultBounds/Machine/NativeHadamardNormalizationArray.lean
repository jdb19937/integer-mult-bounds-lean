module

public import IntegerMultBounds.Machine.NativeHadamardNormalizationRecord
public import IntegerMultBounds.Machine.CountedLoopHeaderClean
public import IntegerMultBounds.Machine.ButterflyStreamEndpoint

/-! An original-header counted normalization pass over a literal finite array.
The header is retained, all fourteen private/loop tapes are reclaimed, and no
terminal phantom record is read. This pass has one fixed volume coefficient,
independent of the native width selected for the normalization factor. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationArray
noncomputable section
open ButterflyStreamData (Coefficient full prefixTape position context)
open NativeHadamardNormalizationNumerator (words)
variable {coefficientCount : ℕ}

def components (coefficient : Coefficient) : ℕ → List (Fin 2) :=
  fun index => if index=0 then coefficient.1 else coefficient.2

def result (coefficients : Fin coefficientCount → Coefficient) (index : Fin coefficientCount) : Coefficient :=
  (words 0 (components (coefficients index)),words 1 (components (coefficients index)))

def state (sourceBackground destinationBackground : ℤ → Fin 6) (sourceOrigin destinationOrigin : ℤ)
    (coefficients : Fin coefficientCount → Coefficient) (processed : ℕ) : Tapes 14 2 :=
  (NativeHadamardNormalizationRecord.streams (full sourceBackground sourceOrigin coefficients)
    (prefixTape destinationBackground destinationOrigin (result coefficients) processed)
    (position sourceOrigin coefficients processed) (position destinationOrigin (result coefficients) processed)).append
    (SharedBank.empty 12 2)

def counted (sourceBackground destinationBackground : ℤ → Fin 6) (sourceOrigin destinationOrigin : ℤ)
    (coefficients : Fin coefficientCount → Coefficient) (processed : ℕ) :=
  (state sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients processed).append
    (MarkedWordCleanup.one (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits coefficientCount)) 1)

def body := extend NativeHadamardNormalizationRecord.program 1
def program := CountedLoopHeaderClean.program body (14 : Fin 15)

private theorem record_input (sourceBackground destinationBackground : ℤ → Fin 6) (sourceOrigin destinationOrigin : ℤ)
    (coefficients : Fin coefficientCount → Coefficient) (index : Fin coefficientCount) :
    NativeHadamardNormalizationRecord.input (context sourceBackground sourceOrigin coefficients index)
      (prefixTape destinationBackground destinationOrigin (result coefficients) index.val)
      (position destinationOrigin (result coefficients) index.val)=
    state sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients index.val := by
  simp only [NativeHadamardNormalizationRecord.input,ButterflyStreamData.context_tape,
    ButterflyStreamData.context_start,state]

private theorem record_output (sourceBackground destinationBackground : ℤ → Fin 6) (sourceOrigin destinationOrigin : ℤ)
    (coefficients : Fin coefficientCount → Coefficient) (index : Fin coefficientCount) :
    NativeHadamardNormalizationRecord.output (context sourceBackground sourceOrigin coefficients index)
      (prefixTape destinationBackground destinationOrigin (result coefficients) index.val)
      (position destinationOrigin (result coefficients) index.val)=
    state sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients (index.val+1) := by
  have sources : NativeHadamardNormalizationRecord.sources (context sourceBackground sourceOrigin coefficients index)=
      components (coefficients index) := rfl
  simp only [NativeHadamardNormalizationRecord.output,ButterflyStreamData.context_tape,
    ButterflyStreamData.context_start,sources,state]
  change (NativeHadamardNormalizationRecord.streams _
    (putWord (prefixTape destinationBackground destinationOrigin (result coefficients) index.val)
      (position destinationOrigin (result coefficients) index.val) (ButterflyStreamData.encoded (result coefficients index)))
    (position sourceOrigin coefficients index.val+(coefficients index).1.length+(coefficients index).2.length+2)
    (position destinationOrigin (result coefficients) index.val+(result coefficients index).1.length+
      (result coefficients index).2.length+2)).append _ = _
  rw [ButterflyStreamData.prefixTape_succ,←ButterflyStreamData.position_succ,←ButterflyStreamData.position_succ]

/-- The count is read from its physical original header. The exact normalized
array is emitted, with the source and count retained and every private tape
blank again. Includes an empty array without reading any dummy coefficient. -/
theorem runs (sourceBackground destinationBackground : ℤ → Fin 6) (sourceOrigin destinationOrigin : ℤ)
    (coefficients : Fin coefficientCount → Coefficient) (wordWidth : ℕ)
    (coefficientWidths : ∀ index,(coefficients index).1.length=wordWidth ∧ (coefficients index).2.length=wordWidth) :
    HoareTime program
      (fun bank => bank=CountedLoopHeaderClean.bank
        (counted sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients 0))
      (fun bank => bank=CountedLoopHeaderClean.bank
        (counted sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients coefficientCount))
      (coefficientCount*(48*wordWidth+172)+
        11*(RecursiveChildQuotientsConstant.bits coefficientCount).length+35) := by
  have bodyRun : ∀ processed<coefficientCount,HoareTime body
      (fun bank => bank=counted sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients processed)
      (fun bank => bank=counted sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients (processed+1))
      (48*wordWidth+166) := by
    intro processed belowCount
    let index : Fin coefficientCount := ⟨processed,belowCount⟩
    have recordRun := NativeHadamardNormalizationRecord.runs (context sourceBackground sourceOrigin coefficients index)
      (prefixTape destinationBackground destinationOrigin (result coefficients) processed)
      (position destinationOrigin (result coefficients) processed) wordWidth (coefficientWidths index)
    rw [record_input,record_output] at recordRun
    exact hoare_extend_eq recordRun _
  have countedRun := CountedLoopHeaderClean.runs body (14 : Fin 15)
    (RecursiveChildQuotientsConstant.bits coefficientCount) coefficientCount
    (counted sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients)
    (fun _ => 48*wordWidth+166)
    (by simp [counted,Tapes.append,Fin.addCases,MarkedWordCleanup.one])
    (RecursiveChildQuotientsConstant.bits_value _) bodyRun
  apply countedRun.consequence (fun _ equality => equality) (fun _ equality => equality) ?_
  simp only [CountedLoopHeaderClean.cost,Finset.sum_const,Finset.card_range,smul_eq_mul]
  nlinarith

theorem result_width (coefficients : Fin coefficientCount → Coefficient) (wordWidth : ℕ)
    (coefficientWidths : ∀ index,(coefficients index).1.length=wordWidth ∧ (coefficients index).2.length=wordWidth)
    (index : Fin coefficientCount) :
    (result coefficients index).1.length=wordWidth ∧ (result coefficients index).2.length=wordWidth := by
  have widths : ∀ sourceIndex,(components (coefficients index) sourceIndex).length=wordWidth := by
    intro sourceIndex
    unfold components
    split_ifs <;> first | exact (coefficientWidths index).1 | exact (coefficientWidths index).2
  exact ⟨NativeHadamardNormalizationNumerator.words_length _ _ _ widths,
    NativeHadamardNormalizationNumerator.words_length _ _ _ widths⟩

/-- The emitted stream is literally the full result array, at its true endpoint. -/
theorem destination_endpoint (sourceBackground destinationBackground : ℤ → Fin 6) (sourceOrigin destinationOrigin : ℤ)
    (coefficients : Fin coefficientCount → Coefficient) (wordWidth : ℕ)
    (coefficientWidths : ∀ index,(coefficients index).1.length=wordWidth ∧ (coefficients index).2.length=wordWidth) :
    (state sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients coefficientCount).tape 1=
      full destinationBackground destinationOrigin (result coefficients) ∧
    (state sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients coefficientCount).head 1=
      destinationOrigin+coefficientCount*(2*(wordWidth+1)) := by
  change prefixTape destinationBackground destinationOrigin (result coefficients) coefficientCount=
      full destinationBackground destinationOrigin (result coefficients) ∧
    position destinationOrigin (result coefficients) coefficientCount=
      destinationOrigin+coefficientCount*(2*(wordWidth+1))
  constructor
  · simp only [prefixTape,CyclicRowCycle.prefix_all,full]
  · exact ButterflyStreamEndpoint.position_all destinationOrigin (result coefficients) wordWidth
      (result_width coefficients wordWidth coefficientWidths)


/-- One common volume coefficient pays the full scan, descriptor copy and
cleanup. Neither the coefficient count nor native visit width selects a program. -/
theorem runtime_le_volume (wordWidth : ℕ) :
    coefficientCount*(48*wordWidth+172)+
        11*(RecursiveChildQuotientsConstant.bits coefficientCount).length+35 ≤
      200*(coefficientCount*(2*(wordWidth+1))+
        (RecursiveChildQuotientsConstant.bits coefficientCount).length+1) := by
  nlinarith

/-- Every actual emitted coefficient decodes to its exact native Hadamard
normalization at the increased denominator. The source-width and signed guard
are the only arithmetic premises; physical denominator installation is separate. -/
theorem result_normalization (coefficients : Fin coefficientCount → Coefficient)
    (halfWidth denominator exponent : ℕ)
    (coefficientWidths : ∀ index,(coefficients index).1.length=halfWidth+1 ∧
      (coefficients index).2.length=halfWidth+1) (bound : ℤ)
    (coefficientBounds : ∀ index,|ButterflySigned.signedValue halfWidth (coefficients index).1|≤bound ∧
      |ButterflySigned.signedValue halfWidth (coefficients index).2|≤bound)
    (signedGuard : 2*bound<(2^halfWidth : ℕ)) (index : Fin coefficientCount) :
    ButterflySigned.complexValue (ButterflySigned.signedValue halfWidth (result coefficients index).1)
      (ButterflySigned.signedValue halfWidth (result coefficients index).2)
      (denominator+NativeHadamardNormalizationFactor.denominatorIncrease
        (CompactComplexRecursiveGeometry.arity^exponent))=
      Networks.GaussianHadamardBridge.normalization^(CompactComplexRecursiveGeometry.arity^exponent)*
        ButterflySigned.complexValue (ButterflySigned.signedValue halfWidth (coefficients index).1)
          (ButterflySigned.signedValue halfWidth (coefficients index).2) denominator := by
  have widths : ∀ sourceIndex,(components (coefficients index) sourceIndex).length=halfWidth+1 := by
    intro sourceIndex
    unfold components
    split_ifs <;> first | exact (coefficientWidths index).1 | exact (coefficientWidths index).2
  have bounds : ∀ sourceIndex : Fin 2,
      |ButterflySigned.signedValue halfWidth (components (coefficients index) sourceIndex.val)|≤bound := by
    intro sourceIndex
    fin_cases sourceIndex
    · exact (coefficientBounds index).1
    · exact (coefficientBounds index).2
  have signedResult (coordinate : Fin 2) := NativeHadamardNormalizationNumerator.words_signed coordinate
    (components (coefficients index)) halfWidth widths
    (fun sourceIndex => ButterflySigned.signedValue halfWidth (components (coefficients index) sourceIndex.val))
    (fun sourceIndex => (ButterflySigned.signed_cast halfWidth (components (coefficients index) sourceIndex.val)).symm)
    bound bounds signedGuard
  change ButterflySigned.complexValue _ _ _ = _
  rw [show (result coefficients index).1=words 0 (components (coefficients index)) from rfl,
    show (result coefficients index).2=words 1 (components (coefficients index)) from rfl,
    signedResult 0,signedResult 1]
  exact NativeHadamardNormalizationNumerator.complex_normalization _ denominator exponent

/-- Timed literal-array execution together with exact normalization of every
emitted coefficient. No supplied machine execution or semantic oracle is used. -/
theorem runs_exact (sourceBackground destinationBackground : ℤ → Fin 6) (sourceOrigin destinationOrigin : ℤ)
    (coefficients : Fin coefficientCount → Coefficient) (halfWidth denominator exponent : ℕ)
    (coefficientWidths : ∀ index,(coefficients index).1.length=halfWidth+1 ∧
      (coefficients index).2.length=halfWidth+1) (bound : ℤ)
    (coefficientBounds : ∀ index,|ButterflySigned.signedValue halfWidth (coefficients index).1|≤bound ∧
      |ButterflySigned.signedValue halfWidth (coefficients index).2|≤bound)
    (signedGuard : 2*bound<(2^halfWidth : ℕ)) :
    HoareTime program
      (fun bank => bank=CountedLoopHeaderClean.bank
        (counted sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients 0))
      (fun bank => bank=CountedLoopHeaderClean.bank
        (counted sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients coefficientCount) ∧
        ∀ index,ButterflySigned.complexValue
          (ButterflySigned.signedValue halfWidth (result coefficients index).1)
          (ButterflySigned.signedValue halfWidth (result coefficients index).2)
          (denominator+NativeHadamardNormalizationFactor.denominatorIncrease
            (CompactComplexRecursiveGeometry.arity^exponent))=
          Networks.GaussianHadamardBridge.normalization^(CompactComplexRecursiveGeometry.arity^exponent)*
            ButterflySigned.complexValue (ButterflySigned.signedValue halfWidth (coefficients index).1)
              (ButterflySigned.signedValue halfWidth (coefficients index).2) denominator)
      (200*(coefficientCount*(2*(halfWidth+2))+
        (RecursiveChildQuotientsConstant.bits coefficientCount).length+1)) := by
  apply (runs sourceBackground destinationBackground sourceOrigin destinationOrigin coefficients
    (halfWidth+1) coefficientWidths).consequence (fun _ equality => equality) _
    (by simpa only [Nat.add_assoc] using (runtime_le_volume (coefficientCount:=coefficientCount) (halfWidth+1)))
  intro bank equality
  exact ⟨equality,result_normalization coefficients halfWidth denominator exponent coefficientWidths bound
    coefficientBounds signedGuard⟩

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationArray
