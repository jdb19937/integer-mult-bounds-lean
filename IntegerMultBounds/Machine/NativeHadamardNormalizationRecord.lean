module

public import IntegerMultBounds.Machine.NativeHadamardNormalizationNumerator
public import IntegerMultBounds.Machine.RawLinearCombinationFieldEmit
public import IntegerMultBounds.Machine.RadixControlCleanupBank
public import IntegerMultBounds.Machine.ButterflyRecordEmit

/-! A complete normalization record pass. It reads the two literal source
fields, computes their sum and difference, emits both exact fields, and erases
all twelve private tapes. Source and output streams can have arbitrary frames.
The native stream loop and live-denominator update remain separate. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationRecord
noncomputable section
open DelimitedRadixRecord (Context field complex)
open SharedPlacementAlphabet (setTape)
open RadixDigits
open NativeHadamardNormalizationNumerator (words)

def sources (record : Context 2) : ℕ → List (Fin 2) :=
  fun index => if index=0 then record.re else record.im

def streams (source destination : ℤ → Fin 6) (sourceHead destinationHead : ℤ) : Tapes 2 2 :=
  (MarkedWordCleanup.one source sourceHead).append (MarkedWordCleanup.one destination destinationHead)

def input (record : Context 2) (destination : ℤ → Fin 6) (destinationHead : ℤ) : Tapes 14 2 :=
  (streams record.tape destination record.start destinationHead).append (SharedBank.empty 12 2)

def afterRead (record : Context 2) (destination : ℤ → Fin 6) (destinationHead : ℤ) : Tapes 14 2 :=
  (streams record.tape destination (record.start+record.re.length+record.im.length+2) destinationHead).append
    (NativeHadamardNormalizationNumerator.input (sources record))

def afterArithmetic (record : Context 2) (destination : ℤ → Fin 6) (destinationHead : ℤ) : Tapes 14 2 :=
  (streams record.tape destination (record.start+record.re.length+record.im.length+2) destinationHead).append
    (NativeHadamardNormalizationNumerator.output (sources record))

def afterEmit (record : Context 2) (destination : ℤ → Fin 6) (destinationHead : ℤ) : Tapes 14 2 :=
  (streams record.tape
    (putWord destination destinationHead (complex (words 0 (sources record)) (words 1 (sources record))))
    (record.start+record.re.length+record.im.length+2)
    (destinationHead+(words 0 (sources record)).length+(words 1 (sources record)).length+2)).append
    ((RadixLinearCombinationRefresh.controls (c:=2) (sources record)).append (SharedBank.empty 10 2))

def output (record : Context 2) (destination : ℤ → Fin 6) (destinationHead : ℤ) : Tapes 14 2 :=
  (streams record.tape
    (putWord destination destinationHead (complex (words 0 (sources record)) (words 1 (sources record))))
    (record.start+record.re.length+record.im.length+2)
    (destinationHead+(words 0 (sources record)).length+(words 1 (sources record)).length+2)).append
    (SharedBank.empty 12 2)

def readReal := TwoTapeAt.program (DelimitedRadixRead.program (q:=2)) (0 : Fin 14) 2 (by decide)
def readImaginary := TwoTapeAt.program (DelimitedRadixRead.program (q:=2)) (0 : Fin 14) 3 (by decide)
def readProgram := seq readReal readImaginary
def arithmetic := RawLinearCombinationCleanup.prepend NativeHadamardNormalizationNumerator.program 2
def emitReal := TwoTapeAt.program (DelimitedRadixEmit.program (q:=2)) (4 : Fin 14) 1 (by decide)
def emitImaginary := TwoTapeAt.program (DelimitedRadixEmit.program (q:=2)) (9 : Fin 14) 1 (by decide)
def emitProgram := seq emitReal emitImaginary
def cleanup := RawLinearCombinationCleanup.prepend (RadixControlCleanupBank.program (q:=2) (u:=10) (by decide : 0<2)) 2
def program := seq (seq (seq readProgram arithmetic) emitProgram) cleanup

private theorem read_runs (record : Context 2) (destination : ℤ → Fin 6) (destinationHead : ℤ) :
    HoareTime readProgram (fun bank => bank=input record destination destinationHead)
      (fun bank => bank=afterRead record destination destinationHead)
      (2*(record.re.length+record.im.length)+13) := by
  let initialBank := input record destination destinationHead
  let firstBank := TwoTapeAt.result initialBank 0 2 record.tape
    (MarkedWordCleanup.marked (record.re.map digitSymbol)) (record.start+record.re.length+1) 1
  have realRun := TwoTapeAt.runs DelimitedRadixRead.program (0 : Fin 14) 2 (by decide) initialBank
    _ _ _ _ _ _ _ _ (by constructor <;> rfl) (by constructor <;> rfl) (DelimitedRadixRecord.read_real record)
  have imaginaryRun := TwoTapeAt.runs DelimitedRadixRead.program (0 : Fin 14) 3 (by decide) firstBank
    _ _ _ _ _ _ _ _ (by simp [firstBank,TwoTapeAt.result,setTape])
    (by simp [firstBank,initialBank,input,streams,TwoTapeAt.result,setTape,Tapes.append,Fin.addCases,SharedBank.empty])
    (DelimitedRadixRecord.read_imaginary record)
  apply (realRun.seq imaginaryRun).consequence (fun _ equality => equality) _ (by omega)
  intro bank equality
  rw [equality]
  apply Placement.Tapes.ext'
  all_goals intro port; fin_cases port
  all_goals simp [firstBank,initialBank,input,afterRead,streams,TwoTapeAt.result,setTape,Tapes.append,Fin.addCases,
    SharedBank.empty,NativeHadamardNormalizationNumerator.input,RadixLinearCombinationRefresh.controls,
    RadixLinearCombinationBootstrap.empty,sources,MarkedRadixRefresh.source,MarkedWordCleanup.one]

private theorem emit_runs (record : Context 2) (destination : ℤ → Fin 6) (destinationHead : ℤ) :
    HoareTime emitProgram (fun bank => bank=afterArithmetic record destination destinationHead)
      (fun bank => bank=afterEmit record destination destinationHead)
      (2*((words 0 (sources record)).length+(words 1 (sources record)).length)+13) := by
  let initialBank := afterArithmetic record destination destinationHead
  let firstBank := TwoTapeAt.result initialBank 4 1 (fun _ => blank)
    (putWord destination destinationHead (field (words 0 (sources record))))
    0 (destinationHead+(words 0 (sources record)).length+1)
  have realRun := TwoTapeAt.runs DelimitedRadixEmit.program (4 : Fin 14) 1 (by decide) initialBank
    _ _ _ _ _ _ _ _ (by constructor <;> rfl) (by constructor <;> rfl)
    (DelimitedRadixRecord.emit_field destination destinationHead (words 0 (sources record)))
  have imaginaryRun := TwoTapeAt.runs DelimitedRadixEmit.program (9 : Fin 14) 1 (by decide) firstBank
    _ _ _ _ _ _ _ _
    (by constructor <;> rfl)
    (by simp [firstBank,TwoTapeAt.result,setTape])
    (DelimitedRadixRecord.emit_field (putWord destination destinationHead (field (words 0 (sources record))))
      (destinationHead+(words 0 (sources record)).length+1) (words 1 (sources record)))
  apply (realRun.seq imaginaryRun).consequence (fun _ equality => equality) _ (by omega)
  intro bank equality
  rw [equality,ButterflyRecordEmit.append_fields]
  apply Placement.Tapes.ext'
  all_goals intro port; fin_cases port
  all_goals first | rfl | (change destinationHead+(words 0 (sources record)).length+1+
    (words 1 (sources record)).length+1=destinationHead+(words 0 (sources record)).length+
    (words 1 (sources record)).length+2; omega)

theorem source_widths (record : Context 2) (wordWidth : ℕ)
    (recordWidths : record.re.length=wordWidth ∧ record.im.length=wordWidth) :
    ∀ index,(sources record index).length=wordWidth := by
  intro index
  unfold sources
  split_ifs <;> first | exact recordWidths.1 | exact recordWidths.2

/-- Complete physical two-field normalization with clean private storage.
Both arbitrary stream frames are retained and every transition is charged. -/
theorem runs (record : Context 2) (destination : ℤ → Fin 6) (destinationHead : ℤ) (wordWidth : ℕ)
    (recordWidths : record.re.length=wordWidth ∧ record.im.length=wordWidth) :
    HoareTime program (fun bank => bank=input record destination destinationHead)
      (fun bank => bank=output record destination destinationHead) (48*wordWidth+166) := by
  have widths := source_widths record wordWidth recordWidths
  have arithmeticRun := RawLinearCombinationCleanup.prepend_runs NativeHadamardNormalizationNumerator.program _ _
    (streams record.tape destination (record.start+record.re.length+record.im.length+2) destinationHead)
    (NativeHadamardNormalizationNumerator.runs (sources record) wordWidth widths)
  have cleanupRun := RawLinearCombinationCleanup.prepend_runs
    (RadixControlCleanupBank.program (q:=2) (u:=10) (by decide : 0<2)) _ _
    (streams record.tape
      (putWord destination destinationHead (complex (words 0 (sources record)) (words 1 (sources record))))
      (record.start+record.re.length+record.im.length+2)
      (destinationHead+(words 0 (sources record)).length+(words 1 (sources record)).length+2))
    (RadixControlCleanupBank.runs (by decide : 0<2) (sources record) wordWidth widths (SharedBank.empty 10 2))
  apply (((read_runs record destination destinationHead).seq arithmeticRun).seq
    (emit_runs record destination destinationHead)).seq cleanupRun |>.consequence
      (fun _ equality => equality) ?_ ?_
  · intro bank equality
    rw [equality]
    congr 1
    apply Placement.Tapes.ext'
    all_goals intro port; fin_cases port
    all_goals simp [Tapes.append,Fin.addCases,RadixLinearCombinationBootstrap.empty,SharedBank.empty]
  rw [recordWidths.1,recordWidths.2,NativeHadamardNormalizationNumerator.words_length _ _ _ widths,
    NativeHadamardNormalizationNumerator.words_length _ _ _ widths]
  omega

/-- All private tapes return wholly blank at zero heads, ready for the next
record. The output field lengths retain the original signed-word format. -/
theorem output_private (record : Context 2) (destination : ℤ → Fin 6) (destinationHead : ℤ) (port : Fin 12) :
    (output record destination destinationHead).head (Fin.natAdd 2 port)=0 ∧
      (output record destination destinationHead).tape (Fin.natAdd 2 port)=(fun _ => blank) := by
  simp [output,Tapes.append,SharedBank.empty]

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationRecord
