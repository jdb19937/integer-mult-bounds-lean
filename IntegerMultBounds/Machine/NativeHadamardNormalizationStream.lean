module

public import IntegerMultBounds.Machine.NativeHadamardNormalizationArray
public import IntegerMultBounds.Machine.NativeZeroPaddingArray
public import IntegerMultBounds.Machine.BlankWordOverwriteAt

/-! Install the counted normalization scan in place. Both streams are returned
from their genuine EOF, the source is overwritten by the equal-width normalized
word, and the temporary output is erased. The original count header survives;
all other tapes are blank at zero heads. Updating the live denominator and
placing this program on the returned native root remain separate obligations. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationStream
noncomputable section
open ButterflyStreamData (Coefficient)
open NativeHadamardNormalizationArray (result)
open SharedPlacementAlphabet (setTape)
variable {coefficientCount : ℕ}

def initial (coefficients : Fin coefficientCount → Coefficient) :=
  CountedLoopHeaderClean.bank (NativeHadamardNormalizationArray.counted
    (fun _ => blank) (fun _ => blank) 0 0 coefficients 0)

def scanned (coefficients : Fin coefficientCount → Coefficient) :=
  CountedLoopHeaderClean.bank (NativeHadamardNormalizationArray.counted
    (fun _ => blank) (fun _ => blank) 0 0 coefficients coefficientCount)

def output (coefficients : Fin coefficientCount → Coefficient) :=
  setTape (initial coefficients) 0
    (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word (result coefficients))) 0

def program := seq (seq (seq NativeHadamardNormalizationArray.program
    (BlankWordReturnAt.program (a:=2) (0 : Fin 17)))
    (BlankWordReturnAt.program (a:=2) (1 : Fin 17)))
    (BlankWordOverwriteAt.program (a:=2) (0 : Fin 17) 1 (by decide))

theorem word_length (coefficients : Fin coefficientCount → Coefficient) (wordWidth : ℕ)
    (coefficientWidths : ∀ index,(coefficients index).1.length=wordWidth ∧ (coefficients index).2.length=wordWidth) :
    (NativeZeroPaddingArray.word coefficients).length=coefficientCount*(2*(wordWidth+1)) := by
  have lengthBound := CyclicRowSplit.prefix_length (fun index => ButterflyStreamData.encoded (coefficients index))
    (2*(wordWidth+1))
    (fun index => DelimitedRadixRecord.complex_length _ _ _ (coefficientWidths index).1 (coefficientWidths index).2)
    coefficientCount le_rfl
  simpa only [CyclicRowCycle.prefix_all,NativeZeroPaddingArray.word] using lengthBound

private theorem scan_endpoints (coefficients : Fin coefficientCount → Coefficient) :
    (scanned coefficients).tape 0=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word coefficients) ∧
    (scanned coefficients).head 0=(NativeZeroPaddingArray.word coefficients).length ∧
    (scanned coefficients).tape 1=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word (result coefficients)) ∧
    (scanned coefficients).head 1=(NativeZeroPaddingArray.word (result coefficients)).length := by
  change ButterflyStreamData.full (fun _ => blank) 0 coefficients = _ ∧
    ButterflyStreamData.position 0 coefficients coefficientCount = _ ∧
    ButterflyStreamData.prefixTape (fun _ => blank) 0 (result coefficients) coefficientCount = _ ∧
    ButterflyStreamData.position 0 (result coefficients) coefficientCount = _
  simp only [ButterflyStreamData.full,ButterflyStreamData.position,ButterflyStreamData.prefixTape,
    CyclicRowCycle.prefix_all,NativeZeroPaddingArray.word,zero_add,and_self]

private theorem scan_frame (coefficients : Fin coefficientCount → Coefficient) (port : Fin 17)
    (notSource : port≠0) (notDestination : port≠1) :
    (scanned coefficients).head port=(initial coefficients).head port ∧
      (scanned coefficients).tape port=(initial coefficients).tape port := by
  induction port using Fin.addCases (m:=15) (n:=2) with
  | right port =>
    simp only [scanned,initial,CountedLoopHeaderClean.bank,Tapes.append,Fin.addCases_right]
    trivial
  | left port =>
    induction port using Fin.addCases (m:=14) (n:=1) with
    | right port =>
      simp only [scanned,initial,CountedLoopHeaderClean.bank,NativeHadamardNormalizationArray.counted,
        Tapes.append,Fin.addCases_left,Fin.addCases_right]
      trivial
    | left port =>
      induction port using Fin.addCases (m:=2) (n:=12) with
      | right port =>
        simp only [scanned,initial,CountedLoopHeaderClean.bank,NativeHadamardNormalizationArray.counted,
          NativeHadamardNormalizationArray.state,Tapes.append,Fin.addCases_left,Fin.addCases_right]
        trivial
      | left port => fin_cases port <;> contradiction

private theorem initial_destination (coefficients : Fin coefficientCount → Coefficient) :
    (initial coefficients).head 1=0 ∧ (initial coefficients).tape 1=(fun _ => blank) := by
  change 0=0 ∧ putWord (fun _ => blank) 0 []=(fun _ => blank)
  simp [putWord]

/-- One fixed program physically installs the normalized array on its original
source tape, retaining the original count and reclaiming all temporary storage.
The complete scan, two EOF returns, overwrite and every join have a fixed bound. -/
theorem runs (coefficients : Fin coefficientCount → Coefficient) (wordWidth : ℕ)
    (coefficientWidths : ∀ index,(coefficients index).1.length=wordWidth ∧ (coefficients index).2.length=wordWidth) :
    HoareTime program (fun bank => bank=initial coefficients) (fun bank => bank=output coefficients)
      (220*(coefficientCount*(2*(wordWidth+1))+
        (RecursiveChildQuotientsConstant.bits coefficientCount).length+1)) := by
  let sourceWord := NativeZeroPaddingArray.word coefficients
  let resultWord := NativeZeroPaddingArray.word (result coefficients)
  have endpoints := scan_endpoints coefficients
  have sourceReturn := BlankWordReturnAt.runs (scanned coefficients) (0 : Fin 17) sourceWord
    (NativeZeroPaddingArray.nonblank coefficients) endpoints.1 endpoints.2.1
  let sourceReturned := setTape (scanned coefficients) (0 : Fin 17) (putWord (fun _ => blank) 0 sourceWord) 0
  have resultReturn := BlankWordReturnAt.runs sourceReturned (1 : Fin 17) resultWord
    (NativeZeroPaddingArray.nonblank (result coefficients))
    (by simpa [sourceReturned,setTape] using endpoints.2.2.1)
    (by simpa [sourceReturned,setTape] using endpoints.2.2.2)
  let bothReturned := setTape sourceReturned (1 : Fin 17) (putWord (fun _ => blank) 0 resultWord) 0
  have equalLength : sourceWord.length=resultWord.length := by
    rw [word_length coefficients wordWidth coefficientWidths,
      word_length (result coefficients) wordWidth (NativeHadamardNormalizationArray.result_width coefficients wordWidth coefficientWidths)]
  have install := BlankWordOverwriteAt.runs bothReturned (0 : Fin 17) 1 (by decide)
    sourceWord resultWord equalLength (NativeZeroPaddingArray.nonblank (result coefficients))
    (by simp [bothReturned,sourceReturned,setTape]) (by simp [bothReturned,setTape])
  have scan := NativeHadamardNormalizationArray.runs (fun _ => blank) (fun _ => blank) 0 0 coefficients wordWidth coefficientWidths
  apply (((scan.seq sourceReturn).seq resultReturn).seq install).consequence
    (fun _ equality => equality) ?_ ?_
  · intro bank equality
    rw [equality]
    apply Placement.Tapes.ext'
    all_goals
      intro port
      by_cases isSource : port=0
      · subst port
        simp [BlankWordOverwriteAt.output,bothReturned,sourceReturned,output,setTape,resultWord]
      · by_cases isDestination : port=1
        · subst port
          first
            | simpa [BlankWordOverwriteAt.output,bothReturned,sourceReturned,output,setTape] using
                (initial_destination coefficients).1.symm
            | simpa [BlankWordOverwriteAt.output,bothReturned,sourceReturned,output,setTape] using
                (initial_destination coefficients).2.symm
        · first
            | simpa [BlankWordOverwriteAt.output,bothReturned,sourceReturned,output,setTape,isSource,isDestination] using
                (scan_frame coefficients port isSource isDestination).1
            | simpa [BlankWordOverwriteAt.output,bothReturned,sourceReturned,output,setTape,isSource,isDestination] using
                (scan_frame coefficients port isSource isDestination).2
  · have scanBound := NativeHadamardNormalizationArray.runtime_le_volume (coefficientCount:=coefficientCount) wordWidth
    have sourceLength := word_length coefficients wordWidth coefficientWidths
    have resultLength := word_length (result coefficients) wordWidth
      (NativeHadamardNormalizationArray.result_width coefficients wordWidth coefficientWidths)
    dsimp only [sourceWord,resultWord]
    rw [sourceLength,resultLength]
    nlinarith only [scanBound]

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationStream
