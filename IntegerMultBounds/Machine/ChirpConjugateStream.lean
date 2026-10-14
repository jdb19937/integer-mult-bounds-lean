module

public import IntegerMultBounds.Machine.ChirpConjugateArray
public import IntegerMultBounds.Machine.RecoverWorkspace

/-! A reusable native chirp conjugation stream. Start with the original
coefficient array and blank work, emit the exact conjugate array, and physically
rewind both stream heads. Every other tape remains blank at origin. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpConjugateStream
noncomputable section
open ChirpConjugateArray (Pair native conjugated resultPairs)
open SharedPlacementAlphabet (setTape)
open RecoverWorkspace (atProgram restored)

def program := seq (seq ChirpConjugateArray.program (atProgram ReturnOrigin.program (56 : Fin 60)))
  (atProgram ReturnOrigin.program (58 : Fin 60))

def input (pairs : List Pair) : Tapes 60 2 :=
  setTape (SharedBank.empty 60 2) 56 (putWord (fun _ => blank) 0 (native pairs)) 0

def output (pairs : List Pair) : Tapes 60 2 :=
  setTape (input pairs) 58 (putWord (fun _ => blank) 0 (conjugated pairs)) 0

private theorem field_nonblank (digits : List (Fin 2)) :
    ∀ symbol ∈ DelimitedRadixRecord.field digits,symbol ≠ (blank : Fin 6) := by
  intro symbol member
  simp only [DelimitedRadixRecord.field,List.mem_append,List.mem_singleton] at member
  rcases member with dataMember | rfl
  · obtain ⟨digit,_,rfl⟩ := List.mem_map.mp dataMember
    intro equal
    have values := congrArg Fin.val equal
    change digit.val+4=0 at values
    omega
  · decide

private theorem native_nonblank (pairs : List Pair) :
    ∀ symbol ∈ native pairs,symbol ≠ (blank : Fin 6) := by
  intro symbol member
  obtain ⟨pair,_,inPair⟩ := List.mem_flatMap.mp member
  rcases List.mem_append.mp inPair with realMember | imaginaryMember
  · exact field_nonblank pair.1 symbol realMember
  · exact field_nonblank pair.2 symbol imaginaryMember

/-- Original source and conjugated destination are both ready at origin.
No unary ruler, binary count, pre-conjugated word or private work is supplied.
Empty arrays are covered, and every transition is charged to actual cells. -/
theorem runs (pairs : List Pair) (width : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width) :
    HoareTime program (· = input pairs) (· = output pairs) (44*(native pairs).length+6) := by
  have arrayRun := ChirpConjugateArray.runs_array_volume pairs [] (input pairs) width fieldWidths
    (by simp [input,setTape]) (by
      intro index
      have outsideSource : ChirpConjugateRecord.slots index ≠ (56 : Fin 60) := by
        intro equal
        have values := congrArg Fin.val equal
        simp only [ChirpConjugateRecord.slots] at values
        omega
      simp [input,setTape,SharedBank.empty,outsideSource])
  let finished := ChirpConjugateArray.finish (input pairs) pairs
  let sourceReturned := restored finished (56 : Fin 60)
  have returnSource := RecoverWorkspace.return_at (56 : Fin 60) finished (native pairs) (native_nonblank pairs)
    (by simp [finished,ChirpConjugateArray.finish,input,setTape,SharedBank.empty])
    (by simp [finished,ChirpConjugateArray.finish,input,setTape,SharedBank.empty])
  have returnDestination := RecoverWorkspace.return_at (58 : Fin 60) sourceReturned (conjugated pairs)
    (by rw [ChirpConjugateArray.conjugated_native]; exact native_nonblank (resultPairs pairs))
    (by simp [sourceReturned,restored,finished,ChirpConjugateArray.finish,input,setTape,SharedBank.empty])
    (by simp [sourceReturned,restored,finished,ChirpConjugateArray.finish,input,setTape,SharedBank.empty])
  have endpoint : restored sourceReturned (58 : Fin 60)=output pairs := by
    unfold sourceReturned restored finished ChirpConjugateArray.finish output input SharedBank.empty setTape
    apply Placement.Tapes.ext'
    all_goals intro slot; by_cases sourceSlot : slot=56 <;> by_cases destinationSlot : slot=58 <;>
      simp [Function.update_apply,sourceSlot,destinationSlot]
  unfold program
  apply ((arrayRun.seq returnSource).seq returnDestination).consequence
    (fun _ ready => ready) (fun _ finished => finished.trans endpoint)
  rw [ChirpConjugateArray.conjugated_length pairs width fieldWidths]
  omega

theorem workspace_blank (pairs : List Pair) (slot : Fin 60) (notSource : slot ≠ 56) (notDestination : slot ≠ 58) :
    (output pairs).tape slot=(fun _ => blank) ∧ (output pairs).head slot=0 := by
  simp [output,input,setTape,SharedBank.empty,notSource,notDestination]

/-- The same actual whole-stream execution produces exact conjugate values.
The public precision/word-width slack discharges the negation guard from the
original numerator bound, retaining the original source for later chirp use. -/
theorem runs_conjugate (pairs : List Pair) (widthPred precision : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=widthPred+1 ∧ pair.2.length=widthPred+1)
    (precisionFits : precision+2 ≤ widthPred+1)
    (imaginaryBound : ∀ pair ∈ pairs,|ButterflySigned.signedValue widthPred pair.2| ≤ (2^precision : ℕ)) :
    HoareTime program (· = input pairs) (· = output pairs) (44*(native pairs).length+6) ∧
      (resultPairs pairs).map (ChirpConjugateArray.value widthPred precision) =
        pairs.map (fun pair => (starRingEnd ℂ) (ChirpConjugateArray.value widthPred precision pair)) ∧
      (∀ slot : Fin 60,slot ≠ 56 → slot ≠ 58 → (output pairs).tape slot=(fun _ => blank) ∧ (output pairs).head slot=0) := by
  refine ⟨runs pairs (widthPred+1) fieldWidths,?_,workspace_blank pairs⟩
  apply ChirpConjugateArray.result_values pairs widthPred precision fieldWidths
  intro pair member
  exact ChirpConjugateNumerator.imaginary_not_minimum_of_bound pair.2 widthPred precision precisionFits
    (imaginaryBound pair member)

end
end IntegerMultBounds.Machine.ChirpConjugateStream
