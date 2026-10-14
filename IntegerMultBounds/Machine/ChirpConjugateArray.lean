module

public import IntegerMultBounds.Machine.ChirpConjugateRecord
public import IntegerMultBounds.Machine.LoopChain

/-! Conjugate every native complex record, using the actual blank source end
as loop termination. No record counter or prepared per-record controls are
supplied. Private arithmetic storage is reused and cleared each iteration. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpConjugateArray
noncomputable section
open SharedPlacementAlphabet (setTape)
open DelimitedRadixRecord (Context complex)
open ChirpConjugateNumerator (words)

abbrev Pair := List (Fin 2) × List (Fin 2)
def pairSources (pair : Pair) : ℕ → List (Fin 2) := fun index => if index=0 then pair.1 else pair.2

def native (pairs : List Pair) := pairs.flatMap fun pair => complex pair.1 pair.2

def conjugated (pairs : List Pair) := pairs.flatMap fun pair =>
  complex (words 0 (pairSources pair)) (words 1 (pairSources pair))

def test (symbols : Fin 60 → Fin 6) := decide (symbols 56 ≠ blank)
def program := whileLoop ChirpConjugateRecord.program test

def finish (current : Tapes 60 2) (pairs : List Pair) :=
  setTape (setTape current 56 (current.tape 56) (current.head 56+(native pairs).length)) 58
    (putWord (current.tape 58) (current.head 58) (conjugated pairs))
    (current.head 58+(conjugated pairs).length)

private theorem finish_append (current : Tapes 60 2) (front back : List Pair) :
    finish (finish current front) back=finish current (front++back) := by
  unfold finish
  simp only [native,conjugated,List.flatMap_append,List.length_append,Nat.cast_add,setTape,
    Function.update_self,show (56 : Fin 60) ≠ 58 by decide,show (58 : Fin 60) ≠ 56 by decide,
    Function.update_of_ne,add_assoc]
  rw [putWord_append_forward]
  apply Placement.Tapes.ext'
  all_goals intro slot; by_cases sourceSlot : slot=56 <;> by_cases destinationSlot : slot=58 <;>
    simp [Function.update_apply,sourceSlot,destinationSlot,add_assoc]

private theorem finish_nil (current : Tapes 60 2) : finish current []=current := by
  simp [finish,native,conjugated,putWord,setTape]

private theorem test_end (current : Tapes 60 2) (front : List (Fin 6))
    (sourceReady : current.tape 56=putWord (fun _ => blank) 0 front ∧ current.head 56=front.length) :
    test current.reads=false := by
  simp only [test,Tapes.reads,sourceReady.1,sourceReady.2]
  rw [putWord_outside _ _ _ _ (Or.inr (by omega))]
  rfl

private theorem record_test (current : Tapes 60 2) (front : List (Fin 6)) (pair : Pair) (rest : List Pair)
    (sourceReady : current.tape 56=putWord (fun _ => blank) 0 (front++native (pair::rest)) ∧
      current.head 56=front.length) : test current.reads=true := by
  simp only [test,Tapes.reads,sourceReady.1,sourceReady.2]
  have sourceView := WordSegments.middle (fun _ => (blank : Fin 6)) 0 front (complex pair.1 pair.2) (native rest)
  simp only [native,List.flatMap_cons,zero_add] at sourceView
  have firstCell := congrFun sourceView (front.length : ℤ)
  cases realWord : pair.1 with
  | nil =>
    simp only [complex,DelimitedRadixRecord.field,realWord,List.map_nil,List.nil_append,List.singleton_append,putWord_head,native,List.flatMap_cons,List.append_assoc] at firstCell ⊢
    rw [←firstCell]
    simp [separator,blank,Fin.ext_iff]
  | cons digit digits =>
    simp only [complex,DelimitedRadixRecord.field,realWord,List.map_cons,List.cons_append,putWord_head,native,List.flatMap_cons,List.append_assoc] at firstCell ⊢
    rw [←firstCell]
    have nonblank : RadixDigits.digitSymbol digit ≠ (blank : Fin 6) := by
      intro equal
      have values := congrArg Fin.val equal
      change digit.val+4=0 at values
      omega
    exact decide_eq_true nonblank

/-- Literal source scanning drives the complete conjugation loop. Even empty
arrays and zero-width fields are supported; each empty field still has its
physical separator. All other tapes and heads are preserved exactly. -/
theorem runs_array (pairs : List Pair) (front : List (Fin 6)) (current : Tapes 60 2) (width : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width)
    (sourceReady : current.tape 56=putWord (fun _ => blank) 0 (front++native pairs) ∧ current.head 56=front.length)
    (coreBlank : ∀ index : Fin 6,current.head (ChirpConjugateRecord.slots index)=0 ∧
      current.tape (ChirpConjugateRecord.slots index)=(fun _ => blank)) :
    HoareTime program (· = current) (· = finish current pairs) ((24*width+83)*pairs.length) := by
  induction pairs generalizing front current with
  | nil =>
    intro initial equal
    subst initial
    refine ⟨0,current.start program,by simp,rfl,?_,?_⟩
    · exact while_step_exit ChirpConjugateRecord.program test current (test_end current front (by simpa [native] using sourceReady))
    · exact (finish_nil current).symm
  | cons pair rest inductionHypothesis =>
    let context : Context 2 := ⟨fun _ => blank,0,front,native rest,pair.1,pair.2⟩
    have contextTape : context.tape=current.tape 56 := by
      simpa only [context,Context.tape,native,List.flatMap_cons,List.append_assoc] using sourceReady.1.symm
    have contextHead : context.start=current.head 56 := by
      simpa only [context,Context.start,zero_add] using sourceReady.2.symm
    have fieldRun := ChirpConjugateRecord.runs current context width (fieldWidths pair (by simp))
      ⟨contextTape.symm,contextHead.symm⟩ coreBlank
    rw [ChirpConjugateRecord.output_eq current context coreBlank] at fieldRun
    have fieldEndpoint : ChirpConjugateRecord.streamOutput current context=finish current [pair] := by
      have sourcesEquation : ChirpConjugateRecord.sources context=pairSources pair := rfl
      unfold ChirpConjugateRecord.streamOutput finish
      rw [contextTape,sourcesEquation]
      simp [native,conjugated,context,Context.start,ChirpConjugateRecord.sources,pairSources,
        DelimitedRadixRecord.complex,DelimitedRadixRecord.field,sourceReady.2,Nat.cast_add,add_assoc]
    rw [fieldEndpoint] at fieldRun
    have nextCore := ChirpConjugateRecord.core_blank current context
    rw [ChirpConjugateRecord.output_eq current context coreBlank,fieldEndpoint] at nextCore
    have nextSource : (finish current [pair]).tape 56=
        putWord (fun _ => blank) 0 ((front++complex pair.1 pair.2)++native rest) ∧
        (finish current [pair]).head 56=(front++complex pair.1 pair.2).length := by
      simp only [finish,setTape,Function.update_self,show (56 : Fin 60) ≠ 58 by decide,
        Function.update_of_ne,sourceReady.1,sourceReady.2,native,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.length_append,Nat.cast_add,List.append_assoc]
      exact ⟨rfl,rfl⟩
    have tailRun := inductionHypothesis (front++complex pair.1 pair.2) (finish current [pair])
      (fun next member => fieldWidths next (List.mem_cons_of_mem pair member)) nextSource nextCore
    rw [finish_append] at tailRun
    simp only [List.singleton_append] at tailRun
    intro initial equal
    subst initial
    obtain ⟨bodyElapsed,bodyConfig,bodyBound,bodyExecuted,bodyHalted,bodyEndpoint⟩ := fieldRun _ rfl
    obtain ⟨tailElapsed,finalConfig,tailBound,tailExecuted,finalHalted,finalEndpoint⟩ := tailRun _ bodyEndpoint
    have firstIteration := while_run_iteration ChirpConjugateRecord.program test current
      (record_test current front pair rest sourceReady) bodyExecuted bodyHalted
    refine ⟨bodyElapsed+2+tailElapsed,finalConfig,?_,?_,finalHalted,finalEndpoint⟩
    · simp only [List.length_cons]
      nlinarith
    · unfold program
      rw [run_add,firstIteration]
      exact tailExecuted

def resultPairs (pairs : List Pair) : List Pair := pairs.map fun pair =>
  (words 0 (pairSources pair),words 1 (pairSources pair))

theorem conjugated_native (pairs : List Pair) : conjugated pairs=native (resultPairs pairs) := by
  simp only [conjugated,native,resultPairs,List.flatMap_map]

theorem result_widths (pairs : List Pair) (width : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width) :
    ∀ pair ∈ resultPairs pairs,pair.1.length=width ∧ pair.2.length=width := by
  intro pair member
  obtain ⟨sourcePair,sourceMember,rfl⟩ := List.mem_map.mp member
  have widths : ∀ index,(pairSources sourcePair index).length=width := by
    intro index
    dsimp [pairSources]
    split_ifs <;> first | exact (fieldWidths sourcePair sourceMember).1 | exact (fieldWidths sourcePair sourceMember).2
  exact ⟨ChirpConjugateNumerator.words_length 0 _ width widths,ChirpConjugateNumerator.words_length 1 _ width widths⟩

theorem native_length (pairs : List Pair) (width : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width) :
    (native pairs).length=2*(width+1)*pairs.length := by
  induction pairs with
  | nil => simp [native]
  | cons pair rest inductionHypothesis =>
    obtain ⟨realWidth,imaginaryWidth⟩ := fieldWidths pair (by simp)
    have restLength := inductionHypothesis (fun next member => fieldWidths next (List.mem_cons_of_mem pair member))
    simp only [native,List.flatMap_cons,List.length_append,DelimitedRadixRecord.complex_length _ _ _ realWidth imaginaryWidth,
      List.length_cons] at restLength ⊢
    nlinarith

theorem conjugated_length (pairs : List Pair) (width : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width) :
    (conjugated pairs).length=(native pairs).length := by
  rw [conjugated_native,native_length (resultPairs pairs) width (result_widths pairs width fieldWidths),
    native_length pairs width fieldWidths]
  simp only [resultPairs,List.length_map]

/-- Whole-array runtime is paid by actual source cells, including the two
separators per record; a record-count clock is unnecessary. -/
theorem runs_array_volume (pairs : List Pair) (front : List (Fin 6)) (current : Tapes 60 2) (width : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width)
    (sourceReady : current.tape 56=putWord (fun _ => blank) 0 (front++native pairs) ∧ current.head 56=front.length)
    (coreBlank : ∀ index : Fin 6,current.head (ChirpConjugateRecord.slots index)=0 ∧
      current.tape (ChirpConjugateRecord.slots index)=(fun _ => blank)) :
    HoareTime program (· = current) (· = finish current pairs) (42*(native pairs).length) := by
  apply (runs_array pairs front current width fieldWidths sourceReady coreBlank).consequence
    (fun _ ready => ready) (fun _ finished => finished)
  rw [native_length pairs width fieldWidths]
  nlinarith

def value (widthPred precision : ℕ) (pair : Pair) : ℂ :=
  ButterflySigned.complexValue (ButterflySigned.signedValue widthPred pair.1)
    (ButterflySigned.signedValue widthPred pair.2) precision

/-- Decode the actual emitted array: every coordinate is exactly conjugated
at the original denominator, with no extra numerical error. -/
theorem result_values (pairs : List Pair) (widthPred precision : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=widthPred+1 ∧ pair.2.length=widthPred+1)
    (imaginaryNotMinimum : ∀ pair ∈ pairs,ButterflySigned.signedValue widthPred pair.2 ≠ -(2^widthPred : ℕ)) :
    (resultPairs pairs).map (value widthPred precision) =
      pairs.map (fun pair => (starRingEnd ℂ) (value widthPred precision pair)) := by
  simp only [resultPairs,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro pair member
  have widths : ∀ index,(pairSources pair index).length=widthPred+1 := by
    intro index
    dsimp [pairSources]
    split_ifs <;> first | exact (fieldWidths pair member).1 | exact (fieldWidths pair member).2
  exact ChirpConjugateNumerator.words_conjugate (pairSources pair) widthPred precision widths
    (imaginaryNotMinimum pair member)

end
end IntegerMultBounds.Machine.ChirpConjugateArray
