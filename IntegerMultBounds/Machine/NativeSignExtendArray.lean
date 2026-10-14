module

public import IntegerMultBounds.Machine.NativeSignExtendField

@[expose] public section
namespace IntegerMultBounds.Machine.NativeSignExtendArray
noncomputable section

def native (fields : List (List (Fin 2))) := fields.flatMap DelimitedRadixRecord.field
def widened (fields : List (List (Fin 2))) (targetWidth : ℕ) :=
  native (fields.map (fun field => NativeSignExtend.extended field targetWidth))
def bank (ruler source destination : ℤ → Fin 6) (sourceHead destinationHead : ℤ) : Tapes 5 2 :=
  ⟨![0,sourceHead,destinationHead,0,0], ![ruler,source,destination,fun _ => blank,fun _ => blank]⟩
def word (symbols : List (Fin 6)) := putWord (fun _ => blank) 0 symbols
def test (symbols : Fin 5 → Fin 6) := decide (symbols 1 ≠ blank)
def program := whileLoop NativeSignExtendField.program test
def cost (fields : List (List (Fin 2))) (targetWidth : ℕ) :=
  (9*targetWidth+41)*fields.length+5*(fields.map List.length).sum

private theorem source_overwrite (done : List (Fin 6)) (field : List (Fin 2)) (rest : List (List (Fin 2))) :
    putWord (word (done++native (field::rest))) done.length (field.map RadixDigits.digitSymbol) =
      word (done++native (field::rest)) := by
  simpa [word, native, DelimitedRadixRecord.field, List.append_assoc] using
    WordSegments.middle (fun _ => (blank : Fin 6)) 0 done (field.map RadixDigits.digitSymbol) (separator::native rest)

private theorem delimiter (done : List (Fin 6)) (field : List (Fin 2)) (rest : List (List (Fin 2))) :
    word (done++native (field::rest)) (done.length+field.length) = separator := by
  have readCell := WordSegments.get (fun _ => (blank : Fin 6)) 0
    (done++native (field::rest)) (done.length+field.length) (by
      simp [native, DelimitedRadixRecord.field])
  simpa [word, native, DelimitedRadixRecord.field, List.getElem_append, List.getElem_cons,
    show ¬done.length+field.length < done.length by omega] using readCell

private theorem test_end (ruler : ℤ → Fin 6) (done : List (Fin 6)) (destination : ℤ → Fin 6) (destinationHead : ℤ) :
    test (bank ruler (word done) destination done.length destinationHead).reads = false := by
  change decide (word done done.length ≠ blank) = false
  rw [word, putWord_outside _ _ _ _ (Or.inr (by simp))]
  rfl

private theorem test_field (ruler : ℤ → Fin 6) (done : List (Fin 6)) (field : List (Fin 2))
    (rest : List (List (Fin 2))) (destination : ℤ → Fin 6) (destinationHead : ℤ) :
    test (bank ruler (word (done++native (field::rest))) destination done.length destinationHead).reads = true := by
  change decide (word (done++native (field::rest)) done.length ≠ blank) = true
  have view := WordSegments.middle (fun _ => (blank : Fin 6)) 0 done
    (DelimitedRadixRecord.field field) (native rest)
  simp only [zero_add] at view
  have firstCell := congrFun view (done.length : ℤ)
  cases field with
  | nil =>
    simp only [DelimitedRadixRecord.field, List.map_nil, List.nil_append, putWord_head] at firstCell
    simp only [word, native, List.flatMap_cons, DelimitedRadixRecord.field, List.map_nil, List.nil_append,
      List.append_assoc] at firstCell ⊢
    rw [←firstCell]
    decide
  | cons digit restDigits =>
    simp only [DelimitedRadixRecord.field, List.map_cons, List.cons_append, putWord_head] at firstCell
    simp only [word, native, List.flatMap_cons, DelimitedRadixRecord.field, List.map_cons, List.cons_append,
      List.append_assoc] at firstCell ⊢
    rw [←firstCell]
    exact decide_eq_true (NativeSignExtendField.digits_nonblank (digit::restDigits) _ (by simp))

theorem runs (fields : List (List (Fin 2))) (targetWidth : ℕ)
    (done : List (Fin 6)) (destination : ℤ → Fin 6) (destinationHead : ℤ)
    (fieldFits : ∀ field ∈ fields, field.length ≤ targetWidth) :
    HoareTime program
      (· = bank (RecoverCarryStep.word (List.replicate targetWidth true))
        (word (done++native fields)) destination done.length destinationHead)
      (· = bank (RecoverCarryStep.word (List.replicate targetWidth true))
        (word (done++native fields)) (putWord destination destinationHead (widened fields targetWidth))
        (done++native fields).length (destinationHead+(widened fields targetWidth).length))
      (cost fields targetWidth) := by
  induction fields generalizing done destination destinationHead with
  | nil =>
    intro current equal
    subst current
    refine ⟨0, _, by simp [cost], rfl, ?_, ?_⟩
    · exact while_step_exit NativeSignExtendField.program test _
        (by simpa [native] using test_end (RecoverCarryStep.word (List.replicate targetWidth true)) done destination destinationHead)
    · simp [native, widened, putWord, Config.tapes, Tapes.start]
  | cons field rest inductionHypothesis =>
    let ruler := RecoverCarryStep.word (alphabet := 2) (List.replicate targetWidth true)
    let source := word (done++native (field::rest))
    let extendedField := DelimitedRadixRecord.field (NativeSignExtend.extended field targetWidth)
    have fieldLength : extendedField.length = targetWidth+1 := by
      rw [DelimitedRadixRecord.field_length, NativeSignExtend.extended_length field targetWidth (fieldFits field (by simp))]
    have fieldRun := NativeSignExtendField.runs (bank ruler source destination done.length destinationHead) field targetWidth
      (fieldFits field (by simp)) source (source_overwrite done field rest).symm (delimiter done field rest) rfl rfl ⟨rfl,rfl⟩ ⟨rfl,rfl⟩
    have fieldEndpoint : NativeSignExtendField.output (bank ruler source destination done.length destinationHead) field targetWidth =
        bank ruler source (putWord destination destinationHead extendedField)
          (done.length+field.length+1) (destinationHead+extendedField.length) := by
      unfold NativeSignExtendField.output bank SharedPlacementAlphabet.setTape
      apply congrArg₂ Tapes.mk
      · funext slot; fin_cases slot <;> simp [fieldLength, add_assoc]
      · funext slot; fin_cases slot <;> rfl
    have fieldExact := fieldRun.consequence (fun _ ready => ready) (fun _ ready => ready.trans fieldEndpoint) le_rfl
    have sourceSame : word ((done++DelimitedRadixRecord.field field)++native rest) = source := by
      simp [source, native, List.append_assoc]
    have sourcePosition : ((done++DelimitedRadixRecord.field field).length : ℤ) = done.length+field.length+1 := by
      simp [DelimitedRadixRecord.field_length, Nat.cast_add, add_assoc]
    have tailRun := inductionHypothesis (done++DelimitedRadixRecord.field field)
      (putWord destination destinationHead extendedField) (destinationHead+extendedField.length)
      (fun next member => fieldFits next (List.mem_cons_of_mem field member))
    rw [sourceSame, sourcePosition] at tailRun
    intro current equal
    subst current
    obtain ⟨bodyElapsed, bodyConfig, bodyBound, bodyExecuted, bodyHalted, bodyEndpoint⟩ := fieldExact _ rfl
    obtain ⟨tailElapsed, finalConfig, tailBound, tailExecuted, finalHalted, finalEndpoint⟩ := tailRun _ bodyEndpoint
    have firstIteration := while_run_iteration NativeSignExtendField.program test _
      (test_field ruler done field rest destination destinationHead) bodyExecuted bodyHalted
    refine ⟨bodyElapsed+2+tailElapsed, finalConfig, ?_, ?_, finalHalted, ?_⟩
    · simp only [cost, List.length_cons, List.map_cons, List.sum_cons] at *
      nlinarith
    · unfold program
      rw [run_add, firstIteration]
      exact tailExecuted
    · rw [putWord_append_forward] at finalEndpoint
      simpa only [source, extendedField, widened, native, List.map_cons, List.flatMap_cons, List.append_assoc,
        List.length_append, Nat.cast_add, add_assoc] using finalEndpoint

theorem widened_values (fields : List (List (Fin 2))) (sourcePred targetPred : ℕ)
    (fieldWidths : ∀ field ∈ fields, field.length = sourcePred+1) (sourceFits : sourcePred ≤ targetPred) :
    (fields.map (fun field => NativeSignExtend.extended field (targetPred+1))).map (ButterflySigned.signedValue targetPred) =
      fields.map (ButterflySigned.signedValue sourcePred) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro field member
  exact NativeSignExtend.extended_signed field sourcePred targetPred (fieldWidths field member) sourceFits

end
end IntegerMultBounds.Machine.NativeSignExtendArray
