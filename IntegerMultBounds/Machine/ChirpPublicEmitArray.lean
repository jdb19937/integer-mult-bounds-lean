module

public import IntegerMultBounds.Machine.ChirpPublicEmitField

/-! Serialize all native delimiter-terminated fields to contiguous public MSB
bits. Widths are discovered from actual source separators, and the actual
blank source end terminates the loop. No count/width descriptor is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicEmitArray
noncomputable section
open ChirpPublicDecode (live publicWord)
open DelimitedRadixRecord (field)

def serialized (fields : List (List (Fin 2))) := fields.flatMap field
def publicBits (fields : List (List (Fin 2))) := fields.flatMap publicWord
def word (symbols : List (Fin 6)) := putWord (fun _ => (blank : Fin 6)) 0 symbols

def test (symbols : Fin 2 → Fin 6) : Bool := decide (symbols 0≠blank)
def program := whileLoop ChirpPublicEmitField.program test

private theorem source_overwrite (done : List (Fin 6)) (digits : List (Fin 2)) (rest : List (List (Fin 2))) :
    putWord (word (done++serialized (digits::rest))) done.length (digits.map RadixDigits.digitSymbol)=
      word (done++serialized (digits::rest)) := by
  have middle := WordSegments.middle (fun _ => (blank : Fin 6)) 0 done (digits.map RadixDigits.digitSymbol)
    (separator::serialized rest)
  simpa only [word,serialized,field,List.flatMap_cons,zero_add,List.singleton_append,List.append_assoc] using middle

private theorem end_separator (done : List (Fin 6)) (digits : List (Fin 2)) (rest : List (List (Fin 2))) :
    word (done++serialized (digits::rest)) (done.length+digits.length)=separator := by
  have middle := WordSegments.middle (fun _ => (blank : Fin 6)) 0 (done++digits.map RadixDigits.digitSymbol)
    [separator] (serialized rest)
  have atCell := congrFun middle ((done++digits.map RadixDigits.digitSymbol).length : ℤ)
  simp only [zero_add,putWord_head,List.length_append,List.length_map,Nat.cast_add] at atCell
  simpa only [word,serialized,field,List.flatMap_cons,List.append_assoc,List.singleton_append] using atCell.symm

private theorem test_end (done : List (Fin 6)) (destination : ℤ → Fin 6) (destinationHead : ℤ) :
    test (Copy.tapes (word done) destination done.length destinationHead).reads=false := by
  change decide (word done done.length≠blank)=false
  rw [word,putWord_outside _ _ _ _ (Or.inr (by omega))]
  rfl

private theorem test_field (done : List (Fin 6)) (digits : List (Fin 2)) (rest : List (List (Fin 2)))
    (destination : ℤ → Fin 6) (destinationHead : ℤ) :
    test (Copy.tapes (word (done++serialized (digits::rest))) destination done.length destinationHead).reads=true := by
  change decide (word (done++serialized (digits::rest)) done.length≠blank)=true
  cases digits with
  | nil =>
    have middle := WordSegments.middle (fun _ => (blank : Fin 6)) 0 done [separator] (serialized rest)
    have atCell := congrFun middle (done.length : ℤ)
    simp only [zero_add,putWord_head] at atCell
    have sourceCell : word (done++serialized ([]::rest)) done.length=separator := by
      simpa only [word,serialized,field,List.flatMap_cons,List.map_nil,List.nil_append,List.append_assoc] using atCell.symm
    rw [sourceCell]
    decide
  | cons digit digits =>
    have atCell := congrFun (source_overwrite done (digit::digits) rest) (done.length : ℤ)
    rw [List.map_cons,putWord_head] at atCell
    rw [←atCell]
    apply decide_eq_true
    intro equal
    have values := congrArg Fin.val equal
    change digit.val+4=0 at values
    omega

/-- Emit a whole field array, including empty arrays and empty individual
fields. All data and delimiter cells are retained literally; source widths
may vary, and the destination contains only public bits with no delimiters. -/
theorem runs_array (fields : List (List (Fin 2))) (done : List (Fin 6))
    (destination : ℤ → Fin 6) (destinationHead : ℤ)
    (beforeStopped : live (word (done++serialized fields) (done.length-1))=false) :
    HoareTime program
      (· = Copy.tapes (word (done++serialized fields)) destination done.length destinationHead)
      (· = Copy.tapes (word (done++serialized fields))
        (putWord destination destinationHead ((publicBits fields).map bitSymbol)) (done++serialized fields).length
        (destinationHead+(publicBits fields).length)) (10*(serialized fields).length) := by
  induction fields generalizing done destination destinationHead with
  | nil =>
    intro initial equal
    subst initial
    refine ⟨0,_,by simp [serialized],rfl,?_,?_⟩
    · exact while_step_exit ChirpPublicEmitField.program test _ (by simpa [serialized] using test_end done destination destinationHead)
    · simp [serialized,publicBits,putWord,Config.tapes,Tapes.start]
  | cons digits rest inductionHypothesis =>
    have fieldRun := ChirpPublicEmitField.runs_field (word (done++serialized (digits::rest))) destination
      done.length destinationHead digits beforeStopped (end_separator done digits rest)
    rw [source_overwrite] at fieldRun
    have nextSource : word ((done++field digits)++serialized rest)=word (done++serialized (digits::rest)) := by
      simp [serialized,List.append_assoc]
    have nextPosition : (((done++field digits).length : ℕ) : ℤ)=done.length+digits.length+1 := by
      simp only [List.length_append,DelimitedRadixRecord.field_length,Nat.cast_add,Nat.cast_one]
      ring
    have nextStopped : live (word ((done++field digits)++serialized rest) ((done++field digits).length-1))=false := by
      rw [nextSource,nextPosition]
      have position : (done.length : ℤ)+digits.length+1-1=done.length+digits.length := by omega
      rw [position,end_separator]
      decide
    have tailRun := inductionHypothesis (done++field digits)
      (putWord destination destinationHead ((publicWord digits).map bitSymbol)) (destinationHead+digits.length) nextStopped
    rw [nextSource,nextPosition] at tailRun
    intro initial equal
    subst initial
    obtain ⟨bodyElapsed,bodyConfig,bodyBound,bodyExecuted,bodyHalted,bodyEndpoint⟩ := fieldRun _ rfl
    obtain ⟨tailElapsed,finalConfig,tailBound,tailExecuted,finalHalted,finalEndpoint⟩ := tailRun _ bodyEndpoint
    have firstIteration := while_run_iteration ChirpPublicEmitField.program test _
      (test_field done digits rest destination destinationHead) bodyExecuted bodyHalted
    refine ⟨bodyElapsed+2+tailElapsed,finalConfig,?_,?_,finalHalted,?_⟩
    · simp only [serialized,List.flatMap_cons,List.length_append,DelimitedRadixRecord.field_length] at tailBound ⊢
      omega
    · unfold program
      rw [run_add,firstIteration]
      exact tailExecuted
    · have destinationPosition : destinationHead+digits.length=destinationHead+((publicWord digits).map (bitSymbol (a := 2))).length := by
        rw [List.length_map,ChirpPublicDecode.public_length]
      rw [destinationPosition,putWord_append_forward] at finalEndpoint
      simpa only [publicBits,serialized,List.flatMap_cons,List.map_append,List.length_append,List.length_map,
        ChirpPublicDecode.public_length,Nat.cast_add,List.append_assoc,add_assoc] using finalEndpoint

end
end IntegerMultBounds.Machine.ChirpPublicEmitArray
