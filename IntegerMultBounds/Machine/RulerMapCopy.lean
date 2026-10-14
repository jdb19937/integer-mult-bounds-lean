module

public import IntegerMultBounds.Machine.RulerReverseCopy

/-! Ruler-bounded copying with a fixed symbol map, including backwards field
reads. Mapping is performed by actual write transitions and costs no extra
pass. Source/ruler cells and all destination background cells are retained. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RulerMapCopy
variable {alphabet : ℕ}
open RulerCopy (cfg)
open CopyCells (cells zeroFill)

def program (convert : Fin (alphabet+4) → Fin (alphabet+4)) : Program 3 1 alphabet where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols =>
    if symbols 0=blank then none
    else some (0,fun slot => if slot=2 then (convert (zeroFill (symbols 1)),.right) else (symbols slot,.right))

theorem copy_step (convert : Fin (alphabet+4) → Fin (alphabet+4))
    (ruler source destination : ℤ → Fin (alphabet+4)) (rulerHead sourceHead destinationHead : ℤ)
    (rulerLive : ruler rulerHead≠blank) :
    step (program convert) (cfg ruler source destination rulerHead sourceHead destinationHead) =
      some (cfg ruler source (Function.update destination destinationHead (convert (zeroFill (source sourceHead))))
        (rulerHead+1) (sourceHead+1) (destinationHead+1)) := by
  unfold step
  simp only [cfg,program,rulerLive,↓reduceIte,Move.offset]
  congr 1
  congr 1
  · funext slot; fin_cases slot <;> simp
  · funext slot position
    fin_cases slot <;> simp [Function.update_apply,eq_comm]
    all_goals try (intro samePosition; rw [samePosition])

theorem copy_run (convert : Fin (alphabet+4) → Fin (alphabet+4))
    (ruler source destination : ℤ → Fin (alphabet+4)) (rulerHead sourceHead destinationHead : ℤ) (count : ℕ)
    (rulerLive : ∀ index : ℕ,index<count → ruler (rulerHead+index)≠blank) :
    run (program convert) count (cfg ruler source destination rulerHead sourceHead destinationHead) =
      some (cfg ruler source (putWord destination destinationHead ((cells source sourceHead count).map convert))
        (rulerHead+count) (sourceHead+count) (destinationHead+count)) := by
  induction count generalizing rulerHead sourceHead destinationHead destination with
  | zero => simp [run,cells,putWord]
  | succ count inductionHypothesis =>
    rw [run,copy_step _ _ _ _ _ _ _ (by simpa using rulerLive 0 (by omega))]
    simp only [Option.bind_some]
    rw [inductionHypothesis (Function.update destination destinationHead (convert (zeroFill (source sourceHead))))
      (rulerHead+1) (sourceHead+1) (destinationHead+1) (fun index bound => by
        rw [show rulerHead+1+(index : ℤ)=rulerHead+((index+1 : ℕ) : ℤ) by push_cast; ring]
        exact rulerLive (index+1) (by omega))]
    rw [cells,List.map_cons,putWord_cons]
    congr 2 <;> push_cast <;> ring

theorem copy_hoare (convert : Fin (alphabet+4) → Fin (alphabet+4))
    (ruler source destination : ℤ → Fin (alphabet+4)) (rulerHead sourceHead destinationHead : ℤ)
    (rulerSymbols : List (Fin (alphabet+4))) (rulerNonblank : ∀ symbol ∈ rulerSymbols,symbol≠blank)
    (rulerEnd : ruler (rulerHead+rulerSymbols.length)=blank) :
    HoareTime (program convert)
      (· = (cfg (putWord ruler rulerHead rulerSymbols) source destination rulerHead sourceHead destinationHead).tapes)
      (· = (cfg (putWord ruler rulerHead rulerSymbols) source
        (putWord destination destinationHead ((cells source sourceHead rulerSymbols.length).map convert))
        (rulerHead+rulerSymbols.length) (sourceHead+rulerSymbols.length) (destinationHead+rulerSymbols.length)).tapes)
      rulerSymbols.length := by
  rintro current rfl
  refine ⟨rulerSymbols.length,_,le_rfl,?_,?_,rfl⟩
  · exact copy_run convert (putWord ruler rulerHead rulerSymbols) source destination rulerHead sourceHead destinationHead
      rulerSymbols.length (fun index bound =>
        rulerNonblank _ (ReturnOrigin.putWord_mem ruler rulerHead rulerSymbols (rulerHead+index) ⟨by omega,by omega⟩))
  · simp [step,program,cfg,putWord_outside _ _ _ _ (Or.inr (le_refl _)),rulerEnd]

def reverseProgram (convert : Fin (alphabet+4) → Fin (alphabet+4)) :=
  Reflection.program (program convert) RulerReverseCopy.mask

theorem reverse_hoare (convert : Fin (alphabet+4) → Fin (alphabet+4))
    (ruler source destination : ℤ → Fin (alphabet+4)) (rulerHead sourceHead destinationHead : ℤ)
    (rulerSymbols : List (Fin (alphabet+4))) (rulerNonblank : ∀ symbol ∈ rulerSymbols,symbol≠blank)
    (rulerEnd : ruler (rulerHead+rulerSymbols.length)=blank) :
    HoareTime (reverseProgram convert)
      (· = (cfg (putWord ruler rulerHead rulerSymbols) source destination rulerHead sourceHead destinationHead).tapes)
      (· = (cfg (putWord ruler rulerHead rulerSymbols) source
        (putWord destination destinationHead ((cells (fun position => source (-position)) (-sourceHead) rulerSymbols.length).map convert))
        (rulerHead+rulerSymbols.length) (sourceHead-rulerSymbols.length) (destinationHead+rulerSymbols.length)).tapes)
      rulerSymbols.length := by
  have copied := copy_hoare convert ruler (fun position => source (-position)) destination rulerHead (-sourceHead)
    destinationHead rulerSymbols rulerNonblank rulerEnd
  have reflected := Reflection.hoare copied RulerReverseCopy.mask
  apply reflected.consequence
  · intro current ready
    refine ⟨_,rfl,?_⟩
    rw [RulerReverseCopy.reflected_bank]
    simpa only [neg_neg] using ready
  · intro current ⟨original,ready,reflectedReady⟩
    rw [ready,RulerReverseCopy.reflected_bank] at reflectedReady
    simpa only [neg_neg,neg_add_rev,sub_eq_add_neg,add_comm] using reflectedReady
  · rfl

/-- Read a contiguous public field backwards and recode each copied symbol.
Both boundaries may be adjacent to other records; the independent ruler alone
controls stopping. The destination contains exactly the converted LSB word. -/
theorem field_hoare (convert : Fin (alphabet+4) → Fin (alphabet+4))
    (ruler background destination : ℤ → Fin (alphabet+4)) (rulerHead origin destinationHead : ℤ)
    (field : List Bool) (rulerSymbols : List (Fin (alphabet+4)))
    (rulerLength : rulerSymbols.length=field.length) (rulerNonblank : ∀ symbol ∈ rulerSymbols,symbol≠blank)
    (rulerEnd : ruler (rulerHead+rulerSymbols.length)=blank) :
    HoareTime (reverseProgram convert)
      (· = (cfg (putWord ruler rulerHead rulerSymbols) (putWord background origin (field.map bitSymbol)) destination
        rulerHead (origin+field.length-1) destinationHead).tapes)
      (· = (cfg (putWord ruler rulerHead rulerSymbols) (putWord background origin (field.map bitSymbol))
        (putWord destination destinationHead ((field.reverse.map bitSymbol).map convert))
        (rulerHead+field.length) (origin-1) (destinationHead+field.length)).tapes) field.length := by
  have copied := reverse_hoare convert ruler (putWord background origin (field.map bitSymbol)) destination
    rulerHead (origin+field.length-1) destinationHead rulerSymbols rulerNonblank rulerEnd
  rw [rulerLength,RulerReverseCopy.reversed_field] at copied
  have sourceEnd : origin+(field.length : ℤ)-1-field.length=origin-1 := by omega
  simpa only [sourceEnd] using copied

end IntegerMultBounds.Machine.RulerMapCopy
