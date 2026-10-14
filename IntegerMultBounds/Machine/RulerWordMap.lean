module

public import IntegerMultBounds.Machine.RulerMapCopy
public import IntegerMultBounds.Machine.RecoverWorkspace

/-! Reusable fixed word recoding with all three heads returned to origin.
Only a same-length ruler and the original source word are supplied; the
converted destination is initially blank and is physically written. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RulerWordMap
noncomputable section
variable {alphabet : ℕ}
open SharedPlacementAlphabet (setTape)
open RecoverWorkspace (atProgram)

def word (symbols : List (Fin (alphabet+4))) := putWord (fun _ => blank) 0 symbols

def bank (ruler source destination : ℤ → Fin (alphabet+4)) (rulerHead sourceHead destinationHead : ℤ) :=
  (RulerCopy.cfg ruler source destination rulerHead sourceHead destinationHead).tapes

def program (convert : Fin (alphabet+4) → Fin (alphabet+4)) :=
  seq (seq (seq (RulerMapCopy.program convert)
    (atProgram (ReturnOrigin.program (a := alphabet)) (0 : Fin 3)))
    (atProgram (ReturnOrigin.program (a := alphabet)) (1 : Fin 3)))
    (atProgram (ReturnOrigin.program (a := alphabet)) (2 : Fin 3))

def input (symbols : List (Fin (alphabet+4))) :=
  bank (word (List.replicate symbols.length (bitSymbol true))) (word symbols) (fun _ => blank) 0 0 0

def output (convert : Fin (alphabet+4) → Fin (alphabet+4)) (symbols : List (Fin (alphabet+4))) :=
  bank (word (List.replicate symbols.length (bitSymbol true))) (word symbols) (word (symbols.map convert)) 0 0 0

/-- Unlike Boolean-only cell extraction, this works for native radix digits
and every other nonblank word over the actual machine alphabet. -/
theorem cells_word (background : ℤ → Fin (alphabet+4)) (origin : ℤ) (symbols : List (Fin (alphabet+4)))
    (nonblank : ∀ symbol ∈ symbols,symbol≠blank) :
    CopyCells.cells (putWord background origin symbols) origin symbols.length=symbols := by
  induction symbols generalizing background origin with
  | nil => rfl
  | cons symbol rest inductionHypothesis =>
    rw [List.length_cons,CopyCells.cells,putWord_head,putWord_cons,
      inductionHypothesis _ _ (fun value member => nonblank value (by simp [member]))]
    simp [CopyCells.zeroFill,nonblank symbol (by simp)]

private theorem set_bank (ruler source destination updated : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead destinationHead updatedHead : ℤ) (slot : Fin 3) :
    setTape (bank ruler source destination rulerHead sourceHead destinationHead) slot updated updatedHead=
      bank (if slot=0 then updated else ruler) (if slot=1 then updated else source) (if slot=2 then updated else destination)
        (if slot=0 then updatedHead else rulerHead) (if slot=1 then updatedHead else sourceHead)
        (if slot=2 then updatedHead else destinationHead) := by
  fin_cases slot <;> unfold bank setTape RulerCopy.cfg Config.tapes
  all_goals congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem reset_at (slot : Fin 3) (ruler source destination : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead destinationHead : ℤ) (symbols : List (Fin (alphabet+4)))
    (nonblank : ∀ symbol ∈ symbols,symbol≠blank)
    (headReady : (bank ruler source destination rulerHead sourceHead destinationHead).head slot=symbols.length)
    (tapeReady : (bank ruler source destination rulerHead sourceHead destinationHead).tape slot=word symbols) :
    HoareTime (atProgram ReturnOrigin.program slot) (· = bank ruler source destination rulerHead sourceHead destinationHead)
      (· = setTape (bank ruler source destination rulerHead sourceHead destinationHead) slot (word symbols) 0) (symbols.length+2) := by
  have returned := RecoverWorkspace.return_at slot (bank ruler source destination rulerHead sourceHead destinationHead)
    symbols nonblank headReady tapeReady
  simpa only [RecoverWorkspace.restored,tapeReady,word] using returned

/-- One fixed program recodes the full word, preserves the source and ruler,
and returns all heads. No converted word is present in its input. -/
theorem runs (convert : Fin (alphabet+4) → Fin (alphabet+4)) (symbols : List (Fin (alphabet+4)))
    (nonblank : ∀ symbol ∈ symbols,symbol≠blank)
    (convertedNonblank : ∀ symbol ∈ symbols,convert symbol≠blank) :
    HoareTime (program convert) (· = input symbols) (· = output convert symbols) (4*symbols.length+9) := by
  let rulerSymbols := List.replicate symbols.length (bitSymbol (a := alphabet) true)
  have rulerNonblank : ∀ symbol ∈ rulerSymbols,symbol≠blank := by
    intro symbol member
    have equal : symbol=bitSymbol true := List.eq_of_mem_replicate member
    subst symbol
    simp [bitSymbol,blank,Fin.ext_iff]
  have outputNonblank : ∀ symbol ∈ symbols.map convert,symbol≠blank := by
    intro symbol member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact convertedNonblank original originalMember
  have copied := RulerMapCopy.copy_hoare convert (fun _ => (blank : Fin (alphabet+4))) (word symbols) (fun _ => blank)
    0 0 0 rulerSymbols rulerNonblank rfl
  simp only [rulerSymbols,List.length_replicate,zero_add,word] at copied
  rw [cells_word _ _ symbols nonblank] at copied
  have rulerReset := reset_at (0 : Fin 3) (word rulerSymbols) (word symbols) (word (symbols.map convert))
    symbols.length symbols.length symbols.length rulerSymbols rulerNonblank
    (by simp [bank,RulerCopy.cfg,Config.tapes,rulerSymbols]) rfl
  have sourceReset := reset_at (1 : Fin 3) (word rulerSymbols) (word symbols) (word (symbols.map convert))
    0 symbols.length symbols.length symbols nonblank rfl rfl
  have outputReset := reset_at (2 : Fin 3) (word rulerSymbols) (word symbols) (word (symbols.map convert))
    0 0 symbols.length (symbols.map convert) outputNonblank (by simp [bank,RulerCopy.cfg,Config.tapes]) rfl
  simp only [set_bank,List.length_map] at rulerReset sourceReset outputReset
  unfold program input output bank word
  exact ((copied.seq rulerReset).seq sourceReset).seq outputReset |>.consequence
    (fun _ ready => ready) (fun _ finished => finished) (by simp only [rulerSymbols,List.length_replicate]; omega)

end
end IntegerMultBounds.Machine.RulerWordMap
