module

public import IntegerMultBounds.Machine.DoubleRulerErase

/-! Exact section 8 residual precision on the actual unary control tapes.
Two cells per chunk-ruler cell and two per exponent-ruler cell are erased,
then four fixed scaling cells are removed. Both retained length rulers and the
shortened precision ruler return to origin; no residual descriptor is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverResidualPrecision
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open RecoverWorkspace (atProgram)
open SharedPlacementAlphabet (setTape)

def bank (precision chunk exponent : ℤ → Fin (alphabet+4)) (precisionHead chunkHead exponentHead : ℤ) : Tapes 3 alphabet :=
  ⟨![precisionHead,chunkHead,exponentHead],![precision,chunk,exponent]⟩

@[simp] private theorem bank_head (precision chunk exponent : ℤ → Fin (alphabet+4))
    (precisionHead chunkHead exponentHead : ℤ) (slot : Fin 3) :
    (bank precision chunk exponent precisionHead chunkHead exponentHead).head slot = ![precisionHead,chunkHead,exponentHead] slot := rfl

@[simp] private theorem bank_tape (precision chunk exponent : ℤ → Fin (alphabet+4))
    (precisionHead chunkHead exponentHead : ℤ) (slot : Fin 3) :
    (bank precision chunk exponent precisionHead chunkHead exponentHead).tape slot = ![precision,chunk,exponent] slot := rfl

def exponentSlots : Fin (2+1) ≃ Fin 3 where
  toFun := ![0,2,1]
  invFun := ![0,2,1]
  left_inv := by decide
  right_inv := by decide

def eraseOne : Program 3 2 alphabet := atProgram RecoverRulerTrim.eraseCell (0 : Fin 3)
def eraseFour : Program 3 8 alphabet := seq (seq (seq eraseOne eraseOne) eraseOne) eraseOne

def program : Program 3 25 alphabet := seq (seq (seq (seq (seq (seq (seq
  (atProgram (MultiplicationInputSplit.shift .left) (0 : Fin 3)) (extend DoubleRulerErase.program 1))
  (atProgram ReturnOrigin.program (1 : Fin 3)))
  (Placement.placed DoubleRulerErase.program exponentSlots))
  (atProgram ReturnOrigin.program (2 : Fin 3))) eraseFour)
  (atProgram (MultiplicationInputSplit.shift .right) (0 : Fin 3)))
  (atProgram ReturnOrigin.program (0 : Fin 3))

def input (precision chunkWidth lengthExponent : ℕ) : Tapes 3 alphabet :=
  bank (word (List.replicate precision true)) (word (List.replicate chunkWidth true))
    (word (List.replicate lengthExponent true)) precision 0 0

def output (precision chunkWidth lengthExponent : ℕ) : Tapes 3 alphabet :=
  bank (word (List.replicate (precision-(2*chunkWidth+4+2*lengthExponent)) true))
    (word (List.replicate chunkWidth true)) (word (List.replicate lengthExponent true)) 0 0 0

private theorem set_bank (precision chunk exponent updated : ℤ → Fin (alphabet+4))
    (precisionHead chunkHead exponentHead updatedHead : ℤ) (slot : Fin 3) :
    setTape (bank precision chunk exponent precisionHead chunkHead exponentHead) slot updated updatedHead =
      bank (if slot = 0 then updated else precision) (if slot = 1 then updated else chunk)
        (if slot = 2 then updated else exponent) (if slot = 0 then updatedHead else precisionHead)
        (if slot = 1 then updatedHead else chunkHead) (if slot = 2 then updatedHead else exponentHead) := by
  fin_cases slot <;> unfold setTape bank
  all_goals congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem double_bank (precision chunk exponent : ℤ → Fin (alphabet+4)) (precisionHead chunkHead exponentHead : ℤ) :
    (DoubleRulerErase.cfg precision chunk precisionHead chunkHead 0).tapes.append
      (⟨fun _ => exponentHead,fun _ => exponent⟩ : Tapes 1 alphabet) = bank precision chunk exponent precisionHead chunkHead exponentHead := by
  unfold DoubleRulerErase.cfg Config.tapes Tapes.append bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem exponent_bank (precision chunk exponent : ℤ → Fin (alphabet+4)) (precisionHead chunkHead exponentHead : ℤ) :
    ((DoubleRulerErase.cfg precision exponent precisionHead exponentHead 0).tapes.append
      (⟨fun _ => chunkHead,fun _ => chunk⟩ : Tapes 1 alphabet)).reindex exponentSlots =
        bank precision chunk exponent precisionHead chunkHead exponentHead := by
  unfold DoubleRulerErase.cfg Config.tapes Tapes.append Tapes.reindex exponentSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem bits_nonblank (bits : List Bool) : ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem erase_one (remaining : ℕ) (chunk exponent : ℤ → Fin (alphabet+4)) :
    HoareTime (eraseOne (alphabet := alphabet))
      (· = bank (word (List.replicate (remaining+1) true)) chunk exponent remaining 0 0)
      (· = bank (word (List.replicate remaining true)) chunk exponent ((remaining : ℤ)-1) 0 0) 1 := by
  have localRun := RecoverRulerTrim.erase_cell (alphabet := alphabet) (word (List.replicate (remaining+1) true)) remaining
  rw [RecoverRulerTrim.erase_last] at localRun
  have placed := RecoverWorkspace.runs_one_at RecoverRulerTrim.eraseCell (0 : Fin 3)
    (bank (word (List.replicate (remaining+1) true)) chunk exponent remaining 0 0)
    _ _ _ _ rfl rfl localRun
  rw [set_bank] at placed
  simpa only [eraseOne,ite_true,show (0 : Fin 3) ≠ 1 by decide,show (0 : Fin 3) ≠ 2 by decide,ite_false] using placed

private theorem erase_four (remaining : ℕ) (chunk exponent : ℤ → Fin (alphabet+4)) :
    HoareTime (eraseFour (alphabet := alphabet))
      (· = bank (word (List.replicate (remaining+4) true)) chunk exponent ((remaining : ℤ)+3) 0 0)
      (· = bank (word (List.replicate remaining true)) chunk exponent ((remaining : ℤ)-1) 0 0) 7 := by
  have first := erase_one (alphabet := alphabet) (remaining+3) chunk exponent
  have second := erase_one (alphabet := alphabet) (remaining+2) chunk exponent
  have third := erase_one (alphabet := alphabet) (remaining+1) chunk exponent
  have fourth := erase_one (alphabet := alphabet) remaining chunk exponent
  norm_num only [Nat.cast_add,Nat.cast_one] at first second third
  have positionThree : (remaining : ℤ)+3-1 = remaining+2 := by omega
  have positionTwo : (remaining : ℤ)+2-1 = remaining+1 := by omega
  have positionOne : (remaining : ℤ)+1-1 = remaining := by omega
  rw [positionThree] at first
  rw [positionTwo] at second
  rw [positionOne] at third
  unfold eraseFour
  exact ((first.seq second).seq third).seq fourth

/-- Execute the complete scaling adjustment, preserving chunk and exponent
rulers. The final precision is computed by these actual erasures, and all
three heads return to origin; the boundary residual zero is supported. -/
theorem runs_adjust (precision chunkWidth lengthExponent : ℕ)
    (scalingFits : 2*chunkWidth+4+2*lengthExponent ≤ precision) :
    HoareTime (program (alphabet := alphabet)) (· = input precision chunkWidth lengthExponent)
      (· = output precision chunkWidth lengthExponent) (4 * precision + 22) := by
  let chunk := word (alphabet := alphabet) (List.replicate chunkWidth true)
  let exponent := word (alphabet := alphabet) (List.replicate lengthExponent true)
  have left := RecoverWorkspace.shift_at (0 : Fin 3) (input (alphabet := alphabet) precision chunkWidth lengthExponent) .left
  simp only [input,bank_head,bank_tape,set_bank,Move.offset,ite_true,show (0 : Fin 3) ≠ 1 by decide,
    show (0 : Fin 3) ≠ 2 by decide,ite_false] at left
  have chunks := FamilyPlacementAlphabet.extend_hoare
    (DoubleRulerErase.erase_hoare (alphabet := alphabet) precision (List.replicate chunkWidth true) (by simp; omega))
    (⟨fun _ => 0,fun _ => exponent⟩ : Tapes 1 alphabet)
  simp only [List.length_replicate] at chunks
  rw [double_bank,double_bank] at chunks
  have chunkReset := RecoverWorkspace.return_at (1 : Fin 3)
    (bank (word (List.replicate (precision-2*chunkWidth) true)) chunk exponent (((precision-2*chunkWidth : ℕ) : ℤ)-1) chunkWidth 0)
    ((List.replicate chunkWidth true).map bitSymbol) (bits_nonblank _) (by simp [bank]) rfl
  simp only [RecoverWorkspace.restored,bank_tape,set_bank,List.length_map,List.length_replicate,ite_true,
    show (1 : Fin 3) ≠ 0 by decide,show (1 : Fin 3) ≠ 2 by decide,ite_false] at chunkReset
  have exponents := hoare_place
    (DoubleRulerErase.erase_hoare (alphabet := alphabet) (precision-2*chunkWidth) (List.replicate lengthExponent true) (by simp; omega))
    exponentSlots (⟨fun _ => 0,fun _ => chunk⟩ : Tapes 1 alphabet)
  simp only [List.length_replicate] at exponents
  rw [exponent_bank,exponent_bank] at exponents
  let beforeFour := precision-2*chunkWidth-2*lengthExponent
  have exponentReset := RecoverWorkspace.return_at (2 : Fin 3)
    (bank (word (List.replicate beforeFour true)) chunk exponent (((beforeFour : ℕ) : ℤ)-1) 0 lengthExponent)
    ((List.replicate lengthExponent true).map bitSymbol) (bits_nonblank _) (by simp [bank]) rfl
  simp only [RecoverWorkspace.restored,bank_tape,set_bank,List.length_map,List.length_replicate,ite_true,
    show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide,ite_false] at exponentReset
  let remaining := precision-(2*chunkWidth+4+2*lengthExponent)
  have remainingSplit : beforeFour = remaining+4 := by omega
  have four := erase_four (alphabet := alphabet) remaining chunk exponent
  have beforePosition : (((beforeFour : ℕ) : ℤ)-1) = (remaining : ℤ)+3 := by omega
  rw [← remainingSplit,← beforePosition] at four
  have right := RecoverWorkspace.shift_at (0 : Fin 3)
    (bank (word (List.replicate remaining true)) chunk exponent ((remaining : ℤ)-1) 0 0) .right
  simp [set_bank,Move.offset] at right
  have returned := RecoverWorkspace.return_at (0 : Fin 3)
    (bank (word (List.replicate remaining true)) chunk exponent remaining 0 0)
    ((List.replicate remaining true).map bitSymbol) (bits_nonblank _) (by simp [bank]) rfl
  simp [RecoverWorkspace.restored,set_bank] at returned
  unfold program input output
  apply (((((((left.seq chunks).seq chunkReset).seq exponents).seq exponentReset).seq four).seq right).seq returned).consequence
    (fun _ ready => ready) (fun _ finished => finished)
  omega

end
end IntegerMultBounds.Machine.RecoverResidualPrecision
