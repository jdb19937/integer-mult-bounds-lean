module

public import IntegerMultBounds.Machine.RulerMapCopy
public import IntegerMultBounds.Machine.SignExtendAdd
public import IntegerMultBounds.Machine.RecoverWorkspace
public import IntegerMultBounds.Machine.GaussianLineValue

/-! Physically widen a signed LSB bit word into blank storage, using only its
actual unary target-width ruler. Constant zero filling, counted source rewind,
signed accumulation and both final head returns are actual transitions. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpSignExtend
noncomputable section
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)
open RecoverWorkspace (atProgram)

abbrev alphabet := 2

def bank (ruler source destination : ℤ → Fin 6) (rulerHead sourceHead destinationHead : ℤ) : Tapes 3 2 :=
  (RulerCopy.cfg ruler source destination rulerHead sourceHead destinationHead).tapes

def backMask (slot : Fin 2) : Bool := decide (slot=1)
def backProgram := extend (Reflection.program (RulerAdvance.program (a := 2)) backMask) 1

def addSlots : Fin (2+1) ≃ Fin 3 where
  toFun := ![1,2,0]
  invFun := ![2,0,1]
  left_inv := by decide
  right_inv := by decide

def fill := RulerMapCopy.program (fun _ : Fin 6 => bitSymbol false)
def resetRuler := atProgram (ReturnOrigin.program (a := 2)) (0 : Fin 3)
def resetSource := atProgram (ReturnOrigin.program (a := 2)) (1 : Fin 3)
def resetDestination := atProgram (ReturnOrigin.program (a := 2)) (2 : Fin 3)
def preparedProgram := seq (seq (seq (seq fill resetRuler) backProgram) resetRuler) resetDestination

def program := seq (seq (seq preparedProgram (Placement.placed (SignExtendAdd.program 2) addSlots)) resetSource) resetDestination

def input (bits : List Bool) (targetWidth : ℕ) : Tapes 3 2 :=
  bank (word (List.replicate targetWidth true)) (word bits) (fun _ => blank) 0 0 0

def outputBits (bits : List Bool) (targetWidth : ℕ) := TwosComplement.addMod bits (List.replicate targetWidth false)
def output (bits : List Bool) (targetWidth : ℕ) : Tapes 3 2 :=
  bank (word (List.replicate targetWidth true)) (word bits) (word (outputBits bits targetWidth)) 0 0 0

private theorem bits_nonblank (bits : List Bool) : ∀ symbol ∈ bits.map (bitSymbol (a := 2)),symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem set_bank (ruler source destination updated : ℤ → Fin 6) (rulerHead sourceHead destinationHead updatedHead : ℤ)
    (slot : Fin 3) : setTape (bank ruler source destination rulerHead sourceHead destinationHead) slot updated updatedHead =
      bank (if slot=0 then updated else ruler) (if slot=1 then updated else source) (if slot=2 then updated else destination)
        (if slot=0 then updatedHead else rulerHead) (if slot=1 then updatedHead else sourceHead)
        (if slot=2 then updatedHead else destinationHead) := by
  fin_cases slot <;> unfold bank setTape RulerCopy.cfg Config.tapes
  all_goals congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem reset_at (slot : Fin 3) (ruler source destination : ℤ → Fin 6) (rulerHead sourceHead destinationHead : ℤ)
    (bits : List Bool) (headReady : (bank ruler source destination rulerHead sourceHead destinationHead).head slot=bits.length)
    (tapeReady : (bank ruler source destination rulerHead sourceHead destinationHead).tape slot=word bits) :
    HoareTime (atProgram ReturnOrigin.program slot) (· = bank ruler source destination rulerHead sourceHead destinationHead)
      (· = setTape (bank ruler source destination rulerHead sourceHead destinationHead) slot (word bits) 0) (bits.length+2) := by
  have returned := RecoverWorkspace.return_at slot (bank ruler source destination rulerHead sourceHead destinationHead)
    (bits.map bitSymbol) (bits_nonblank _) (by simpa using headReady) tapeReady
  simpa only [RecoverWorkspace.restored,tapeReady,List.length_map] using returned

private theorem advance_bank (ruler source destination : ℤ → Fin 6) (rulerHead sourceHead destinationHead : ℤ) :
    (RulerAdvance.cfg ruler source rulerHead sourceHead).tapes.append
      (⟨fun _ => destinationHead,fun _ => destination⟩ : Tapes 1 2)=bank ruler source destination rulerHead sourceHead destinationHead := by
  unfold bank RulerAdvance.cfg RulerCopy.cfg Config.tapes Tapes.append
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem reflected_bank (ruler source : ℤ → Fin 6) (rulerHead sourceHead : ℤ) :
    Reflection.tapes backMask (RulerAdvance.cfg ruler source rulerHead sourceHead).tapes=
      (RulerAdvance.cfg ruler (fun position => source (-position)) rulerHead (-sourceHead)).tapes := by
  unfold Reflection.tapes RulerAdvance.cfg Config.tapes
  congr 1
  · funext slot; fin_cases slot <;> simp [backMask,Reflection.coord]
  · funext slot position; fin_cases slot <;> simp [backMask,Reflection.coord]

private theorem backward (rulerBits : List Bool) (source destination : ℤ → Fin 6) (sourceHead destinationHead : ℤ) :
    HoareTime backProgram (· = bank (word rulerBits) source destination 0 sourceHead destinationHead)
      (· = bank (word rulerBits) source destination rulerBits.length (sourceHead-rulerBits.length) destinationHead) rulerBits.length := by
  have forward := RulerAdvance.advance_hoare (a := 2) (fun _ => blank) (fun position => source (-position))
    0 (-sourceHead) (rulerBits.map bitSymbol) (bits_nonblank _) rfl
  simp only [List.length_map,zero_add] at forward
  have reflected := Reflection.hoare forward backMask
  have localRun : HoareTime (Reflection.program RulerAdvance.program backMask)
      (· = (RulerAdvance.cfg (word rulerBits) source 0 sourceHead).tapes)
      (· = (RulerAdvance.cfg (word rulerBits) source rulerBits.length (sourceHead-rulerBits.length)).tapes) rulerBits.length := by
    apply reflected.consequence
    · intro current ready
      refine ⟨_,rfl,?_⟩
      rw [reflected_bank]
      simpa only [word,neg_neg] using ready
    · intro current ⟨original,originalReady,currentReady⟩
      rw [originalReady,reflected_bank] at currentReady
      simpa only [word,neg_neg,neg_add_rev,sub_eq_add_neg,add_comm] using currentReady
    · simp
  have framed := FamilyPlacementAlphabet.extend_hoare localRun (⟨fun _ => destinationHead,fun _ => destination⟩ : Tapes 1 2)
  rw [advance_bank,advance_bank] at framed
  exact framed

/-- Widen a signed source from genuinely blank destination storage. The
source and target-width ruler are retained at origin; every output bit,
including high sign padding, is computed by actual machine transitions. -/
theorem runs (bits : List Bool) (targetWidth : ℕ) (sourceFits : bits.length≤targetWidth) :
    HoareTime program (· = input bits targetWidth) (· = output bits targetWidth) (7*targetWidth+bits.length+17) := by
  let ruler : ℤ → Fin 6 := word (List.replicate targetWidth true)
  let source : ℤ → Fin 6 := word bits
  let zeros : ℤ → Fin 6 := word (List.replicate targetWidth false)
  let extended : ℤ → Fin 6 := word (outputBits bits targetWidth)
  have filled := RulerMapCopy.copy_hoare (fun _ : Fin 6 => bitSymbol false) (fun _ => blank) source (fun _ => blank)
    0 0 0 ((List.replicate targetWidth true).map bitSymbol) (bits_nonblank _) rfl
  have copiedZeros : (CopyCells.cells source 0 targetWidth).map (fun _ : Fin 6 => bitSymbol (a := 2) false) =
      (List.replicate targetWidth false).map (bitSymbol (a := 2)) := by
    simp only [List.map_const',CopyCells.cells_length,List.map_replicate]
  simp only [copiedZeros,List.length_map,List.length_replicate,zero_add] at filled
  have firstReset := reset_at (0 : Fin 3) ruler source zeros targetWidth targetWidth targetWidth
    (List.replicate targetWidth true) (by simp [bank,RulerCopy.cfg,Config.tapes]) rfl
  have rewound := backward (List.replicate targetWidth true) source zeros targetWidth targetWidth
  simp only [List.length_replicate,sub_self] at rewound
  have secondReset := reset_at (0 : Fin 3) ruler source zeros targetWidth 0 targetWidth
    (List.replicate targetWidth true) (by simp [bank,RulerCopy.cfg,Config.tapes]) rfl
  have zeroReset := reset_at (2 : Fin 3) ruler source zeros 0 0 targetWidth
    (List.replicate targetWidth false) (by simp [bank,RulerCopy.cfg,Config.tapes]) rfl
  have added := hoare_place (SignExtendAdd.add_hoare (a := 2) bits (List.replicate targetWidth false)
    (fun _ => blank) (fun _ => blank) 0 0 (by simpa using sourceFits) rfl rfl) addSlots
    (⟨fun _ => 0,fun _ => ruler⟩ : Tapes 1 2)
  have addBefore : ((SignExtendAdd.cfg source zeros 0 0 0).tapes.append
      (⟨fun _ => 0,fun _ => ruler⟩ : Tapes 1 2)).reindex addSlots=bank ruler source zeros 0 0 0 := by
    unfold bank RulerCopy.cfg SignExtendAdd.cfg Config.tapes Tapes.append Tapes.reindex addSlots
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have addAfter : ((SignExtendAdd.cfg source extended bits.length targetWidth 0).tapes.append
      (⟨fun _ => 0,fun _ => ruler⟩ : Tapes 1 2)).reindex addSlots=bank ruler source extended 0 bits.length targetWidth := by
    unfold bank RulerCopy.cfg SignExtendAdd.cfg Config.tapes Tapes.append Tapes.reindex addSlots
    congr 1 <;> apply List.ofFn_injective <;> rfl
  simp only [List.length_replicate,zero_add] at added
  change HoareTime (Placement.placed (SignExtendAdd.program 2) addSlots)
    (· = ((SignExtendAdd.cfg source zeros 0 0 0).tapes.append
      (⟨fun _ => 0,fun _ => ruler⟩ : Tapes 1 2)).reindex addSlots)
    (· = ((SignExtendAdd.cfg source extended bits.length targetWidth 0).tapes.append
      (⟨fun _ => 0,fun _ => ruler⟩ : Tapes 1 2)).reindex addSlots) targetWidth at added
  rw [addBefore,addAfter] at added
  have sourceReset := reset_at (1 : Fin 3) ruler source extended 0 bits.length targetWidth bits rfl rfl
  have extendedLength : (outputBits bits targetWidth).length=targetWidth := by
    simpa only [outputBits,List.length_replicate] using TwosComplement.addMod_length bits (List.replicate targetWidth false) (by simpa using sourceFits)
  have outputReset := reset_at (2 : Fin 3) ruler source extended 0 0 targetWidth (outputBits bits targetWidth)
    (by simpa [bank,RulerCopy.cfg,Config.tapes] using extendedLength.symm) rfl
  simp only [set_bank] at firstReset secondReset zeroReset sourceReset outputReset
  simp only [List.length_replicate,extendedLength] at firstReset secondReset zeroReset sourceReset outputReset
  unfold program preparedProgram fill resetRuler resetSource resetDestination input output
  apply (((((((filled.seq firstReset).seq rewound).seq secondReset).seq zeroReset).seq added).seq sourceReset).seq outputReset).consequence
    (fun _ ready => ready) (fun _ finished => finished)
  omega

theorem output_length (bits : List Bool) (targetWidth : ℕ) (sourceFits : bits.length≤targetWidth) :
    (outputBits bits targetWidth).length=targetWidth := by
  simpa only [outputBits,List.length_replicate] using TwosComplement.addMod_length bits (List.replicate targetWidth false) (by simpa using sourceFits)

/-- Widening preserves the original centered integer, including its minimum
value; no caller-supplied sign or prepared high padding is assumed. -/
theorem output_signed (bits : List Bool) (targetWidth : ℕ) (sourceFits : bits.length≤targetWidth)
    (nonempty : bits≠[]) : TwosComplement.signed (outputBits bits targetWidth)=TwosComplement.signed bits := by
  have widthPositive : 0<targetWidth := (List.length_pos_of_ne_nil nonempty).trans_le sourceFits
  have zeroSigned := GaussianLine.signed_zero_word targetWidth
  have originalBounds := TwosComplement.signed_bounds bits nonempty
  have thresholdLe : (2 : ℤ)^(bits.length-1)≤2^(targetWidth-1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have executionValue := TwosComplement.signed_addMod bits (List.replicate targetWidth false)
    (by simpa using sourceFits) (by simp; omega)
    (by simp only [List.length_replicate,zeroSigned,add_zero]; omega)
    (by simp only [List.length_replicate,zeroSigned,add_zero]; omega)
  simpa only [outputBits,zeroSigned,add_zero] using executionValue

/-- Actual preparation for wider arithmetic ports, exact signed value and
all three original heads at origin on the same final bank. -/
theorem runs_signed (bits : List Bool) (targetWidth : ℕ) (sourceFits : bits.length≤targetWidth) (nonempty : bits≠[]) :
    HoareTime program (· = input bits targetWidth) (· = output bits targetWidth) (7*targetWidth+bits.length+17) ∧
      (outputBits bits targetWidth).length=targetWidth ∧
      TwosComplement.signed (outputBits bits targetWidth)=TwosComplement.signed bits ∧
      (∀ slot : Fin 3,(output bits targetWidth).head slot=0) := by
  exact ⟨runs bits targetWidth sourceFits,output_length bits targetWidth sourceFits,
    output_signed bits targetWidth sourceFits nonempty,by intro slot; fin_cases slot <;> rfl⟩

end
end IntegerMultBounds.Machine.ChirpSignExtend
