module

public import IntegerMultBounds.Machine.RecoverCoefficientStep
public import IntegerMultBounds.Machine.DescriptorStackControl

/-! Physical splitting of a coefficient magnitude at a supplied precision
ruler. A fixed machine creates both descriptor sentinels, copies the fractional
prefix and integer suffix, returns the integer head to its first bit, and places
the fractional head on the actual half-unit guard. No split fields are supplied
as prepared input tapes. Ruler synthesis and stream iteration remain separate. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverPrecisionSplit
variable {alphabet : ℕ}
open RecoverCarryStep (word)

def bank (ruler source fraction integer : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead fractionHead integerHead : ℤ) : Tapes 4 alphabet :=
  ⟨![rulerHead,sourceHead,fractionHead,integerHead],![ruler,source,fraction,integer]⟩

def fractionBits (lowerBits : List Bool) (guard : Bool) := lowerBits ++ [guard]
def sourceBits (lowerBits : List Bool) (guard : Bool) (integerBits : List Bool) :=
  fractionBits lowerBits guard ++ integerBits

def input (lowerBits : List Bool) (guard : Bool) (integerBits : List Bool) : Tapes 4 alphabet :=
  bank (word (List.replicate (fractionBits lowerBits guard).length true))
    (word (sourceBits lowerBits guard integerBits)) (fun _ => blank) (fun _ => blank) 0 0 0 0

def output (lowerBits : List Bool) (guard : Bool) (integerBits : List Bool) : Tapes 4 alphabet :=
  bank (word (List.replicate (fractionBits lowerBits guard).length true))
    (word (sourceBits lowerBits guard integerBits))
    (BinaryDescriptorStack.descriptor (fractionBits lowerBits guard))
    (BinaryDescriptorStack.descriptor integerBits)
    (fractionBits lowerBits guard).length (sourceBits lowerBits guard integerBits).length
    (fractionBits lowerBits guard).length 1

def setup : Program 4 2 alphabet := DescriptorStackControl.once (by decide)
  (fun symbols slot => if slot = 2 ∨ slot = 3 then (separator,Move.right) else (symbols slot,Move.stay))

def highSlots : Fin (2+2) ≃ Fin 4 where
  toFun := ![1,3,0,2]
  invFun := ![2,0,3,1]
  left_inv := by decide
  right_inv := by decide

def integerSlots : Fin (1+3) ≃ Fin 4 where
  toFun := ![3,0,1,2]
  invFun := ![1,2,3,0]
  left_inv := by decide
  right_inv := by decide

def fractionSlots : Fin (1+3) ≃ Fin 4 where
  toFun := ![2,0,1,3]
  invFun := ![1,2,0,3]
  left_inv := by decide
  right_inv := by decide

def returnDescriptor : Program 1 5 alphabet :=
  seq ReturnOrigin.program (MultiplicationInputSplit.shift .right)

def program : Program 4 11 alphabet :=
  seq (seq (seq (seq setup (extend RulerCopy.program 1))
    (reindex (extend (Copy.program blank false) 2) highSlots))
    (reindex (extend returnDescriptor 3) integerSlots))
    (reindex (extend (MultiplicationInputSplit.shift .left) 3) fractionSlots)

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

theorem descriptor_word (bits : List Bool) :
    BinaryDescriptorStack.descriptor (a := alphabet) bits =
      putWord (fun _ => blank) 0 (separator :: bits.map bitSymbol) := by
  unfold BinaryDescriptorStack.descriptor
  rw [putWord_cons]
  congr 1
  funext cell
  simp [BinaryDescriptorStack.empty,Function.update_apply]

/-- A reusable literal return contract for a marked descriptor at its end. -/
theorem returns_descriptor (bits : List Bool) :
    HoareTime (returnDescriptor (alphabet := alphabet))
      (· = (⟨fun _ => 1 + bits.length,fun _ => BinaryDescriptorStack.descriptor bits⟩ : Tapes 1 alphabet))
      (· = BinaryDescriptorIncrement.bank bits) (bits.length + 5) := by
  have symbolsNonblank : ∀ symbol ∈ separator :: bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
    intro symbol member
    rcases List.mem_cons.mp member with rfl | member
    · simp [separator,blank,Fin.ext_iff]
    · exact bits_nonblank bits symbol member
  have returned := ReturnOrigin.return_hoare (separator :: bits.map (bitSymbol (a := alphabet))) symbolsNonblank
  rw [← descriptor_word] at returned
  simp only [List.length_cons,List.length_map] at returned
  have shifted := MultiplicationInputSplit.shifts (a := alphabet) .right (BinaryDescriptorStack.descriptor bits) 0
  simp only [ReturnOrigin.cfg,Config.tapes,Nat.cast_add,Nat.cast_one] at returned
  simp only [Move.offset,zero_add] at shifted
  have relaxed := (returned.seq shifted).consequence (b' := bits.length + 5)
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis) (by omega)
  simpa only [returnDescriptor,BinaryDescriptorIncrement.bank,add_comm] using relaxed

private theorem setups (lowerBits : List Bool) (guard : Bool) (integerBits : List Bool) :
    HoareTime (setup (alphabet := alphabet)) (· = input lowerBits guard integerBits)
      (· = bank (word (List.replicate (fractionBits lowerBits guard).length true))
        (word (sourceBits lowerBits guard integerBits)) BinaryDescriptorStack.empty BinaryDescriptorStack.empty 0 0 1 1) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (input lowerBits guard integerBits)).consequence
    (fun _ hypothesis => hypothesis) _ le_rfl
  intro current equal
  rw [equal]
  unfold DescriptorStackControl.after input bank
  congr 1
  · apply List.ofFn_injective; rfl
  · funext slot cell
    fin_cases slot <;> simp [BinaryDescriptorStack.empty,eq_comm]
    all_goals by_cases atOrigin : cell = 0 <;> simp [atOrigin]

private theorem low_bank (ruler source fraction integer : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead fractionHead integerHead : ℤ) :
    (RulerCopy.cfg ruler source fraction rulerHead sourceHead fractionHead).tapes.append
      (⟨fun _ => integerHead,fun _ => integer⟩ : Tapes 1 alphabet) =
      bank ruler source fraction integer rulerHead sourceHead fractionHead integerHead := by
  unfold RulerCopy.cfg Config.tapes Tapes.append bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem high_bank (ruler source fraction integer : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead fractionHead integerHead : ℤ) :
    ((Copy.tapes source integer sourceHead integerHead).append
      (⟨![rulerHead,fractionHead],![ruler,fraction]⟩ : Tapes 2 alphabet)).reindex highSlots =
      bank ruler source fraction integer rulerHead sourceHead fractionHead integerHead := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex highSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem integer_bank (ruler source fraction integer : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead fractionHead integerHead : ℤ) :
    ((⟨fun _ => integerHead,fun _ => integer⟩ : Tapes 1 alphabet).append
      (⟨![rulerHead,sourceHead,fractionHead],![ruler,source,fraction]⟩ : Tapes 3 alphabet)).reindex integerSlots =
      bank ruler source fraction integer rulerHead sourceHead fractionHead integerHead := by
  unfold Tapes.append Tapes.reindex integerSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem fraction_bank (ruler source fraction integer : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead fractionHead integerHead : ℤ) :
    ((⟨fun _ => fractionHead,fun _ => fraction⟩ : Tapes 1 alphabet).append
      (⟨![rulerHead,sourceHead,integerHead],![ruler,source,integer]⟩ : Tapes 3 alphabet)).reindex fractionSlots =
      bank ruler source fraction integer rulerHead sourceHead fractionHead integerHead := by
  unfold Tapes.append Tapes.reindex fractionSlots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem runs_split (lowerBits : List Bool) (guard : Bool) (integerBits : List Bool) :
    HoareTime (program (alphabet := alphabet)) (· = input lowerBits guard integerBits)
      (· = output lowerBits guard integerBits)
      ((fractionBits lowerBits guard).length + 2 * integerBits.length + 11) := by
  have lowCopied := FamilyPlacementAlphabet.extend_hoare
    (RulerCopy.copy_hoare (fun _ => (blank : Fin (alphabet+4)))
      (word (sourceBits lowerBits guard integerBits)) BinaryDescriptorStack.empty 0 0 1
      ((List.replicate (fractionBits lowerBits guard).length true).map bitSymbol)
      (bits_nonblank _) (by rfl))
    (⟨fun _ => 1,fun _ => BinaryDescriptorStack.empty⟩ : Tapes 1 alphabet)
  simp only [List.length_map,List.length_replicate,zero_add] at lowCopied
  rw [low_bank,low_bank,RecoverCarryStep.copied_chunk _ _ (by simp [sourceBits])] at lowCopied
  simp only [sourceBits,List.take_left] at lowCopied
  have wholeWord : putWord (word (alphabet := alphabet) (fractionBits lowerBits guard))
      (fractionBits lowerBits guard).length (integerBits.map bitSymbol) =
      word (sourceBits lowerBits guard integerBits) := by
    have joined := putWord_append_forward (fun _ => (blank : Fin (alphabet+4))) 0
      ((fractionBits lowerBits guard).map bitSymbol) (integerBits.map bitSymbol)
    simpa only [word,sourceBits,List.length_map,zero_add,← List.map_append] using joined
  have highCopied := hoare_place
    (Copy.copy_hoare (a := alphabet) blank false (word (fractionBits lowerBits guard)) BinaryDescriptorStack.empty
      (fractionBits lowerBits guard).length 1 (integerBits.map bitSymbol) (bits_nonblank _)
      (by unfold word; rw [putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map]; omega))])) highSlots
    (⟨![(fractionBits lowerBits guard).length,1 + (fractionBits lowerBits guard).length],
      ![word (List.replicate (fractionBits lowerBits guard).length true),
        BinaryDescriptorStack.descriptor (fractionBits lowerBits guard)]⟩ : Tapes 2 alphabet)
  have retained : (Copy.retained false : Fin (alphabet+4) → Fin (alphabet+4)) = id := by funext symbol; rfl
  simp only [retained,List.map_id,List.length_map] at highCopied
  rw [wholeWord,high_bank,high_bank] at highCopied
  have returned := hoare_place (returns_descriptor (alphabet := alphabet) integerBits) integerSlots
    (⟨![(fractionBits lowerBits guard).length,(sourceBits lowerBits guard integerBits).length,
      1 + (fractionBits lowerBits guard).length],
      ![word (List.replicate (fractionBits lowerBits guard).length true),word (sourceBits lowerBits guard integerBits),
        BinaryDescriptorStack.descriptor (fractionBits lowerBits guard)]⟩ : Tapes 3 alphabet)
  simp only [BinaryDescriptorIncrement.bank] at returned
  rw [integer_bank,integer_bank] at returned
  have positioned := hoare_place (MultiplicationInputSplit.shifts (a := alphabet) .left
    (BinaryDescriptorStack.descriptor (fractionBits lowerBits guard)) (1 + (fractionBits lowerBits guard).length)) fractionSlots
    (⟨![(fractionBits lowerBits guard).length,(sourceBits lowerBits guard integerBits).length,1],
      ![word (List.replicate (fractionBits lowerBits guard).length true),word (sourceBits lowerBits guard integerBits),
        BinaryDescriptorStack.descriptor integerBits]⟩ : Tapes 3 alphabet)
  simp only [Move.offset] at positioned
  have guardPosition : (1 : ℤ) + (fractionBits lowerBits guard).length + -1 =
      (fractionBits lowerBits guard).length := by omega
  rw [guardPosition] at positioned
  rw [fraction_bank,fraction_bank] at positioned
  have sourceEnd : ((fractionBits lowerBits guard).length : ℤ) + integerBits.length =
      (sourceBits lowerBits guard integerBits).length := by simp [sourceBits]
  rw [sourceEnd] at highCopied
  apply (((((setups lowerBits guard integerBits).seq lowCopied).seq highCopied).seq returned).seq positioned).consequence
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
  omega

end IntegerMultBounds.Machine.RecoverPrecisionSplit
