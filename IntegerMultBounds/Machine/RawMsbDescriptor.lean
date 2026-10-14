module

public import IntegerMultBounds.Machine.GammaRead

/-! Convert a raw MSB binary word into the marked LSB descriptor used by
runtime parameter controls. The machine discovers the word's end, physically
copies it backwards while erasing the source, and returns the descriptor head
to its first bit. No word length or prepared length ruler is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RawMsbDescriptor
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open RecoverWorkspace (atProgram)
open SharedPlacementAlphabet (setTape)

def program : Program 2 13 alphabet :=
  seq (seq (seq (seq (seq (seq (seq (atProgram ScanEnd.program (0 : Fin 2))
    (atProgram (MultiplicationInputSplit.shift .left) (0 : Fin 2)))
    (atProgram (WriteSymbol.program separator) (1 : Fin 2)))
    (atProgram (MultiplicationInputSplit.shift .right) (1 : Fin 2)))
    (DelimitedReverseCopy.program blank true))
    (atProgram (MultiplicationInputSplit.shift .right) (0 : Fin 2)))
    (atProgram (Rewind.program separator) (1 : Fin 2)))
    (atProgram (MultiplicationInputSplit.shift .right) (1 : Fin 2))

private theorem set_source (source destination updated : ℤ → Fin (alphabet+4))
    (sourceHead destinationHead updatedHead : ℤ) :
    setTape (Copy.tapes source destination sourceHead destinationHead) (0 : Fin 2) updated updatedHead =
      Copy.tapes updated destination updatedHead destinationHead := by
  unfold setTape Copy.tapes Copy.cfg Config.tapes
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem set_destination (source destination updated : ℤ → Fin (alphabet+4))
    (sourceHead destinationHead updatedHead : ℤ) :
    setTape (Copy.tapes source destination sourceHead destinationHead) (1 : Fin 2) updated updatedHead =
      Copy.tapes source updated sourceHead updatedHead := by
  unfold setTape Copy.tapes Copy.cfg Config.tapes
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem source_run {states cost : ℕ} (machine : Program 1 states alphabet)
    (source destination updated : ℤ → Fin (alphabet+4)) (sourceHead destinationHead updatedHead : ℤ)
    (localRun : HoareTime machine (· = FiniteReturnStack.bank source sourceHead)
      (· = FiniteReturnStack.bank updated updatedHead) cost) :
    HoareTime (atProgram machine (0 : Fin 2)) (· = Copy.tapes source destination sourceHead destinationHead)
      (· = Copy.tapes updated destination updatedHead destinationHead) cost := by
  have placed := RecoverWorkspace.runs_one_at machine (0 : Fin 2)
    (Copy.tapes source destination sourceHead destinationHead) source updated sourceHead updatedHead rfl rfl localRun
  rw [set_source] at placed
  exact placed

private theorem destination_run {states cost : ℕ} (machine : Program 1 states alphabet)
    (source destination updated : ℤ → Fin (alphabet+4)) (sourceHead destinationHead updatedHead : ℤ)
    (localRun : HoareTime machine (· = FiniteReturnStack.bank destination destinationHead)
      (· = FiniteReturnStack.bank updated updatedHead) cost) :
    HoareTime (atProgram machine (1 : Fin 2)) (· = Copy.tapes source destination sourceHead destinationHead)
      (· = Copy.tapes source updated sourceHead updatedHead) cost := by
  have placed := RecoverWorkspace.runs_one_at machine (1 : Fin 2)
    (Copy.tapes source destination sourceHead destinationHead) destination updated destinationHead updatedHead rfl rfl localRun
  rw [set_destination] at placed
  exact placed

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem descriptor_return (bits : List Bool) :
    HoareTime (Rewind.program (separator : Fin (alphabet+4)))
      (· = FiniteReturnStack.bank (BinaryDescriptorStack.descriptor bits) (1+bits.length))
      (· = FiniteReturnStack.bank (BinaryDescriptorStack.descriptor bits) 0) (bits.length+1) := by
  have noMarker : ∀ position : ℤ, 0 < position → BinaryDescriptorStack.descriptor (a := alphabet) bits position ≠ separator := by
    intro position positive
    by_cases inside : position < 1+bits.length
    · have member := ReturnOrigin.putWord_mem BinaryDescriptorStack.empty 1
        (bits.map (bitSymbol (a := alphabet))) position ⟨by omega,by simpa using inside⟩
      obtain ⟨bit,_,equal⟩ := List.mem_map.mp member
      change putWord BinaryDescriptorStack.empty 1 (bits.map bitSymbol) position ≠ separator
      rw [← equal]
      cases bit <;> simp [bitSymbol,separator,Fin.ext_iff]
    · rw [BinaryDescriptorStack.descriptor,putWord_outside _ _ _ _ (Or.inr (by simpa using le_of_not_gt inside))]
      simp [BinaryDescriptorStack.empty,show position ≠ 0 by omega,blank,separator,Fin.ext_iff]
  have returned := Rewind.rewind_hoare (separator : Fin (alphabet+4)) (BinaryDescriptorStack.descriptor bits)
    (1+bits.length) (bits.length+1) (by intro index bound; apply noMarker; omega) (by
      simp only [Nat.cast_add,Nat.cast_one,add_comm,sub_self]
      rw [BinaryDescriptorStack.descriptor,putWord_outside _ _ _ _ (Or.inl (by omega))]
      rfl)
  simpa only [Rewind.cfg,Config.tapes,FiniteReturnStack.bank,Nat.cast_add,Nat.cast_one,add_comm,sub_self] using returned

/-- Exact bit reversal, source erasure, sentinel creation and descriptor-head
positioning. Empty words are supported; all output exterior remains blank. -/
theorem runs_convert (bits : List Bool) :
    HoareTime (program (alphabet := alphabet))
      (· = Copy.tapes (word bits) (fun _ => blank) 0 0)
      (· = Copy.tapes (fun _ => blank) (BinaryDescriptorStack.descriptor bits.reverse) 0 1)
      (3 * bits.length + 13) := by
  have scanned := source_run (alphabet := alphabet) ScanEnd.program (word bits) (fun _ => blank) (word bits) 0 0 bits.length
    (by simpa only [ScanEnd.cfg,Config.tapes,FiniteReturnStack.bank,word,List.length_map,zero_add] using
      ScanEnd.scan_hoare (fun _ => (blank : Fin (alphabet+4))) 0 (bits.map bitSymbol) (bits_nonblank _) rfl)
  have shiftedLeft := source_run (alphabet := alphabet) (MultiplicationInputSplit.shift .left) (word bits) (fun _ => blank)
    (word bits) bits.length 0 (bits.length-1)
    (by simpa only [FiniteReturnStack.bank,Move.offset,Int.add_neg_one] using MultiplicationInputSplit.shifts .left (word bits) bits.length)
  have marked := destination_run (alphabet := alphabet) (WriteSymbol.program separator) (word bits) (fun _ => blank)
    (Function.update (fun _ => blank) 0 separator) (bits.length-1) 0 0
    (by simpa only [WriteSymbol.cfg,Config.tapes,FiniteReturnStack.bank] using
      WriteSymbol.write_hoare (separator : Fin (alphabet+4)) (fun _ => blank) 0)
  have markerTape : Function.update (fun _ => (blank : Fin (alphabet+4))) 0 separator = BinaryDescriptorStack.empty := by
    funext position; simp [Function.update_apply,BinaryDescriptorStack.empty]
  rw [markerTape] at marked
  have shiftedDestination := destination_run (alphabet := alphabet) (MultiplicationInputSplit.shift .right) (word bits) BinaryDescriptorStack.empty
    BinaryDescriptorStack.empty (bits.length-1) 0 1
    (by simpa only [FiniteReturnStack.bank,Move.offset,zero_add] using MultiplicationInputSplit.shifts .right BinaryDescriptorStack.empty (0 : ℤ))
  have reversed := DelimitedReverseCopy.reverse_hoare (blank : Fin (alphabet+4)) true (fun _ => blank)
    BinaryDescriptorStack.empty 0 1 (bits.map bitSymbol) (bits_nonblank _) rfl
  have erasedSource : putWord (fun _ => (blank : Fin (alphabet+4))) 0
      ((bits.map bitSymbol).map (Copy.retained true)) = (fun _ => blank) := by
    have retained : (bits.map (bitSymbol (a := alphabet))).map (Copy.retained true) = List.replicate bits.length blank := by
      simp [Copy.retained,List.map_map,Function.comp_def]
    rw [retained]
    exact putWord_replicate_blank _ _ _ (by intros; rfl)
  simp only [List.length_map,zero_add,zero_sub,← List.map_reverse] at reversed
  rw [erasedSource] at reversed
  have shiftedSource := source_run (alphabet := alphabet) (MultiplicationInputSplit.shift .right) (fun _ => blank)
    (BinaryDescriptorStack.descriptor bits.reverse) (fun _ => blank) (-1) (1+bits.length) 0
    (by simpa only [FiniteReturnStack.bank,Move.offset,neg_add_cancel] using (MultiplicationInputSplit.shifts .right (fun _ => (blank : Fin (alphabet+4))) (-1 : ℤ)))
  have returned := destination_run (alphabet := alphabet) (Rewind.program separator) (fun _ => blank) (BinaryDescriptorStack.descriptor bits.reverse)
    (BinaryDescriptorStack.descriptor bits.reverse) 0 (1+bits.length) 0
    (by simpa only [List.length_reverse] using descriptor_return (alphabet := alphabet) bits.reverse)
  have finalShift := destination_run (alphabet := alphabet) (MultiplicationInputSplit.shift .right) (fun _ => blank)
    (BinaryDescriptorStack.descriptor bits.reverse) (BinaryDescriptorStack.descriptor bits.reverse) 0 0 1
    (by simpa only [FiniteReturnStack.bank,Move.offset,zero_add] using (MultiplicationInputSplit.shifts .right
      (BinaryDescriptorStack.descriptor (a := alphabet) bits.reverse) (0 : ℤ)))
  unfold program
  apply (((((((scanned.seq shiftedLeft).seq marked).seq shiftedDestination).seq reversed).seq shiftedSource).seq returned).seq finalShift).consequence
    (fun _ ready => ready) (fun _ finished => finished)
  omega

/-- Conversion preserves the numerical value across the representation change. -/
theorem converted_value (bits : List Bool) : Counter.value bits.reverse = binaryValue bits :=
  ElementaryMultiplyCore.value_reverse bits

end
end IntegerMultBounds.Machine.RawMsbDescriptor
