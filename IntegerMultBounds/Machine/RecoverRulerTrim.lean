module

public import IntegerMultBounds.Machine.RecoverChunkParameter

/-! Runtime-counted removal of a unary ruler's suffix. The independent binary
count is copied into a real countdown; one cell is erased per successful
iteration, then the shortened ruler is returned to origin and every private
control is cleared. This implements residual-precision subtraction on tapes. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverRulerTrim
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)

def eraseCell : Program 1 2 alphabet := DescriptorStackControl.once (by decide) (fun _ _ => (blank,Move.left))

private theorem erase_cell (source : ℤ → Fin (alphabet+4)) (position : ℤ) :
    HoareTime eraseCell (· = FiniteReturnStack.bank source position)
      (· = FiniteReturnStack.bank (Function.update source position blank) (position-1)) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (FiniteReturnStack.bank source position)).consequence
    (fun _ ready => ready) _ le_rfl
  rintro finalBank rfl
  unfold DescriptorStackControl.after FiniteReturnStack.bank
  congr 1
  funext slot cell
  simp [Function.update_apply]

/-- Erasing the final true cell shortens the entire raw ruler by one, with no
changed exterior cell and no leftover blank padding as an encoded payload. -/
theorem erase_last (remaining : ℕ) :
    Function.update (word (alphabet := alphabet) (List.replicate (remaining+1) true)) remaining blank =
      word (List.replicate remaining true) := by
  have appended : Function.update (word (alphabet := alphabet) (List.replicate remaining true)) remaining (bitSymbol true) =
      word (List.replicate (remaining+1) true) := by
    simpa only [word,List.map_replicate,List.length_replicate,zero_add,List.replicate_add,List.replicate_one,List.map_append,List.map_cons,List.map_nil] using
      Gather.putWord_snoc (fun _ => (blank : Fin (alphabet+4))) 0 (List.replicate remaining (bitSymbol true)) (bitSymbol true)
  rw [← appended,Function.update_idem]
  apply Function.update_eq_self_iff.mpr
  rw [word,putWord_outside _ _ _ _ (Or.inr (by simp))]

def rawProgram : Program 3 24 alphabet := seq (seq CountedGuardConstantsFill.mark
  (CountedLoopReuseAlphabet.program eraseCell)) (BinaryDescriptorCleanupList.oneProgram (1 : Fin 3))

private theorem runs_raw (width : ℕ) (eraseBits : List Bool) (eraseCount : ℕ)
    (countValue : Counter.value eraseBits = eraseCount) (erasuresFit : eraseCount ≤ width) :
    HoareTime (rawProgram (alphabet := alphabet))
      (· = CountedGuardConstantsFill.input (word (List.replicate width true)) ((width : ℤ)-1) eraseBits)
      (· = CountedGuardConstantsFill.input (word (List.replicate (width-eraseCount) true))
        ((width-eraseCount : ℕ)-1 : ℤ) eraseBits) (7 * eraseCount + 7 * eraseBits.length + 23) := by
  let stage := fun index : ℕ => FiniteReturnStack.bank (word (alphabet := alphabet) (List.replicate (width-index) true))
    (((width-index : ℕ) : ℤ)-1)
  have bodyRun : ∀ index < eraseCount, HoareTime (eraseCell (alphabet := alphabet)) (· = stage index) (· = stage (index+1)) 1 := by
    intro index bound
    have remainingPositive : 0 < width-index := by omega
    have widthStep : width-index = (width-(index+1))+1 := by omega
    have erased := erase_cell (alphabet := alphabet) (word (List.replicate (width-index) true)) (((width-index : ℕ) : ℤ)-1)
    rw [widthStep] at erased
    have lastPosition : (((width-(index+1))+1 : ℕ) : ℤ)-1 = ((width-(index+1) : ℕ) : ℤ) := by omega
    rw [lastPosition,erase_last] at erased
    simpa only [stage,widthStep,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using erased
  have marked := CountedGuardConstantsFill.marks (a := alphabet) (word (List.replicate width true)) ((width : ℤ)-1) eraseBits
  have loop := CountedLoopReuseAlphabet.loop_hoare (eraseCell (alphabet := alphabet)) eraseBits eraseCount stage (fun _ => 1) countValue bodyRun
  have initialBank : CountedGuardConstantsFill.marked (a := alphabet) (word (List.replicate width true)) ((width : ℤ)-1) eraseBits =
      CountedLoopReuseAlphabet.bank (stage 0) CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary eraseBits) 1 1 := by
    simp [stage,CountedGuardConstantsFill.marked,CountedGuardConstantsFill.one,FiniteReturnStack.bank]
  rw [initialBank] at marked
  have cleared := BinaryDescriptorCleanupList.one_hoare (1 : Fin 3)
    (CountedLoopReuseAlphabet.bank (stage eraseCount) CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary eraseBits) 1 1) [] rfl rfl
  have endpoint : setTape
      (CountedLoopReuseAlphabet.bank (stage eraseCount) CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary eraseBits) 1 1)
      (1 : Fin 3) (fun _ => blank) 0 = CountedGuardConstantsFill.input
        (word (List.replicate (width-eraseCount) true)) (((width-eraseCount : ℕ) : ℤ)-1) eraseBits := by
    unfold stage setTape CountedLoopReuseAlphabet.bank CountedLoopReuseAlphabet.controls Tapes.append
      CountedGuardConstantsFill.input CountedGuardGadgetPosition.input FiniteReturnStack.bank
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [endpoint] at cleared
  unfold rawProgram
  apply ((marked.seq loop).seq cleared).consequence (fun _ ready => ready) (fun _ finished => finished)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,List.length_nil]
  omega

def program : Program 3 35 alphabet := seq (seq (seq (seq
  (RecoverWorkspace.atProgram (MultiplicationInputSplit.shift .left) (0 : Fin 3)) rawProgram)
  (RecoverWorkspace.atProgram (MultiplicationInputSplit.shift .right) (0 : Fin 3)))
  (RecoverWorkspace.atProgram ReturnOrigin.program (0 : Fin 3)))
  (BinaryDescriptorCleanupList.oneProgram (2 : Fin 3))

def input (width : ℕ) (eraseBits : List Bool) : Tapes 3 alphabet :=
  CountedGuardConstantsFill.input (word (List.replicate width true)) width eraseBits

def output (remaining : ℕ) : Tapes 3 alphabet := RecoverBinaryRuler.output remaining

/-- Both arithmetic boundary cases are executed: removing no cells leaves the
ruler unchanged, and removing all cells returns a truly blank ruler at origin.
The actual binary count controls each erasure; its descriptor is consumed. -/
theorem runs_trim (width : ℕ) (eraseBits : List Bool) (eraseCount : ℕ)
    (countValue : Counter.value eraseBits = eraseCount) (erasuresFit : eraseCount ≤ width) :
    HoareTime (program (alphabet := alphabet)) (· = input width eraseBits) (· = output (width-eraseCount))
      (8 * width + 9 * eraseBits.length + 35) := by
  let initial := input (alphabet := alphabet) width eraseBits
  have left := RecoverWorkspace.shift_at (0 : Fin 3) initial .left
  have leftEndpoint : setTape initial (0 : Fin 3) (initial.tape 0) (initial.head 0+Move.left.offset) =
      CountedGuardConstantsFill.input (word (List.replicate width true)) ((width : ℤ)-1) eraseBits := by
    unfold initial input setTape CountedGuardConstantsFill.input CountedGuardGadgetPosition.input
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [leftEndpoint] at left
  have trimmed := runs_raw (alphabet := alphabet) width eraseBits eraseCount countValue erasuresFit
  let shortened := CountedGuardConstantsFill.input (word (alphabet := alphabet) (List.replicate (width-eraseCount) true))
    (((width-eraseCount : ℕ) : ℤ)-1) eraseBits
  have right := RecoverWorkspace.shift_at (0 : Fin 3) shortened .right
  have rightEndpoint : setTape shortened (0 : Fin 3) (shortened.tape 0) (shortened.head 0+Move.right.offset) =
      input (alphabet := alphabet) (width-eraseCount) eraseBits := by
    unfold shortened input setTape CountedGuardConstantsFill.input CountedGuardGadgetPosition.input
    congr 1
    · apply List.ofFn_injective; simp [Move.offset]
    · apply List.ofFn_injective; rfl
  rw [rightEndpoint] at right
  have returned := RecoverWorkspace.return_at (0 : Fin 3) (input (alphabet := alphabet) (width-eraseCount) eraseBits)
    ((List.replicate (width-eraseCount) true).map bitSymbol) (by
      intro symbol member
      obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
      cases bit <;> simp [bitSymbol,blank,Fin.ext_iff])
    (by change ((width-eraseCount : ℕ) : ℤ) = _; simp) rfl
  let returnedBank := RecoverWorkspace.restored (input (alphabet := alphabet) (width-eraseCount) eraseBits) (0 : Fin 3)
  have descriptorReady : returnedBank.tape (2 : Fin 3) = BinaryDescriptorStack.descriptor eraseBits := by
    simp [returnedBank,RecoverWorkspace.restored,input,CountedGuardConstantsFill.input,CountedGuardGadgetPosition.input,setTape]
    rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
    exact CountedLoopReuseAlphabet.encoding_binary eraseBits |>.symm
  have cleared := BinaryDescriptorCleanupList.one_hoare (2 : Fin 3) returnedBank eraseBits descriptorReady
    (by simp [returnedBank,RecoverWorkspace.restored,input,CountedGuardConstantsFill.input,CountedGuardGadgetPosition.input,setTape])
  have endpoint : setTape returnedBank (2 : Fin 3) (fun _ => blank) 0 = output (alphabet := alphabet) (width-eraseCount) := by
    unfold returnedBank RecoverWorkspace.restored input CountedGuardConstantsFill.input CountedGuardGadgetPosition.input
      setTape output RecoverBinaryRuler.output
    congr 1 <;> apply List.ofFn_injective <;> rfl
  unfold program
  apply ((((left.seq trimmed).seq right).seq returned).seq cleared).consequence (fun _ ready => ready)
    (fun _ finished => finished.trans endpoint)
  simp only [List.length_map,List.length_replicate]
  omega

end
end IntegerMultBounds.Machine.RecoverRulerTrim
