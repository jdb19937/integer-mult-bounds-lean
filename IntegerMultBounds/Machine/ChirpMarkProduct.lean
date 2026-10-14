module

public import IntegerMultBounds.Machine.ChirpScalarProducts
public import IntegerMultBounds.Machine.MarkedRadixRefresh

/-! Copy one actual unmarked native product into the marked control format
used by the exact numerator-sum machine. The marker and digits are physical
writes into blank storage; the original source returns to zero and the marked
control head returns to one. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpMarkProduct
noncomputable section
open RecoverWorkspace (atProgram)
open SharedPlacementAlphabet (setTape)

abbrev alphabet := 2

def raw (digits : List (Fin 2)) := RulerWordMap.word (digits.map RadixDigits.digitSymbol)
def bank (source destination : ℤ → Fin 6) (sourceHead destinationHead : ℤ) :=
  Copy.tapes source destination sourceHead destinationHead

def mark := atProgram (MarkedWordCleanup.markProgram (a := 2)) (1 : Fin 2)
def resetSource := atProgram (ReturnOrigin.program (a := 2)) (0 : Fin 2)
def rewindDestination := atProgram (Rewind.program (separator : Fin 6)) (1 : Fin 2)
def advanceDestination := atProgram (MultiplicationInputSplit.shift (a := 2) .right) (1 : Fin 2)
def program := seq (seq (seq (seq mark (Copy.program (blank : Fin 6) false)) resetSource) rewindDestination) advanceDestination

def input (digits : List (Fin 2)) := bank (raw digits) (fun _ => blank) 0 0
def output (digits : List (Fin 2)) := bank (raw digits) (MarkedRadixRefresh.source digits) 0 1

private theorem nonblank (digits : List (Fin 2)) : ∀ symbol ∈ digits.map RadixDigits.digitSymbol,symbol≠(blank : Fin 6) := by
  intro symbol member
  obtain ⟨digit,_,rfl⟩ := List.mem_map.mp member
  fin_cases digit <;> decide

private theorem set_bank (source destination updated : ℤ → Fin 6) (sourceHead destinationHead updatedHead : ℤ) (slot : Fin 2) :
    setTape (bank source destination sourceHead destinationHead) slot updated updatedHead=
      bank (if slot=0 then updated else source) (if slot=1 then updated else destination)
        (if slot=0 then updatedHead else sourceHead) (if slot=1 then updatedHead else destinationHead) := by
  fin_cases slot <;> unfold bank setTape Copy.tapes Copy.cfg Config.tapes
  all_goals congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem marker (digits : List (Fin 2)) : MarkedRadixRefresh.source digits 0=separator := by
  rw [MarkedRadixRefresh.source,MarkedWordCleanup.marked,putWord_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem no_marker (digits : List (Fin 2)) (position : ℤ) (positive : 0<position) :
    MarkedRadixRefresh.source digits position≠separator := by
  by_cases inWord : position<1+digits.length
  · have member := ReturnOrigin.putWord_mem (MarkedWordCleanup.empty (a := 2)) 1
      (digits.map RadixDigits.digitSymbol) position ⟨by omega,by simpa using inWord⟩
    obtain ⟨digit,_,equal⟩ := List.mem_map.mp member
    change putWord MarkedWordCleanup.empty 1 (digits.map RadixDigits.digitSymbol) position≠separator
    rw [←equal]
    fin_cases digit <;> decide
  · rw [MarkedRadixRefresh.source,MarkedWordCleanup.marked,putWord_outside _ _ _ _ (Or.inr (by simpa using le_of_not_gt inWord))]
    simp [MarkedWordCleanup.empty,show position≠0 by omega,separator,blank,Fin.ext_iff]

/-- Genuine marker construction and field copy, including empty words.
No already-marked source/control word is supplied in the input. -/
theorem runs (digits : List (Fin 2)) :
    HoareTime program (· = input digits) (· = output digits) (3*digits.length+9) := by
  let symbols := digits.map RadixDigits.digitSymbol
  let source := raw digits
  let destination := MarkedRadixRefresh.source digits
  have marked := RecoverWorkspace.runs_one_at (MarkedWordCleanup.markProgram (a := 2)) (1 : Fin 2)
    (bank source (fun _ => blank) 0 0) (fun _ => blank) (MarkedWordCleanup.empty (a := 2)) 0 1 rfl rfl
    (by simpa [MarkedWordCleanup.word,MarkedWordCleanup.marked,putWord,MarkedWordCleanup.one,FiniteReturnStack.bank]
      using MarkedWordCleanup.mark_hoare (a := 2) [])
  have copied := Copy.copy_hoare (blank : Fin 6) false (fun _ => blank) MarkedWordCleanup.empty 0 1 symbols
    (nonblank digits) (by rfl)
  have retained : Copy.retained false=(id : Fin 6 → Fin 6) := by funext symbol; rfl
  simp only [retained,List.map_id,zero_add] at copied
  have returned := RecoverWorkspace.return_at (0 : Fin 2) (bank source destination digits.length (1+digits.length))
    symbols (nonblank digits) (by simp [bank,Copy.tapes,Copy.cfg,Config.tapes,symbols]) rfl
  have rewound := Rewind.rewind_hoare (separator : Fin 6) destination (digits.length+1) (digits.length+1)
    (by intro index bound; apply no_marker digits; omega) (by simpa using marker digits)
  have rewoundLocal : HoareTime (Rewind.program (separator : Fin 6))
      (· = FiniteReturnStack.bank destination (1+digits.length)) (· = FiniteReturnStack.bank destination 0) (digits.length+1) := by
    simpa [Rewind.cfg,Config.tapes,FiniteReturnStack.bank,add_comm] using rewound
  have destinationReset := RecoverWorkspace.runs_one_at (Rewind.program (separator : Fin 6)) (1 : Fin 2)
    (bank source destination 0 (1+digits.length)) destination destination (1+digits.length) 0 rfl rfl rewoundLocal
  have advanced := RecoverWorkspace.shift_at (1 : Fin 2) (bank source destination 0 0) .right
  simp only [RecoverWorkspace.restored,set_bank,Move.offset] at marked returned destinationReset advanced
  simp [bank,Copy.tapes,Copy.cfg,Config.tapes] at marked returned destinationReset advanced
  simp only [symbols,List.length_map] at copied returned
  unfold program input output mark resetSource rewindDestination advanceDestination
  simp only [bank,Copy.tapes,Copy.cfg,Config.tapes,ite_self]
  apply (((marked.seq copied).seq returned).seq destinationReset).seq advanced |>.consequence
    (fun _ ready => ready) (fun _ finished => finished) ?_
  omega

theorem output_eq_input_update (digits : List (Fin 2)) :
    output digits=setTape (input digits) (1 : Fin 2) (MarkedRadixRefresh.source digits) 1 := by
  apply Placement.Tapes.ext'
  · intro slot; fin_cases slot <;> rfl
  · intro slot; fin_cases slot <;> rfl

end
end IntegerMultBounds.Machine.ChirpMarkProduct
