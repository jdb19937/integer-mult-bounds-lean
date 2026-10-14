module

public import IntegerMultBounds.Machine.ChirpFastNativeProduct

/-! Construct a signed full-width integer one in genuinely blank storage.
The actual width ruler clocks zero filling; a single physical origin write
sets the low bit. Original source/ruler and every head are retained. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpUnitOperand
noncomputable section
open SharedPlacementAlphabet (setTape)

abbrev alphabet := 2

def bits (width : ℕ) := true :: List.replicate (width-1) false

def writeOne : Program 1 2 2 where
  tapes_pos := by decide
  start := 0
  transition := fun state _ => if state=0 then some (1,fun _ => (bitSymbol true,Move.stay)) else none

def fill := RulerWordMap.program (fun _ : Fin 6 => bitSymbol false)
def write := RecoverWorkspace.atProgram writeOne (2 : Fin 3)
def program := seq fill write

def input (source : List Bool) := RulerWordMap.input (source.map (bitSymbol (a := 2)))
def output (source : List Bool) : Tapes 3 2 :=
  RulerWordMap.bank (RulerWordMap.word (List.replicate source.length (bitSymbol true)))
    (RulerWordMap.word (source.map bitSymbol)) (RulerWordMap.word ((bits source.length).map bitSymbol)) 0 0 0

theorem bits_length (width : ℕ) (positive : 1≤width) : (bits width).length=width := by simp [bits]; omega

theorem written_word (width : ℕ) (positive : 1≤width) :
    Function.update (RulerWordMap.word (List.replicate width (bitSymbol (a := 2) false))) 0 (bitSymbol true)=
      RulerWordMap.word ((bits width).map bitSymbol) := by
  have splitWidth : width=(width-1)+1 := by omega
  conv_lhs => rw [splitWidth]
  simp only [List.replicate_succ,bits,List.map_cons,List.map_replicate,RulerWordMap.word,putWord,Function.update_idem]

private theorem writes (tape : ℤ → Fin 6) :
    HoareTime writeOne (· = FiniteReturnStack.bank tape 0)
      (· = FiniteReturnStack.bank (Function.update tape 0 (bitSymbol true)) 0) 1 := by
  rintro current rfl
  refine ⟨1,⟨1,fun _ => 0,fun _ => Function.update tape 0 (bitSymbol true)⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,writeOne,FiniteReturnStack.bank,Tapes.start,↓reduceIte,Move.offset,add_zero]
    congr 1
    congr 1
    funext slot position
    by_cases atOrigin : position=0 <;> simp [atOrigin]
  · simp [step,writeOne]

/-- Generate the complete unit operand from a blank destination, returning
all heads. No preconstructed unit word appears in the input. -/
theorem runs (source : List Bool) (nonempty : source≠[]) :
    HoareTime program (· = input source) (· = output source) (4*source.length+11) := by
  have nonblank : ∀ symbol ∈ source.map (bitSymbol (a := 2)),symbol≠blank := by
    intro symbol member
    obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
    cases bit <;> decide
  have filled := RulerWordMap.runs (fun _ : Fin 6 => bitSymbol false) (source.map bitSymbol)
    nonblank (by intro symbol member; decide)
  simp only [RulerWordMap.output,List.map_const',List.length_map] at filled
  let zeroTape := RulerWordMap.word (List.replicate source.length (bitSymbol (a := 2) false))
  have written := RecoverWorkspace.runs_one_at writeOne (2 : Fin 3)
    (RulerWordMap.bank (RulerWordMap.word (List.replicate source.length (bitSymbol true)))
      (RulerWordMap.word (source.map bitSymbol)) zeroTape 0 0 0)
    zeroTape (Function.update zeroTape 0 (bitSymbol true)) 0 0 rfl rfl (writes zeroTape)
  have positive : 1≤source.length := List.length_pos_of_ne_nil nonempty
  have endpoint : setTape (RulerWordMap.bank (RulerWordMap.word (List.replicate source.length (bitSymbol true)))
      (RulerWordMap.word (source.map bitSymbol)) zeroTape 0 0 0) (2 : Fin 3)
      (Function.update zeroTape 0 (bitSymbol true)) 0=output source := by
    apply Placement.Tapes.ext'
    · intro slot; fin_cases slot <;> rfl
    · intro slot
      fin_cases slot
      · rfl
      · rfl
      · exact written_word source.length positive
  unfold program input fill write
  apply (filled.seq written).consequence (fun _ ready => ready) _ (by omega)
  intro finalBank finished
  exact finished.trans endpoint

theorem output_eq_input_update (source : List Bool) :
    output source=setTape (input source) (2 : Fin 3)
      (RulerWordMap.word ((bits source.length).map bitSymbol)) 0 := by
  apply Placement.Tapes.ext'
  · intro slot; fin_cases slot <;> simp [output,input,RulerWordMap.input,RulerWordMap.bank,RulerCopy.cfg,Config.tapes,setTape]
  · intro slot; fin_cases slot <;> simp [output,input,RulerWordMap.input,RulerWordMap.bank,RulerCopy.cfg,Config.tapes,setTape]

/-- The generated word is the integer one, not a precision-scaled unit. -/
theorem signed_bits (width : ℕ) (wideEnough : 2≤width) : TwosComplement.signed (bits width)=1 := by
  have unsigned : Counter.value (bits width)=1 := by
    simp [bits,Counter.value]
  have small : (Counter.value (bits width) : ℤ)<(2 : ℤ)^((bits width).length-1) := by
    rw [unsigned,bits_length width (by omega)]
    exact_mod_cast Nat.one_lt_two_pow (by omega : width-1≠0)
  rw [FixedMulTruncation.signed_eq_value_of_small _ (by simp [bits]) small,unsigned]
  norm_num

end
end IntegerMultBounds.Machine.ChirpUnitOperand
