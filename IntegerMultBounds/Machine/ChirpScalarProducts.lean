module

public import IntegerMultBounds.Machine.ChirpFastNativeProduct

/-! Four exact scalar products on one shared fast-multiplier workspace.
Original order is real(left), imaginary(left), real(right), imaginary(right).
The four native destinations occupy the kernel's vacated interface slots. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpScalarProducts
noncomputable section
open Schoenhage Strm Tp

abbrev tapeCount := 97

def leftIndex : Fin 4 → Fin 4 := ![0,1,0,1]
def rightIndex : Fin 4 → Fin 4 := ![2,3,3,2]
def resultSlot : Fin 4 → Fin tapeCount := ![88,89,84,86]

def slots (product : Fin 4) (slot : Fin 92) : Fin tapeCount :=
  if slot.val=88 then ⟨91+(leftIndex product).val,by change 91+(leftIndex product).val<97; have := (leftIndex product).isLt; omega⟩
  else if slot.val=89 then ⟨91+(rightIndex product).val,by change 91+(rightIndex product).val<97; have := (rightIndex product).isLt; omega⟩
  else if slot.val=84 then 95
  else if slot.val=86 then 96
  else if slot.val=91 then resultSlot product
  else ⟨slot.val,by change slot.val<97; omega⟩

theorem slots_injective (product : Fin 4) : Function.Injective (slots product) := by
  fin_cases product <;> decide

def placement (product : Fin 4) :=
  InjectivePlacement.placement (slots product) (slots_injective product) (by decide : 92+5=97)

def call (product : Fin 4) := Placement.placed ChirpFastNativeProduct.program (placement product)
def program := seq (seq (seq (call 0) (call 1)) (call 2)) (call 3)

def words (operands : Fin 4 → List Bool) (width : ℕ) (product : Fin 4) :=
  ChirpArithmeticCodec.nativeBits (FixedMul.result (operands (leftIndex product)) (operands (rightIndex product)) 0 width)

/-- A placed scalar call writes exactly its own native destination. Its
entire complementary bank, including earlier product words, is retained. -/
theorem runs_call (product : Fin 4) (operands : Fin 4 → List Bool) (width : ℕ)
    (operandWidths : ∀ index,(operands index).length=width) (widthPositive : 1≤width)
    (current : Tapes tapeCount 2)
    (activeReady : Placement.active (placement product) current=
      ChirpFastNativeProduct.input (operands (leftIndex product)) (operands (rightIndex product)) 0 width) :
    HoareTime (call product) (· = current)
      (· = SharedPlacementAlphabet.setTape current (resultSlot product)
        (RulerWordMap.word ((words operands width product).map RadixDigits.digitSymbol)) 0)
      (Schoenhage.fmTime width+6*width+14) := by
  have executed := Placement.hoare_at
    (ChirpFastNativeProduct.runs (operands (leftIndex product)) (operands (rightIndex product)) 0 width
      (operandWidths _) (operandWidths _) widthPositive (by omega)) (placement product) current activeReady
  apply executed.consequence (fun _ ready => ready) _ le_rfl
  rintro finalBank ⟨localBank,rfl,rfl⟩
  rw [ChirpFastNativeProduct.output_eq_input_update,←activeReady,placement,InjectivePlacement.replace_set]
  rfl

theorem words_length (operands : Fin 4 → List Bool) (width : ℕ) (product : Fin 4) :
    (words operands width product).length=width := by
  unfold words ChirpArithmeticCodec.nativeBits FixedMul.result
  split_ifs <;> simp [TwosComplement.negWord_length,Gather.field_length]

/-- All four published words are full signed scalar products, before any
complex sum or rounding. The original operand-scale bounds derive guards. -/
theorem words_signed (operands : Fin 4 → List Bool) (operandScale width : ℕ) (product : Fin 4)
    (operandWidths : ∀ index,(operands index).length=width)
    (wideEnough : 2*operandScale+2≤width)
    (operandBounds : ∀ index,|TwosComplement.signed (operands index)|≤(2 : ℤ)^operandScale) :
    ButterflySigned.signedValue (width-1) (words operands width product)=
      TwosComplement.signed (operands (leftIndex product))*TwosComplement.signed (operands (rightIndex product)) := by
  exact (ChirpFastNativeProduct.runs_exact (operands (leftIndex product)) (operands (rightIndex product))
    operandScale width (operandWidths _) (operandWidths _) wideEnough (operandBounds _) (operandBounds _)).2.2.1

/-- Literal stages: original raw operands at 91--94, width ruler at 96,
zero-drop precision and all private work blank; only completed results appear. -/
def stage (operands : Fin 4 → List Bool) (width completed : ℕ) : Tapes tapeCount 2 :=
  ⟨fun _ => 0,fun slot =>
    if slot.val=91 then RulerWordMap.word ((operands 0).map bitSymbol)
    else if slot.val=92 then RulerWordMap.word ((operands 1).map bitSymbol)
    else if slot.val=93 then RulerWordMap.word ((operands 2).map bitSymbol)
    else if slot.val=94 then RulerWordMap.word ((operands 3).map bitSymbol)
    else if slot.val=96 then RulerWordMap.word (List.replicate width (bitSymbol true))
    else if slot.val=88 ∧ 0<completed then RulerWordMap.word ((words operands width 0).map RadixDigits.digitSymbol)
    else if slot.val=89 ∧ 1<completed then RulerWordMap.word ((words operands width 1).map RadixDigits.digitSymbol)
    else if slot.val=84 ∧ 2<completed then RulerWordMap.word ((words operands width 2).map RadixDigits.digitSymbol)
    else if slot.val=86 ∧ 3<completed then RulerWordMap.word ((words operands width 3).map RadixDigits.digitSymbol)
    else fun _ => blank⟩

def input (operands : Fin 4 → List Bool) (width : ℕ) := stage operands width 0
def output (operands : Fin 4 → List Bool) (width : ℕ) := stage operands width 4

private theorem active_stage (operands : Fin 4 → List Bool) (width : ℕ) (product : Fin 4) :
    Placement.active (placement product) (stage operands width product.val)=
      ChirpFastNativeProduct.input (operands (leftIndex product)) (operands (rightIndex product)) 0 width := by
  rw [placement,InjectivePlacement.active_bank]
  apply Placement.Tapes.ext'
  · intro slot
    refine Fin.addCases (m := 91) (n := 1) (fun index => ?_) (fun index => ?_) slot
    all_goals simp [stage,ChirpFastNativeProduct.input,ChirpFastNativeProduct.empty,
      Tapes.append,ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM]
  · intro slot
    rw [ChirpFastNativeProduct.input_tape_zero]
    by_cases isLeft : slot.val=88
    · fin_cases product <;> simp [stage,slots,leftIndex,tapeCount,isLeft]
    · by_cases isRight : slot.val=89
      · fin_cases product <;> simp [stage,slots,rightIndex,tapeCount,isRight]
      · by_cases isPrecision : slot.val=84
        · fin_cases product <;> simp [stage,slots,tapeCount,isPrecision]
        · by_cases isWidth : slot.val=86
          · fin_cases product <;> simp [stage,slots,tapeCount,isWidth]
          · by_cases isNative : slot.val=91
            · fin_cases product <;> simp [stage,slots,resultSlot,tapeCount,isNative]
            · have notSecond : slot.val≠92 := by omega
              have notThird : slot.val≠93 := by omega
              have notFourth : slot.val≠94 := by omega
              have notRuler : slot.val≠96 := by omega
              simp [stage,slots,tapeCount,
                isLeft,isRight,isPrecision,isWidth,isNative,notSecond,notThird,notFourth,notRuler]

private theorem stage_update (operands : Fin 4 → List Bool) (width : ℕ) (product : Fin 4) :
    SharedPlacementAlphabet.setTape (stage operands width product.val) (resultSlot product)
      (RulerWordMap.word ((words operands width product).map RadixDigits.digitSymbol)) 0=
      stage operands width (product.val+1) := by
  apply Placement.Tapes.ext'
  · intro slot
    simp [SharedPlacementAlphabet.setTape,stage]
  · intro slot
    fin_cases product
    all_goals by_cases atRealReal : slot.val=88
    all_goals by_cases atImaginaryImaginary : slot.val=89
    all_goals by_cases atRealImaginary : slot.val=84
    all_goals by_cases atImaginaryReal : slot.val=86
    all_goals simp [SharedPlacementAlphabet.setTape,Function.update_apply,stage,resultSlot,
      Fin.ext_iff,tapeCount,atRealReal,atImaginaryImaginary,atRealImaginary,atImaginaryReal]

/-- All four actual fast multiplications execute from the original operand
bank, sharing one scratch block. No intermediate run/readiness premise is
supplied; every complete intermediate bank is proved from the layout. -/
theorem runs (operands : Fin 4 → List Bool) (width : ℕ)
    (operandWidths : ∀ index,(operands index).length=width) (widthPositive : 1≤width) :
    HoareTime program (· = input operands width) (· = output operands width)
      (4*Schoenhage.fmTime width+24*width+59) := by
  have stepRun (product : Fin 4) : HoareTime (call product)
      (· = stage operands width product.val) (· = stage operands width (product.val+1))
      (Schoenhage.fmTime width+6*width+14) := by
    have executed := runs_call product operands width operandWidths widthPositive
      (stage operands width product.val) (active_stage operands width product)
    simpa only [stage_update] using executed
  unfold program input output
  exact (((stepRun 0).seq (stepRun 1)).seq (stepRun 2)).seq (stepRun 3) |>.consequence
    (fun _ ready => ready) (fun _ finished => finished) (by omega)

theorem output_result (operands : Fin 4 → List Bool) (width : ℕ) (product : Fin 4) :
    (output operands width).tape (resultSlot product)=
      RulerWordMap.word ((words operands width product).map RadixDigits.digitSymbol) := by
  fin_cases product <;> simp [output,stage,resultSlot,tapeCount]

theorem output_head (operands : Fin 4 → List Bool) (width : ℕ) (slot : Fin tapeCount) :
    (output operands width).head slot=0 := rfl

/-- All original operand/control tapes are retained literally, including
the empty zero-drop precision ruler. -/
theorem original_retained (operands : Fin 4 → List Bool) (width : ℕ) (slot : Fin tapeCount)
    (original : 91≤slot.val) : (output operands width).tape slot=(input operands width).tape slot := by
  have notRealReal : slot.val≠88 := by omega
  have notImaginaryImaginary : slot.val≠89 := by omega
  have notRealImaginary : slot.val≠84 := by omega
  have notImaginaryReal : slot.val≠86 := by omega
  simp [input,output,stage,notRealReal,notImaginaryImaginary,notRealImaginary,notImaginaryReal]

/-- Every entire non-output scratch tape is blank, not merely its live
segment; the shared workspace is ready for the following arithmetic stage. -/
theorem workspace_blank (operands : Fin 4 → List Bool) (width : ℕ) (slot : Fin tapeCount)
    (scratch : slot.val<91) (notResult : ∀ product,resultSlot product≠slot) :
    (output operands width).tape slot=(fun _ => blank) := by
  have notRealReal : slot.val≠88 := by
    intro equal
    apply notResult 0
    apply Fin.ext
    simpa [resultSlot,tapeCount] using equal.symm
  have notImaginaryImaginary : slot.val≠89 := by
    intro equal
    apply notResult 1
    apply Fin.ext
    simpa [resultSlot,tapeCount] using equal.symm
  have notRealImaginary : slot.val≠84 := by
    intro equal
    apply notResult 2
    apply Fin.ext
    simpa [resultSlot,tapeCount] using equal.symm
  have notImaginaryReal : slot.val≠86 := by
    intro equal
    apply notResult 3
    apply Fin.ext
    simpa [resultSlot,tapeCount] using equal.symm
  have notFirst : slot.val≠91 := by omega
  have notSecond : slot.val≠92 := by omega
  have notThird : slot.val≠93 := by omega
  have notFourth : slot.val≠94 := by omega
  have notWidth : slot.val≠96 := by omega
  simp [output,stage,notFirst,notSecond,notThird,notFourth,notWidth,
    notRealReal,notImaginaryImaginary,notRealImaginary,notImaginaryReal]

end
end IntegerMultBounds.Machine.ChirpScalarProducts
