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

end
end IntegerMultBounds.Machine.ChirpScalarProducts
