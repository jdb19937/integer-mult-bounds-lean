module

public import IntegerMultBounds.Machine.ChirpMarkedProducts
public import IntegerMultBounds.Machine.ChirpProductNumerator

/-! Actual four full scalar multiplications, marked-control construction and
exact complex numerator sums on one ninety-seven-tape bank. Rounding remains
a later operation, so the four scalar products are never rounded separately. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpExactProduct
noncomputable section

def sources (operands : Fin 4 → List Bool) (width : ℕ) (index : ℕ) :=
  ChirpScalarProducts.words operands width ⟨index%4,by omega⟩

def placement : Fin (14+83) ≃ Fin 97 := Equiv.refl _
def addProgram := Placement.placed ChirpProductNumerator.program placement
def program := seq ChirpMarkedProducts.program addProgram

def input := ChirpMarkedProducts.input
def output (operands : Fin 4 → List Bool) (width : ℕ) :=
  Placement.replace placement (ChirpMarkedProducts.output operands width)
    (ChirpProductNumerator.output (sources operands width))

def words (operands : Fin 4 → List Bool) (width : ℕ) (field : Fin 2) :=
  ChirpProductNumerator.words field (sources operands width)

private theorem sources_length (operands : Fin 4 → List Bool) (width : ℕ) :
    ∀ index,(sources operands width index).length=width := by
  intro index
  exact ChirpScalarProducts.words_length _ _ _

private theorem active_input (operands : Fin 4 → List Bool) (width : ℕ) :
    Placement.active placement (ChirpMarkedProducts.output operands width)=
      ChirpProductNumerator.input (sources operands width) := by
  apply Placement.Tapes.ext'
  · intro slot
    refine Fin.addCases (m := 4) (n := 10) (fun index => ?_) (fun index => ?_) slot
    · simp only [ChirpProductNumerator.input,Tapes.append,Fin.addCases_left]
      fin_cases index <;> simp [Placement.active,placement,ChirpMarkedProducts.output,ChirpMarkedProducts.stage,
        RadixLinearCombinationRefresh.controls]
    · simp only [ChirpProductNumerator.input,Tapes.append,Fin.addCases_right]
      have bound := index.isLt
      simp [Placement.active,placement,ChirpMarkedProducts.output,ChirpMarkedProducts.stage,
                RadixLinearCombinationBootstrap.empty,show ¬(4+index.val<4) by omega]
  · intro slot
    refine Fin.addCases (m := 4) (n := 10) (fun index => ?_) (fun index => ?_) slot
    · simp only [ChirpProductNumerator.input,Tapes.append,Fin.addCases_left]
      fin_cases index <;> simp [Placement.active,placement,ChirpMarkedProducts.output,ChirpMarkedProducts.stage,
        RadixLinearCombinationRefresh.controls,sources]
    · simp only [ChirpProductNumerator.input,Tapes.append,Fin.addCases_right]
      fin_cases index <;> simp [Placement.active,placement,ChirpMarkedProducts.output,ChirpMarkedProducts.stage,
                ChirpScalarProducts.output,ChirpScalarProducts.stage,RadixLinearCombinationBootstrap.empty]

/-- Complete genuine execution of exact complex numerator arithmetic from
four original raw operand words, one width ruler and blank work. -/
theorem runs (operands : Fin 4 → List Bool) (width : ℕ)
    (operandWidths : ∀ index,(operands index).length=width) (widthPositive : 1≤width) :
    HoareTime program (· = input operands width) (· = output operands width)
      (4*Schoenhage.fmTime width+72*width+227) := by
  have added := Placement.hoare_at (ChirpProductNumerator.runs (sources operands width) width (sources_length operands width))
    placement (ChirpMarkedProducts.output operands width) (active_input operands width)
  have addedExact : HoareTime addProgram (· = ChirpMarkedProducts.output operands width) (· = output operands width)
      (36*width+127) := by
    apply added.consequence (fun _ ready => ready) _ le_rfl
    rintro finalBank ⟨localBank,rfl,rfl⟩
    rfl
  unfold program input
  exact ((ChirpMarkedProducts.runs operands width operandWidths widthPositive).seq addedExact).consequence
    (fun _ ready => ready) (fun _ finished => finished) (by omega)

theorem words_length (operands : Fin 4 → List Bool) (width : ℕ) (field : Fin 2) :
    (words operands width field).length=width :=
  ChirpProductNumerator.words_length field _ width (sources_length operands width)

/-- Wider precision slack derives exact centered sums of the full products.
This is the numerator required before componentwise rounding toward zero. -/
theorem words_signed (operands : Fin 4 → List Bool) (operandScale width : ℕ) (field : Fin 2)
    (operandWidths : ∀ index,(operands index).length=width)
    (wideEnough : 2*operandScale+3≤width)
    (operandBounds : ∀ index,|TwosComplement.signed (operands index)|≤(2 : ℤ)^operandScale) :
    ButterflySigned.signedValue (width-1) (words operands width field)=
      if field=0 then TwosComplement.signed (operands 0)*TwosComplement.signed (operands 2)-
        TwosComplement.signed (operands 1)*TwosComplement.signed (operands 3)
      else TwosComplement.signed (operands 0)*TwosComplement.signed (operands 3)+
        TwosComplement.signed (operands 1)*TwosComplement.signed (operands 2) := by
  have productValues (index : Fin 4) :
      ButterflySigned.signedValue (width-1) (sources operands width index.val)=
        TwosComplement.signed (operands (ChirpScalarProducts.leftIndex index))*
          TwosComplement.signed (operands (ChirpScalarProducts.rightIndex index)) := by
    simp only [sources,Nat.mod_eq_of_lt index.isLt]
    exact ChirpScalarProducts.words_signed operands operandScale width index operandWidths (by omega) operandBounds
  have productBounds (index : Fin 4) :
      |ButterflySigned.signedValue (width-1) (sources operands width index.val)|≤(2 : ℤ)^(2*operandScale) := by
    rw [productValues,abs_mul,show (2 : ℤ)^(2*operandScale)=(2^operandScale)^2 by rw [pow_mul']]
    simpa only [pow_two] using mul_le_mul (operandBounds _) (operandBounds _) (abs_nonneg _)
      (show 0≤(2 : ℤ)^operandScale by positivity)
  have computed := ChirpProductNumerator.words_signed_of_scale field (sources operands width) (width-1) (2*operandScale)
    (fun index => by rw [sources_length]; omega) (by omega) productBounds
  change ButterflySigned.signedValue (width-1) (words operands width field)=_ at computed
  rw [computed]
  simp only [productValues]
  fin_cases field <;> simp [ChirpProductNumerator.numerator,ChirpScalarProducts.leftIndex,ChirpScalarProducts.rightIndex]

def resultSlot (field : Fin 2) : Fin 97 := if field=0 then 4 else 9

/-- The exact sum words occur on actual output tapes, at cell one with a
blank cell zero, as required by the existing native linear-combination format. -/
theorem output_result (operands : Fin 4 → List Bool) (width : ℕ) (field : Fin 2) :
    (output operands width).tape (resultSlot field)=
      MarkedWordCleanup.word ((words operands width field).map RadixDigits.digitSymbol) := by
  fin_cases field
  · change (Placement.replace placement (ChirpMarkedProducts.output operands width)
      (ChirpProductNumerator.output (sources operands width))).tape (placement (Fin.castAdd 83 (4 : Fin 14)))=_
    rw [Placement.replace_tape_active]
    rfl
  · change (Placement.replace placement (ChirpMarkedProducts.output operands width)
      (ChirpProductNumerator.output (sources operands width))).tape (placement (Fin.castAdd 83 (9 : Fin 14)))=_
    rw [Placement.replace_tape_active]
    rfl

theorem output_result_head (operands : Fin 4 → List Bool) (width : ℕ) (field : Fin 2) :
    (output operands width).head (resultSlot field)=0 := by
  fin_cases field
  · change (Placement.replace placement (ChirpMarkedProducts.output operands width)
      (ChirpProductNumerator.output (sources operands width))).head (placement (Fin.castAdd 83 (4 : Fin 14)))=0
    rw [Placement.replace_head_active]
    rfl
  · change (Placement.replace placement (ChirpMarkedProducts.output operands width)
      (ChirpProductNumerator.output (sources operands width))).head (placement (Fin.castAdd 83 (9 : Fin 14)))=0
    rw [Placement.replace_head_active]
    rfl

/-- Literal complete-bank endpoint, exposing all retained controls and
scalar products as well as the two exact sums and blank private arithmetic. -/
def bank (operands : Fin 4 → List Bool) (width : ℕ) : Tapes 97 2 :=
  ⟨fun slot => if slot.val<4 then 1 else 0,
    fun slot => if slot.val=0 then MarkedRadixRefresh.source (ChirpScalarProducts.words operands width 0)
      else if slot.val=1 then MarkedRadixRefresh.source (ChirpScalarProducts.words operands width 1)
      else if slot.val=2 then MarkedRadixRefresh.source (ChirpScalarProducts.words operands width 2)
      else if slot.val=3 then MarkedRadixRefresh.source (ChirpScalarProducts.words operands width 3)
      else if slot.val=4 then MarkedWordCleanup.word ((words operands width 0).map RadixDigits.digitSymbol)
      else if slot.val=9 then MarkedWordCleanup.word ((words operands width 1).map RadixDigits.digitSymbol)
      else (ChirpScalarProducts.output operands width).tape slot⟩

theorem output_eq_bank (operands : Fin 4 → List Bool) (width : ℕ) : output operands width=bank operands width := by
  apply Placement.Tapes.ext'
  · intro slot
    refine Fin.addCases (m := 14) (n := 83) (fun index => ?_) (fun index => ?_) slot
    · change (Placement.replace placement (ChirpMarkedProducts.output operands width)
        (ChirpProductNumerator.output (sources operands width))).head (placement (Fin.castAdd 83 index))=_
      rw [Placement.replace_head_active]
      fin_cases index <;> rfl
    · have outside : ∀ selected : Fin 14,placement (Fin.castAdd 83 selected)≠Fin.natAdd 14 index := by
        intro selected equal
        have values := congrArg Fin.val equal
        change selected.val=14+index.val at values
        omega
      rw [output,Placement.replace_head_other placement _ _ _ outside]
      simp [bank,ChirpMarkedProducts.output,ChirpMarkedProducts.stage,show ¬(14+index.val<4) by omega]
  · intro slot
    refine Fin.addCases (m := 14) (n := 83) (fun index => ?_) (fun index => ?_) slot
    · change (Placement.replace placement (ChirpMarkedProducts.output operands width)
        (ChirpProductNumerator.output (sources operands width))).tape (placement (Fin.castAdd 83 index))=_
      rw [Placement.replace_tape_active]
      fin_cases index <;> rfl
    · have outside : ∀ selected : Fin 14,placement (Fin.castAdd 83 selected)≠Fin.natAdd 14 index := by
        intro selected equal
        have values := congrArg Fin.val equal
        change selected.val=14+index.val at values
        omega
      rw [output,Placement.replace_tape_other placement _ _ _ outside]
      have notOne : 14+index.val≠1 := by omega
      have notTwo : 14+index.val≠2 := by omega
      have notThree : 14+index.val≠3 := by omega
      have notReal : 14+index.val≠4 := by omega
      have notImaginary : 14+index.val≠9 := by omega
      simp [bank,ChirpMarkedProducts.output,ChirpMarkedProducts.stage,notOne,notTwo,notThree,notReal,notImaginary]

end
end IntegerMultBounds.Machine.ChirpExactProduct
