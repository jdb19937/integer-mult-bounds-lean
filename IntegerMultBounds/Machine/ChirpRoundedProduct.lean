module

public import IntegerMultBounds.Machine.ChirpExactProductClean
public import IntegerMultBounds.Machine.ChirpRoundCalls
public import IntegerMultBounds.Machine.ChirpRoundedValue

/-! Complete shared-workspace complex multiplication: form full numerators,
round each component once, and physically reclaim all arithmetic scratch. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpRoundedProduct
noncomputable section
open SharedPlacementAlphabet (setTape)

attribute [local irreducible] ChirpFastProduct.stateCount

abbrev tapeCount := 98

def words (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2) :=
  ChirpNativeTruncate.words (ChirpExactProduct.words operands width field) precision width

def bank (operands : Fin 4 → List Bool) (precision width completed : ℕ)
    (rawNumerator unit : List Bool) : Tapes tapeCount 2 :=
  ⟨fun _ => 0,fun slot =>
    if slot.val=91 then RulerWordMap.word ((operands 0).map bitSymbol)
    else if slot.val=92 then RulerWordMap.word ((operands 1).map bitSymbol)
    else if slot.val=93 then RulerWordMap.word ((operands 2).map bitSymbol)
    else if slot.val=94 then RulerWordMap.word ((operands 3).map bitSymbol)
    else if slot.val=96 then RulerWordMap.word (List.replicate width (bitSymbol true))
    else if slot.val=97 then RulerWordMap.word (List.replicate precision (bitSymbol true))
    else if slot.val=4 ∧ completed=0 then ChirpConsumeNumerator.source (ChirpExactProduct.words operands width 0)
    else if slot.val=9 ∧ completed≤1 then ChirpConsumeNumerator.source (ChirpExactProduct.words operands width 1)
    else if slot.val=14 ∧ 1≤completed then RulerWordMap.word ((words operands precision width 0).map RadixDigits.digitSymbol)
    else if slot.val=15 ∧ 2≤completed then RulerWordMap.word ((words operands precision width 1).map RadixDigits.digitSymbol)
    else if slot.val=88 then RulerWordMap.word (rawNumerator.map bitSymbol)
    else if slot.val=89 then RulerWordMap.word (unit.map bitSymbol)
    else fun _ => blank⟩

def stage (operands : Fin 4 → List Bool) (precision width completed : ℕ) :=
  bank operands precision width completed [] []
def after (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2) :=
  bank operands precision width (field.val+1)
    (ChirpArithmeticCodec.rawBits (ChirpExactProduct.words operands width field)) (ChirpUnitOperand.bits width)

def ruler (precision : ℕ) : Tapes 1 2 :=
  ⟨fun _ => 0,fun _ => RulerWordMap.word (List.replicate precision (bitSymbol true))⟩
def input (operands : Fin 4 → List Bool) (precision width : ℕ) :=
  (ChirpExactProductClean.input operands width).append (ruler precision)
def output (operands : Fin 4 → List Bool) (precision width : ℕ) := stage operands precision width 2

def eraseNumerator := RecoverWorkspace.atProgram (RecoverArrayCleanup.eraseOrigin (alphabet := 2)) (88 : Fin tapeCount)
def eraseUnit := RecoverWorkspace.atProgram (RecoverArrayCleanup.eraseOrigin (alphabet := 2)) (89 : Fin tapeCount)
def reclaim := seq eraseNumerator eraseUnit
def roundOne (field : Fin 2) := seq (ChirpRoundCalls.call field) reclaim
def program := seq (extend ChirpExactProductClean.program 1) (seq (roundOne 0) (roundOne 1))

private theorem exact_endpoint (operands : Fin 4 → List Bool) (precision width : ℕ) :
    (ChirpExactProductClean.output operands width).append (ruler precision)=stage operands precision width 0 := by
  rw [ChirpExactProductClean.output_eq_bank]
  apply Placement.Tapes.ext'
  · intro slot; fin_cases slot <;> rfl
  · intro slot; fin_cases slot <;> rfl

private theorem active_stage (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2) :
    Placement.active (ChirpRoundCalls.placement field) (stage operands precision width field.val)=
      ChirpNativeTruncate.input (ChirpExactProduct.words operands width field) precision width := by
  rw [ChirpRoundCalls.placement,InjectivePlacement.active_bank,ChirpNativeTruncate.input_eq_bank]
  apply Placement.Tapes.ext'
  · intro slot; fin_cases field <;> fin_cases slot <;> rfl
  · intro slot
    fin_cases field <;> fin_cases slot <;>
      simp [stage,bank,ChirpRoundCalls.slots,ChirpRoundCalls.resultSlot,ChirpRoundCalls.sourceSlot,
        ChirpNativeTruncate.inputBank,ChirpNativeTruncate.tapeCount,tapeCount,RulerWordMap.word,putWord]

private theorem active_after (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2) :
    Placement.active (ChirpRoundCalls.placement field) (after operands precision width field)=
      ChirpNativeTruncate.output (ChirpExactProduct.words operands width field) precision width := by
  rw [ChirpRoundCalls.placement,InjectivePlacement.active_bank,ChirpNativeTruncate.output_eq_bank]
  apply Placement.Tapes.ext'
  · intro slot; fin_cases field <;> fin_cases slot <;> rfl
  · intro slot
    fin_cases field <;> fin_cases slot <;>
      simp [after,bank,words,ChirpRoundCalls.slots,ChirpRoundCalls.resultSlot,ChirpRoundCalls.sourceSlot,
        ChirpNativeTruncate.bank,ChirpNativeTruncate.tapeCount,tapeCount,RulerWordMap.word]

private def candidate (field : Fin 2) (slot : Fin tapeCount) : Fin 93 :=
  if slot.val=84 then 4 else if slot.val=86 then 9 else if slot.val=95 then 14
  else if slot.val=(if field=0 then 15 else 4) then 15
  else if slot.val=97 then 84 else if slot.val=96 then 86
  else if slot=ChirpRoundCalls.resultSlot field then 91
  else if slot=ChirpRoundCalls.sourceSlot field then 92
  else ⟨slot.val%93,by omega⟩

private theorem outside_cases (field : Fin 2) (slot : Fin tapeCount)
    (outside : ∀ selected,ChirpRoundCalls.slots field selected≠slot) :
    slot.val=91 ∨ slot.val=92 ∨ slot.val=93 ∨ slot.val=94 ∨
      (if field=0 then slot.val=9 else slot.val=14) := by
  have missing := outside (candidate field slot)
  fin_cases field <;> fin_cases slot <;> first | decide | exact False.elim (missing rfl)

private theorem retained_frame (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2)
    (slot : Fin tapeCount) (outside : ∀ selected,ChirpRoundCalls.slots field selected≠slot) :
    (after operands precision width field).head slot=(stage operands precision width field.val).head slot ∧
      (after operands precision width field).tape slot=(stage operands precision width field.val).tape slot := by
  have classified := outside_cases field slot outside
  clear outside
  fin_cases field <;> rcases classified with retained | retained | retained | retained | retained
  all_goals first
    | have slotEq : slot=(91 : Fin tapeCount) := Fin.ext retained
      subst slot; exact ⟨rfl,rfl⟩
    | have slotEq : slot=(92 : Fin tapeCount) := Fin.ext retained
      subst slot; exact ⟨rfl,rfl⟩
    | have slotEq : slot=(93 : Fin tapeCount) := Fin.ext retained
      subst slot; exact ⟨rfl,rfl⟩
    | have slotEq : slot=(94 : Fin tapeCount) := Fin.ext retained
      subst slot; exact ⟨rfl,rfl⟩
    | have slotEq : slot=(9 : Fin tapeCount) := Fin.ext retained
      subst slot; exact ⟨rfl,rfl⟩
    | have slotEq : slot=(14 : Fin tapeCount) := Fin.ext retained
      subst slot; exact ⟨rfl,rfl⟩

private theorem runs_call (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2)
    (widthPositive : 1≤width) (precisionFits : precision≤width) :
    HoareTime (ChirpRoundCalls.call field) (· = stage operands precision width field.val)
      (· = after operands precision width field) (Schoenhage.fmTime width+13*width+37) := by
  have executed := Placement.hoare_at
    (ChirpNativeTruncate.runs (ChirpExactProduct.words operands width field) precision width
      (ChirpExactProduct.words_length _ _ _) widthPositive precisionFits)
    (ChirpRoundCalls.placement field) _ (active_stage operands precision width field)
  have endpoint := InjectivePlacement.replace_eq (ChirpRoundCalls.slots field)
    (ChirpRoundCalls.slots_injective field) (by decide : 93+5=98)
    (stage operands precision width field.val) (after operands precision width field) _
    (active_after operands precision width field) (retained_frame operands precision width field)
  apply executed.consequence (fun _ ready => ready) _ le_rfl
  rintro finalBank ⟨localBank,rfl,rfl⟩
  exact endpoint

private theorem runs_reclaim (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2)
    (widthPositive : 1≤width) :
    HoareTime reclaim (· = after operands precision width field)
      (· = stage operands precision width (field.val+1)) (4*width+7) := by
  let current := after operands precision width field
  let middle := RecoverWorkspace.erased current (88 : Fin tapeCount)
  have nonblank (bits : List Bool) : ∀ symbol ∈ bits.map (bitSymbol (a := 2)),symbol≠blank := by
    intro symbol member
    obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
    cases bit <;> decide
  have numeratorWidth : (ChirpArithmeticCodec.rawBits (ChirpExactProduct.words operands width field)).length=width := by
    simp only [ChirpArithmeticCodec.rawBits,List.length_map,ChirpExactProduct.words_length]
  have first := RecoverArrayCleanup.erase_origin_at (88 : Fin tapeCount) current
    ((ChirpArithmeticCodec.rawBits (ChirpExactProduct.words operands width field)).map bitSymbol)
    (nonblank _) (by rfl) (by rfl)
  have second := RecoverArrayCleanup.erase_origin_at (89 : Fin tapeCount) middle
    ((ChirpUnitOperand.bits width).map bitSymbol) (nonblank _) (by rfl) (by rfl)
  have final : RecoverWorkspace.erased middle (89 : Fin tapeCount)=stage operands precision width (field.val+1) := by
    apply Placement.Tapes.ext'
    · intro slot; fin_cases slot <;> rfl
    · intro slot; fin_cases slot <;> rfl
  rw [final] at second
  unfold reclaim eraseNumerator eraseUnit
  exact HoareTime.seq_bound (M := RecoverWorkspace.atProgram RecoverArrayCleanup.eraseOrigin (88 : Fin tapeCount))
    (N := RecoverWorkspace.atProgram RecoverArrayCleanup.eraseOrigin (89 : Fin tapeCount)) first second (by
      simp only [List.length_map,numeratorWidth,ChirpUnitOperand.bits_length width widthPositive]
      omega)

private theorem runs_round (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2)
    (widthPositive : 1≤width) (precisionFits : precision≤width) :
    HoareTime (roundOne field) (· = stage operands precision width field.val)
      (· = stage operands precision width (field.val+1)) (Schoenhage.fmTime width+17*width+45) := by
  exact HoareTime.seq_bound (M := ChirpRoundCalls.call field) (N := reclaim)
    (runs_call operands precision width field widthPositive precisionFits)
    (runs_reclaim operands precision width field widthPositive) (by omega)

/-- Actual full numerator formation followed by componentwise signed
truncation. Every scratch tape finishes blank and every head at origin. -/
theorem runs (operands : Fin 4 → List Bool) (precision width : ℕ)
    (operandWidths : ∀ index,(operands index).length=width)
    (widthPositive : 1≤width) (precisionFits : precision≤width) :
    HoareTime program (· = input operands precision width) (· = output operands precision width)
      (6*Schoenhage.fmTime width+122*width+359) := by
  have exactRun := FamilyPlacementAlphabet.extend_hoare
    (ChirpExactProductClean.runs operands width operandWidths widthPositive) (ruler precision)
  rw [exact_endpoint] at exactRun
  have rounded := (runs_round operands precision width 0 widthPositive precisionFits).seq
    (runs_round operands precision width 1 widthPositive precisionFits)
  exact HoareTime.seq_bound (M := extend ChirpExactProductClean.program 1)
    (N := seq (roundOne 0) (roundOne 1)) exactRun rounded (by omega)

theorem words_length (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2) :
    (words operands precision width field).length=width := ChirpNativeTruncate.words_length _ _ _

theorem output_result (operands : Fin 4 → List Bool) (precision width : ℕ) (field : Fin 2) :
    (output operands precision width).tape (ChirpRoundCalls.resultSlot field)=
      RulerWordMap.word ((words operands precision width field).map RadixDigits.digitSymbol) := by
  fin_cases field <;> rfl

theorem output_head (operands : Fin 4 → List Bool) (precision width : ℕ) (slot : Fin tapeCount) :
    (output operands precision width).head slot=0 := rfl

theorem workspace_blank (operands : Fin 4 → List Bool) (precision width : ℕ) (slot : Fin tapeCount)
    (notOperandZero : slot.val≠91) (notOperandOne : slot.val≠92)
    (notOperandTwo : slot.val≠93) (notOperandThree : slot.val≠94)
    (notWidth : slot.val≠96) (notPrecision : slot.val≠97)
    (notReal : slot.val≠14) (notImaginary : slot.val≠15) :
    (output operands precision width).tape slot=(fun _ => blank) := by
  simp [output,stage,bank,notOperandZero,notOperandOne,notOperandTwo,notOperandThree,
    notWidth,notPrecision,notReal,notImaginary,RulerWordMap.word,putWord]

/-- The published native result is exactly the manuscript's rounded complex
product, with one rounding after each complete numerator sum. -/
theorem value (operands : Fin 4 → List Bool) (precision width : ℕ)
    (operandWidths : ∀ index,(operands index).length=width)
    (wideEnough : 2*precision+3≤width)
    (operandBounds : ∀ index,|TwosComplement.signed (operands index)|≤(2 : ℤ)^precision) :
    ButterflySigned.complexValue
      (ButterflySigned.signedValue (width-1) (words operands precision width 0))
      (ButterflySigned.signedValue (width-1) (words operands precision width 1)) precision=
      NLogN.rhoC precision
        (ButterflySigned.complexValue (TwosComplement.signed (operands 0)) (TwosComplement.signed (operands 1)) precision*
          ButterflySigned.complexValue (TwosComplement.signed (operands 2)) (TwosComplement.signed (operands 3)) precision) := by
  have productBound (left right : Fin 4) :
      |TwosComplement.signed (operands left)*TwosComplement.signed (operands right)|≤(2 : ℤ)^(2*precision) := by
    rw [abs_mul,show (2 : ℤ)^(2*precision)=(2^precision)^2 by rw [pow_mul']]
    simpa only [pow_two] using mul_le_mul (operandBounds left) (operandBounds right) (abs_nonneg _)
      (show 0≤(2 : ℤ)^precision by positivity)
  have numeratorBound (field : Fin 2) :
      |ButterflySigned.signedValue (width-1) (ChirpExactProduct.words operands width field)|≤(2 : ℤ)^(2*precision+1) := by
    rw [ChirpExactProduct.words_signed operands precision width field operandWidths wideEnough operandBounds,pow_succ]
    fin_cases field
    · change |TwosComplement.signed (operands 0)*TwosComplement.signed (operands 2)-
        TwosComplement.signed (operands 1)*TwosComplement.signed (operands 3)|≤(2 : ℤ)^(2*precision)*2
      have triangle := abs_sub_le (TwosComplement.signed (operands 0)*TwosComplement.signed (operands 2))
        0 (TwosComplement.signed (operands 1)*TwosComplement.signed (operands 3))
      simp only [sub_zero,zero_sub,abs_neg] at triangle
      have first := productBound 0 2
      have second := productBound 1 3
      omega
    · change |TwosComplement.signed (operands 0)*TwosComplement.signed (operands 3)+
        TwosComplement.signed (operands 1)*TwosComplement.signed (operands 2)|≤(2 : ℤ)^(2*precision)*2
      have triangle := abs_add_le (TwosComplement.signed (operands 0)*TwosComplement.signed (operands 3))
        (TwosComplement.signed (operands 1)*TwosComplement.signed (operands 2))
      have first := productBound 0 3
      have second := productBound 1 2
      omega
  have truncated (field : Fin 2) := ChirpNativeTruncate.words_signed
    (ChirpExactProduct.words operands width field) (2*precision+1) precision width
    (ChirpExactProduct.words_length _ _ _) (by omega) (by omega) (numeratorBound field)
  simp only [words,truncated,ChirpExactProduct.words_signed operands precision width _ operandWidths wideEnough operandBounds]
  simp only [↓reduceIte,show (1 : Fin 2)≠0 by decide]
  exact ChirpRoundedValue.rounded_mul _ _ _ _ _

end
end IntegerMultBounds.Machine.ChirpRoundedProduct
