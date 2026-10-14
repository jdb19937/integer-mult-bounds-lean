module

public import IntegerMultBounds.Machine.ChirpUnitOperand

/-! Signed truncation toward zero via the actual fast multiplier, with its
unit operand physically generated from blank storage. Operand scale is not
tied to dropped precision, so this can round the already formed complex sums. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpTruncate
noncomputable section
open Schoenhage Strm Tp

def slots : Fin 3 → Fin 92 := ![Fin.castAdd 1 iW,Fin.castAdd 1 zF,Fin.castAdd 1 zG]
theorem slots_injective : Function.Injective slots := by decide

def placement := InjectivePlacement.placement slots slots_injective (by decide : 3+89=92)
def setup := Placement.placed ChirpUnitOperand.program placement
def program := seq setup ChirpFastNativeProduct.program

def input (numerator : List Bool) (dropPrecision width : ℕ) :=
  ChirpFastNativeProduct.input numerator [] dropPrecision width

def output (numerator : List Bool) (dropPrecision width : ℕ) :=
  ChirpFastNativeProduct.output numerator (ChirpUnitOperand.bits width) dropPrecision width

def words (numerator : List Bool) (dropPrecision width : ℕ) :=
  ChirpArithmeticCodec.nativeBits (FixedMul.result numerator (ChirpUnitOperand.bits width) dropPrecision width)

private theorem active_input (numerator : List Bool) (dropPrecision width : ℕ) (wordWidth : numerator.length=width) :
    Placement.active placement (input numerator dropPrecision width)=ChirpUnitOperand.input numerator := by
  rw [placement,InjectivePlacement.active_bank]
  apply Placement.Tapes.ext'
  · intro slot; fin_cases slot <;> rfl
  · intro slot
    fin_cases slot
    · change (ChirpFastProduct.input numerator [] dropPrecision width).tape iW=
        RulerWordMap.word (List.replicate (numerator.map bitSymbol).length (bitSymbol true))
      simpa [ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,Schoenhage.ones,List.length_map,
        wordWidth,List.map_replicate,iW,zF,zG,iP,zO] using ChirpFastNativeProduct.mapped_word (List.replicate width true)
    · change (ChirpFastProduct.input numerator [] dropPrecision width).tape zF=RulerWordMap.word (numerator.map bitSymbol)
      simpa [ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,zF,zG,iW,iP,zO]
        using ChirpFastNativeProduct.mapped_word numerator
    · change (ChirpFastProduct.input numerator [] dropPrecision width).tape zG=(fun _ => blank)
      simpa [ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,zF,zG,iW,iP,zO,RulerWordMap.word,putWord]
        using ChirpFastNativeProduct.mapped_word []

/-- Actual unit construction followed by scalar truncation and native
publication. The input has no unit word or prepared output. -/
theorem runs (numerator : List Bool) (dropPrecision width : ℕ)
    (wordWidth : numerator.length=width) (widthPositive : 1≤width) (dropFits : dropPrecision≤width) :
    HoareTime program (· = input numerator dropPrecision width) (· = output numerator dropPrecision width)
      (Schoenhage.fmTime width+10*width+26) := by
  have nonempty : numerator≠[] := by intro empty; rw [empty] at wordWidth; simp at wordWidth; omega
  have active := active_input numerator dropPrecision width wordWidth
  have built := Placement.hoare_at (ChirpUnitOperand.runs numerator nonempty) placement (input numerator dropPrecision width) active
  have setupRun : HoareTime setup (· = input numerator dropPrecision width)
      (· = ChirpFastNativeProduct.input numerator (ChirpUnitOperand.bits width) dropPrecision width) (4*width+11) := by
    apply built.consequence (fun _ ready => ready) _ (by rw [wordWidth])
    rintro finalBank ⟨localBank,rfl,rfl⟩
    rw [ChirpUnitOperand.output_eq_input_update,←active,placement,InjectivePlacement.replace_set]
    change SharedPlacementAlphabet.setTape (ChirpFastNativeProduct.input numerator [] dropPrecision width)
      (Fin.castAdd 1 zG) (RulerWordMap.word ((ChirpUnitOperand.bits numerator.length).map bitSymbol)) 0=_
    rw [wordWidth,ChirpFastNativeProduct.input_right_update]
  have truncated := ChirpFastNativeProduct.runs numerator (ChirpUnitOperand.bits width) dropPrecision width
    wordWidth (ChirpUnitOperand.bits_length width widthPositive) widthPositive dropFits
  unfold program output
  exact (setupRun.seq truncated).consequence (fun _ ready => ready) (fun _ finished => finished) (by omega)

/-- The native output is exactly the signed quotient toward zero. Guards
apply to the combined numerator, independently of its dropped precision. -/
theorem words_signed (numerator : List Bool) (dropPrecision width : ℕ)
    (wordWidth : numerator.length=width) (wideEnough : 2≤width) (dropFits : dropPrecision≤width)
    (notMinimum : TwosComplement.signed numerator≠-(2 : ℤ)^(width-1))
    (quotientFits : |TwosComplement.signed numerator|/2^dropPrecision<(2 : ℤ)^(width-1)) :
    ButterflySigned.signedValue (width-1) (words numerator dropPrecision width)=
      (TwosComplement.signed numerator).tdiv (2^dropPrecision) := by
  have unitSigned := ChirpUnitOperand.signed_bits width wideEnough
  have unitLength := ChirpUnitOperand.bits_length width (by omega)
  have unitNotMinimum : TwosComplement.signed (ChirpUnitOperand.bits width)≠-(2 : ℤ)^((ChirpUnitOperand.bits width).length-1) := by
    rw [unitSigned,unitLength]
    have positive : (0 : ℤ)<2^(width-1) := by positivity
    omega
  have computed := ChirpFastProduct.runs_truncated numerator (ChirpUnitOperand.bits width) dropPrecision width
    wordWidth unitLength (by omega) dropFits (by simpa only [wordWidth] using notMinimum) unitNotMinimum
    (by simpa only [unitSigned,mul_one] using quotientFits)
  rw [words,ChirpArithmeticCodec.native_signed _ (width-1) (by rw [computed.2.1]; omega),computed.2.2,unitSigned,mul_one]

theorem words_length (numerator : List Bool) (dropPrecision width : ℕ) :
    (words numerator dropPrecision width).length=width := by
  unfold words ChirpArithmeticCodec.nativeBits FixedMul.result
  split_ifs <;> simp [TwosComplement.negWord_length,Gather.field_length]

/-- The numerator scale can exceed dropped precision. Width slack derives
both signed guards, covering the exact complex sums without a new oracle. -/
theorem words_signed_of_scale (numerator : List Bool) (numeratorScale dropPrecision width : ℕ)
    (wordWidth : numerator.length=width) (wideEnough : numeratorScale+2≤width)
    (dropFits : dropPrecision≤width)
    (numeratorBound : |TwosComplement.signed numerator|≤(2 : ℤ)^numeratorScale) :
    ButterflySigned.signedValue (width-1) (words numerator dropPrecision width)=
      (TwosComplement.signed numerator).tdiv (2^dropPrecision) := by
  have notMinimum := FixedMul.x_ne_min numerator numeratorScale width wordWidth wideEnough numeratorBound
  have quotientLe : |TwosComplement.signed numerator|/2^dropPrecision≤|TwosComplement.signed numerator| := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Nat.div_le_self (TwosComplement.signed numerator).natAbs (2^dropPrecision)
  have threshold : (2 : ℤ)^numeratorScale<2^(width-1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  exact words_signed numerator dropPrecision width wordWidth (by omega) dropFits
    (by simpa only [wordWidth] using notMinimum) (lt_of_le_of_lt (le_trans quotientLe numeratorBound) threshold)

theorem output_head (numerator : List Bool) (dropPrecision width : ℕ) (slot : Fin 92) :
    (output numerator dropPrecision width).head slot=0 := ChirpFastNativeProduct.output_head _ _ _ _ _

theorem output_result (numerator : List Bool) (dropPrecision width : ℕ) :
    (output numerator dropPrecision width).tape ChirpFastNativeProduct.nativeSlot=
      RulerWordMap.word ((words numerator dropPrecision width).map RadixDigits.digitSymbol) :=
  ChirpFastNativeProduct.native_tape _ _ _ _

end
end IntegerMultBounds.Machine.ChirpTruncate
