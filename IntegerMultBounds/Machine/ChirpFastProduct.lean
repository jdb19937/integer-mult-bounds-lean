module

public import IntegerMultBounds.Machine.FixedMulTruncation
public import IntegerMultBounds.Schoenhage.FixedMulProgram
public import IntegerMultBounds.Schoenhage.AlphaLift

/-! The existing literal quasi-linear fixed-point multiplier in the six-symbol
native chirp alphabet. Its signed correctness supports full numerator products
at zero dropped precision and later truncation after exact complex sums.
Neither a product oracle nor an abstract multiplication execution is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpFastProduct
noncomputable section
open TwosComplement (signed)
open Schoenhage Strm Tp

abbrev tapeCount := 91

def encoding : Alphabet.Encoding 0 2 := Schoenhage.embed (by decide : 0≤2)
def program := Alphabet.program encoding Schoenhage.fmProg

def input (left right : List Bool) (dropPrecision width : ℕ) : Tapes tapeCount 2 :=
  Alphabet.mapTapes encoding (Schoenhage.rawFM left right dropPrecision width [])
def output (left right : List Bool) (dropPrecision width : ℕ) : Tapes tapeCount 2 :=
  Alphabet.mapTapes encoding (Schoenhage.rawFM left right dropPrecision width (FixedMul.result left right dropPrecision width))

/-- The concrete quasi-linear program executes on the same finite alphabet
as native complex arithmetic and clears all private multiplier work. -/
theorem runs (left right : List Bool) (dropPrecision width : ℕ)
    (leftWidth : left.length=width) (rightWidth : right.length=width)
    (widthPositive : 1≤width) (dropFits : dropPrecision≤width) :
    HoareTime program (· = input left right dropPrecision width) (· = output left right dropPrecision width)
      (Schoenhage.fmTime width) := by
  have mapped := Alphabet.map_hoare encoding (Schoenhage.fmProg_time leftWidth rightWidth widthPositive dropFits)
  apply mapped.consequence
  · intro current ready
    exact ⟨_,rfl,ready⟩
  · rintro finalBank ⟨original,rfl,rfl⟩
    rfl
  · exact le_rfl

/-- Actual multiplication and signed truncation with independent operand
scale and drop precision. The result guard is its centered representability,
not a supplied arithmetic-result or machine-execution premise. -/
theorem runs_truncated (left right : List Bool) (dropPrecision width : ℕ)
    (leftWidth : left.length=width) (rightWidth : right.length=width)
    (widthPositive : 1≤width) (dropFits : dropPrecision≤width)
    (leftNotMinimum : signed left≠-(2 : ℤ)^(left.length-1))
    (rightNotMinimum : signed right≠-(2 : ℤ)^(right.length-1))
    (outputFits : |signed left*signed right|/2^dropPrecision<(2 : ℤ)^(width-1)) :
    HoareTime program (· = input left right dropPrecision width) (· = output left right dropPrecision width)
      (Schoenhage.fmTime width) ∧
      (FixedMul.result left right dropPrecision width).length=width ∧
      signed (FixedMul.result left right dropPrecision width)=(signed left*signed right).tdiv (2^dropPrecision) := by
  refine ⟨runs left right dropPrecision width leftWidth rightWidth widthPositive dropFits,
    ?_,
    FixedMulTruncation.signed_result_of_fits left right dropPrecision width leftWidth rightWidth widthPositive dropFits
      leftNotMinimum rightNotMinimum outputFits⟩
  unfold FixedMul.result
  split_ifs <;> simp [TwosComplement.negWord_length,Gather.field_length]

/-- At a sufficiently wide signed numerator port, the same actual fast
program computes the full integer product with no dropped fractional bits.
Original operand-scale bounds derive every signed guard. -/
theorem runs_exact (left right : List Bool) (operandScale width : ℕ)
    (leftWidth : left.length=width) (rightWidth : right.length=width)
    (wideEnough : 2*operandScale+2≤width)
    (leftBound : |signed left|≤(2 : ℤ)^operandScale) (rightBound : |signed right|≤(2 : ℤ)^operandScale) :
    HoareTime program (· = input left right 0 width) (· = output left right 0 width) (Schoenhage.fmTime width) ∧
      (FixedMul.result left right 0 width).length=width ∧
      signed (FixedMul.result left right 0 width)=signed left*signed right := by
  have leftNotMinimum := FixedMul.x_ne_min left operandScale width leftWidth (by omega) leftBound
  have rightNotMinimum := FixedMul.x_ne_min right operandScale width rightWidth (by omega) rightBound
  have productBound : |signed left*signed right|≤(2 : ℤ)^(2*operandScale) := by
    rw [abs_mul,show (2 : ℤ)^(2*operandScale)=(2^operandScale)^2 by rw [pow_mul']]
    simpa only [pow_two] using mul_le_mul leftBound rightBound (abs_nonneg _) (show 0≤(2 : ℤ)^operandScale by positivity)
  have productFits : |signed left*signed right|/2^0<(2 : ℤ)^(width-1) := by
    simp only [pow_zero,Int.ediv_one]
    exact productBound.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))
  have execution := runs_truncated left right 0 width leftWidth rightWidth (by omega) (by omega)
    leftNotMinimum rightNotMinimum productFits
  simpa only [pow_zero,Int.tdiv_one] using execution

/-- Every entire non-interface tape is genuinely blank with its head at zero.
Operands, precision/width rulers and the actual result are the only survivors. -/
theorem workspace_blank (left right : List Bool) (dropPrecision width : ℕ) (slot : Fin tapeCount)
    (notLeft : slot≠zF) (notRight : slot≠zG) (notPrecision : slot≠iP) (notWidth : slot≠iW) (notOutput : slot≠zO) :
    (output left right dropPrecision width).tape slot=(fun _ => blank) ∧
      (output left right dropPrecision width).head slot=0 := by
  simp [output,Alphabet.mapTapes,Schoenhage.rawFM,encoding,Schoenhage.embed,
    notLeft,notRight,notPrecision,notWidth,notOutput,blank]


end
end IntegerMultBounds.Machine.ChirpFastProduct
