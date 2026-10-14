module

public import IntegerMultBounds.Machine.RecoverCarryStep
public import IntegerMultBounds.Machine.Negate
public import IntegerMultBounds.Machine.MultiplicationInputSplit
public import IntegerMultBounds.Machine.Branch

/-! Physical absolute value of a signed binary coefficient numerator. The
machine starts at the end of a nonempty word, steps left to read its actual
sign bit, rewinds, conditionally negates, and returns the magnitude to origin.
The minimum signed value is included: its magnitude fits the unsigned word. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverMagnitude
variable {alphabet : ℕ}
open RecoverCarryStep (word)

def one (bits : List Bool) (head : ℤ) : Tapes 1 alphabet :=
  ⟨fun _ => head,fun _ => word bits⟩

def magnitude (lowBits : List Bool) (sign : Bool) : List Bool :=
  if sign then TwosComplement.negWord (lowBits ++ [sign]) else lowBits ++ [sign]

def test (symbols : Fin 1 → Fin (alphabet+4)) := decide (symbols 0 = bitSymbol true)
def prepare : Program 1 5 alphabet :=
  seq (MultiplicationInputSplit.shift .right) ReturnOrigin.program
def negative : Program 1 10 alphabet := seq (seq prepare (Negate.program alphabet)) ReturnOrigin.program
def branches : Program 1 16 alphabet := branch test negative prepare
def program : Program 1 18 alphabet := seq (MultiplicationInputSplit.shift .left) branches

private theorem nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

theorem sign_read (lowBits : List Bool) (sign : Bool) :
    test (one (alphabet := alphabet) (lowBits ++ [sign]) lowBits.length).reads = sign := by
  have atSign : word (alphabet := alphabet) (lowBits ++ [sign]) lowBits.length = bitSymbol sign := by
    unfold word
    rw [List.map_append,← putWord_append_forward,List.length_map,zero_add]
    exact putWord_head _ _ _ _
  change decide (word (lowBits ++ [sign]) lowBits.length = bitSymbol true) = sign
  rw [atSign]
  cases sign <;> simp [bitSymbol,Fin.ext_iff]

private theorem return_word (bits : List Bool) :
    HoareTime (ReturnOrigin.program (a := alphabet)) (· = one bits bits.length) (· = one bits 0)
      (bits.length + 2) := by
  simpa only [one,word,ReturnOrigin.cfg,Config.tapes,List.length_map] using
    ReturnOrigin.return_hoare (bits.map (bitSymbol (a := alphabet))) (nonblank bits)

private theorem runs_prepare (lowBits : List Bool) (sign : Bool) :
    HoareTime (prepare (alphabet := alphabet)) (· = one (lowBits ++ [sign]) lowBits.length)
      (· = one (lowBits ++ [sign]) 0) ((lowBits ++ [sign]).length + 4) := by
  have shifted := MultiplicationInputSplit.shifts (a := alphabet) .right
    (word (lowBits ++ [sign])) lowBits.length
  have endHead : (lowBits.length : ℤ) + Move.right.offset = (lowBits ++ [sign]).length := by simp [Move.offset]
  rw [endHead] at shifted
  apply (shifted.seq (return_word (lowBits ++ [sign]))).consequence
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
  omega

private theorem runs_negative (lowBits : List Bool) (sign : Bool) :
    HoareTime (negative (alphabet := alphabet)) (· = one (lowBits ++ [sign]) lowBits.length)
      (· = one (TwosComplement.negWord (lowBits ++ [sign])) 0)
      (3 * (lowBits ++ [sign]).length + 8) := by
  have negated := Negate.neg_hoare (a := alphabet) (fun _ => blank) 0 (lowBits ++ [sign]) (by rfl)
  simp only [Negate.cfg,Config.tapes,zero_add] at negated
  have restored := return_word (alphabet := alphabet) (TwosComplement.negWord (lowBits ++ [sign]))
  rw [TwosComplement.negWord_length] at restored
  apply (((runs_prepare lowBits sign).seq negated).seq restored).consequence
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
  omega

/-- The sign is discovered from tape, including for padded zero and the
minimum negative value. Every complete output cell and its head are specified. -/
theorem runs_magnitude (lowBits : List Bool) (sign : Bool) :
    HoareTime (program (alphabet := alphabet)) (· = one (lowBits ++ [sign]) (lowBits ++ [sign]).length)
      (· = one (magnitude lowBits sign) 0) (3 * (lowBits ++ [sign]).length + 11) := by
  have shifted := MultiplicationInputSplit.shifts (a := alphabet) .left
    (word (lowBits ++ [sign])) (lowBits ++ [sign]).length
  have signHead : (((lowBits ++ [sign]).length : ℕ) : ℤ) + Move.left.offset = lowBits.length := by simp [Move.offset]
  rw [signHead] at shifted
  have tested := sign_read (alphabet := alphabet) lowBits sign
  have selected : HoareTime (branches (alphabet := alphabet))
      (· = one (lowBits ++ [sign]) lowBits.length) (· = one (magnitude lowBits sign) 0)
      (3 * (lowBits ++ [sign]).length + 9) := by
    cases sign with
    | false =>
      have impossible : HoareTime (negative (alphabet := alphabet))
          (fun current => current = one (lowBits ++ [false]) lowBits.length ∧ test current.reads = true)
          (· = one (lowBits ++ [false]) 0) 0 := by
        rintro _ ⟨rfl,wrongTest⟩; rw [tested] at wrongTest; contradiction
      have prepared := (runs_prepare (alphabet := alphabet) lowBits false).consequence
        (pre' := fun current => current = one (lowBits ++ [false]) lowBits.length ∧ test current.reads = false)
        (fun _ hypothesis => hypothesis.1) (fun _ hypothesis => hypothesis) le_rfl
      apply (branch_hoare test impossible prepared).consequence
        (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
      simp only [Nat.zero_max]
      omega
    | true =>
      have negated := (runs_negative (alphabet := alphabet) lowBits true).consequence
        (pre' := fun current => current = one (lowBits ++ [true]) lowBits.length ∧ test current.reads = true)
        (fun _ hypothesis => hypothesis.1) (fun _ hypothesis => hypothesis) le_rfl
      have impossible : HoareTime (prepare (alphabet := alphabet))
          (fun current => current = one (lowBits ++ [true]) lowBits.length ∧ test current.reads = false)
          (· = one (TwosComplement.negWord (lowBits ++ [true])) 0) 0 := by
        rintro _ ⟨rfl,wrongTest⟩; rw [tested] at wrongTest; contradiction
      apply (branch_hoare test negated impossible).consequence
        (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis)
      simp only [Nat.max_zero]
      omega
  apply (shifted.seq selected).consequence (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => hypothesis)
  omega

theorem magnitude_length (lowBits : List Bool) (sign : Bool) :
    (magnitude lowBits sign).length = (lowBits ++ [sign]).length := by
  cases sign <;> simp [magnitude,TwosComplement.negWord_length]

theorem magnitude_value (lowBits : List Bool) (sign : Bool) :
    Counter.value (magnitude lowBits sign) = (TwosComplement.signed (lowBits ++ [sign])).natAbs := by
  cases sign with
  | false => simp [magnitude,TwosComplement.signed]
  | true =>
    have originalBound := Counter.value_lt (lowBits ++ [true])
    have magnitudeBound := Counter.value_lt (TwosComplement.negWord (lowBits ++ [true]))
    rw [TwosComplement.negWord_length] at magnitudeBound
    have modular := TwosComplement.negWord_value (lowBits ++ [true])
    have positive : 0 < Counter.value (lowBits ++ [true]) := by
      rw [TwosComplement.value_append]
      simp only [Counter.value,ite_true]
      positivity
    have sumEquals : Counter.value (TwosComplement.negWord (lowBits ++ [true])) +
        Counter.value (lowBits ++ [true]) = 2 ^ (lowBits ++ [true]).length := by
      by_cases sumBelowPower : Counter.value (TwosComplement.negWord (lowBits ++ [true])) +
          Counter.value (lowBits ++ [true]) < 2 ^ (lowBits ++ [true]).length
      · rw [Nat.mod_eq_of_lt sumBelowPower] at modular
        omega
      · have powerLeSum : 2 ^ (lowBits ++ [true]).length ≤
            Counter.value (TwosComplement.negWord (lowBits ++ [true])) + Counter.value (lowBits ++ [true]) := by omega
        have reducedBelow : Counter.value (TwosComplement.negWord (lowBits ++ [true])) +
            Counter.value (lowBits ++ [true]) - 2 ^ (lowBits ++ [true]).length < 2 ^ (lowBits ++ [true]).length := by omega
        rw [Nat.mod_eq_sub_mod powerLeSum,Nat.mod_eq_of_lt reducedBelow] at modular
        omega
    have signedNonpositive : TwosComplement.signed (lowBits ++ [true]) ≤ 0 := by
      simp only [TwosComplement.signed,List.getLastD_concat,ite_true]
      have castBound : (Counter.value (lowBits ++ [true]) : ℤ) ≤ 2 ^ (lowBits ++ [true]).length := by
        exact_mod_cast originalBound.le
      omega
    have absolute : (TwosComplement.signed (lowBits ++ [true])).natAbs =
        2 ^ (lowBits ++ [true]).length - Counter.value (lowBits ++ [true]) := by
      apply Int.ofNat_inj.mp
      rw [Int.natCast_natAbs,abs_of_nonpos signedNonpositive]
      simp only [TwosComplement.signed,List.getLastD_concat,ite_true]
      rw [Nat.cast_sub originalBound.le]
      push_cast
      ring
    simp only [magnitude,ite_true]
    rw [absolute]
    omega

/-- A signed dyadic coefficient can be replaced by its physically computed
magnitude without worsening its recovery margin around a natural coefficient. -/
theorem magnitude_margin (lowBits : List Bool) (sign : Bool) (precision coefficient : ℕ)
    (close : |(TwosComplement.signed (lowBits ++ [sign]) : ℝ) / 2 ^ precision - coefficient| < 1 / 2) :
    |(Counter.value (magnitude lowBits sign) : ℝ) / 2 ^ precision - coefficient| < 1 / 2 := by
  rw [magnitude_value]
  have denominatorPositive : (0 : ℝ) < 2 ^ precision := by positivity
  have absoluteValue : ((TwosComplement.signed (lowBits ++ [sign])).natAbs : ℝ) /
      2 ^ precision = |(TwosComplement.signed (lowBits ++ [sign]) : ℝ) / 2 ^ precision| := by
    rw [abs_div,abs_of_pos denominatorPositive]
    congr 1
    rw [Nat.cast_natAbs,Int.cast_abs]
  rw [absoluteValue]
  have contraction := abs_abs_sub_abs_le_abs_sub
    ((TwosComplement.signed (lowBits ++ [sign]) : ℝ) / 2 ^ precision) (coefficient : ℝ)
  have coefficientAbsolute : |(coefficient : ℝ)| = coefficient := abs_of_nonneg (Nat.cast_nonneg coefficient)
  rw [coefficientAbsolute] at contraction
  exact contraction.trans_lt close

/-- Once the physically obtained magnitude is split into fractional and
integer fields, its signed recovery margin is exactly the unsigned rounder's
input margin. The layout equation concerns bits, not a recovered coefficient. -/
theorem split_magnitude_margin (lowBits : List Bool) (sign : Bool)
    (lowerBits integerBits : List Bool) (guard : Bool) (coefficient : ℕ)
    (layout : magnitude lowBits sign = (lowerBits ++ [guard]) ++ integerBits)
    (close : |(TwosComplement.signed (lowBits ++ [sign]) : ℝ) /
      2 ^ (lowerBits.length + 1) - coefficient| < 1 / 2) :
    |(Counter.value integerBits : ℝ) +
      (Counter.value (lowerBits ++ [guard]) : ℝ) / 2 ^ (lowerBits.length + 1) - coefficient| < 1 / 2 := by
  have margin := magnitude_margin lowBits sign (lowerBits.length + 1) coefficient close
  rw [layout,TwosComplement.value_append] at margin
  simp only [List.length_append,List.length_cons,List.length_nil,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at margin
  have splitValue : ((Counter.value (lowerBits ++ [guard]) : ℝ) +
      2 ^ (lowerBits.length + 1) * (Counter.value integerBits : ℝ)) / 2 ^ (lowerBits.length + 1) =
      (Counter.value integerBits : ℝ) +
        (Counter.value (lowerBits ++ [guard]) : ℝ) / 2 ^ (lowerBits.length + 1) := by
    field_simp
    ring
  rw [splitValue] at margin
  exact margin

end IntegerMultBounds.Machine.RecoverMagnitude
