module

public import IntegerMultBounds.Machine.BinaryDescriptorIncrement
public import IntegerMultBounds.Machine.FamilyPlacementAlphabet
public import IntegerMultBounds.Machine.Branch
public import IntegerMultBounds.Machine.TwosComplement
public import Mathlib.Algebra.Order.Round

/-! The section 8 coefficient-rounding boundary. A fixed machine reads the
half-unit bit on a separate fractional tape and conditionally increments the
unsigned integer descriptor. All fractional cells and both heads are preserved;
carry overflow grows the integer word. Splitting a signed computed coefficient
into this layout, and iterating over the coefficient array, remain upstream. -/

@[expose] public section

namespace IntegerMultBounds.Machine.RecoverCoefficientRound
variable {alphabet : ℕ}

def roundedBits (guard : Bool) (integerBits : List Bool) : List Bool :=
  if guard then GrowingCounterData.increment integerBits else integerBits

def fractionBank (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ) : Tapes 1 alphabet :=
  ⟨fun _ => guardHead,fun _ => fractionTape⟩

def bank (integerBits : List Bool) (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ) :=
  (BinaryDescriptorIncrement.bank integerBits).append (fractionBank fractionTape guardHead)

def test (symbols : Fin 2 → Fin (alphabet+4)) : Bool :=
  decide (symbols 1 = bitSymbol true)

def skip : Program 2 1 alphabet where
  tapes_pos := by decide
  start := 0
  transition := fun _ _ => none

/-- Five states, two tapes, and no coefficient-width-dependent control. -/
def program : Program 2 5 alphabet :=
  branch test (extend BinaryDescriptorIncrement.program 1) skip

def cost (guard : Bool) (integerBits : List Bool) : ℕ :=
  (if guard then 2 * GrowingCounterData.carrySteps integerBits else 0) + 1

theorem test_bank (guard : Bool) (integerBits : List Bool)
    (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ)
    (guardRead : fractionTape guardHead = bitSymbol guard) :
    test (bank integerBits fractionTape guardHead).reads = guard := by
  change decide (fractionTape guardHead = bitSymbol true) = guard
  rw [guardRead]
  cases guard <;> simp [bitSymbol,Fin.ext_iff]

private theorem skip_hoare (initial : Tapes 2 alphabet) :
    HoareTime skip (· = initial) (· = initial) 0 := by
  intro current equal
  subst current
  exact ⟨0,Tapes.start initial skip,le_rfl,rfl,rfl,rfl⟩

/-- The branch bit is actually read, and all increment scans and the branch
transition are charged. No bound or canonicality is required of the integer. -/
theorem runs_round (guard : Bool) (integerBits : List Bool)
    (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ)
    (guardRead : fractionTape guardHead = bitSymbol guard) :
    HoareTime program (· = bank integerBits fractionTape guardHead)
      (· = bank (roundedBits guard integerBits) fractionTape guardHead)
      (cost guard integerBits) := by
  have readTest := test_bank guard integerBits fractionTape guardHead guardRead
  cases guard with
  | false =>
    have impossible : HoareTime (extend BinaryDescriptorIncrement.program 1)
        (fun current => current = bank integerBits fractionTape guardHead ∧ test current.reads = true)
        (· = bank integerBits fractionTape guardHead) 0 := by
      rintro _ ⟨rfl,wrongTest⟩
      rw [readTest] at wrongTest
      contradiction
    have unchanged := (skip_hoare (bank integerBits fractionTape guardHead)).consequence
      (pre' := fun current => current = bank integerBits fractionTape guardHead ∧ test current.reads = false)
      (fun _ hypothesis => hypothesis.1) (fun _ hypothesis => hypothesis) le_rfl
    simpa only [program,roundedBits,cost,Bool.false_eq_true,ite_false,Nat.max_self]
      using branch_hoare test impossible unchanged
  | true =>
    have incremented := FamilyPlacementAlphabet.extend_hoare
      (BinaryDescriptorIncrement.increment_hoare integerBits) (fractionBank fractionTape guardHead)
    have selected := incremented.consequence
      (pre' := fun current => current = bank integerBits fractionTape guardHead ∧ test current.reads = true)
      (fun _ hypothesis => hypothesis.1) (fun _ hypothesis => hypothesis) le_rfl
    have impossible : HoareTime skip
        (fun current => current = bank integerBits fractionTape guardHead ∧ test current.reads = false)
        (· = bank (GrowingCounterData.increment integerBits) fractionTape guardHead) 0 := by
      rintro _ ⟨rfl,wrongTest⟩
      rw [readTest] at wrongTest
      contradiction
    simpa only [program,roundedBits,cost,ite_true,Nat.max_zero,bank]
      using branch_hoare test selected impossible

theorem cost_linear (guard : Bool) (integerBits : List Bool) :
    cost guard integerBits ≤ 2 * integerBits.length + 3 := by
  have scans := (GrowingCounterData.carrySteps_bounds integerBits).2
  cases guard <;> simp only [cost,ite_true,Bool.false_eq_true,ite_false] <;> omega

theorem rounded_value (guard : Bool) (integerBits : List Bool) :
    Counter.value (roundedBits guard integerBits) =
      Counter.value integerBits + (if guard then 1 else 0) := by
  cases guard <;> simp [roundedBits,GrowingCounterData.increment_value]

/-- For a nonnegative fixed-point coefficient, the guard comparison implements
Lean's rounding convention, including the half-unit tie. -/
theorem rounded_eq_round (guard : Bool) (integerBits : List Bool) (fraction : ℝ)
    (fractionNonnegative : 0 ≤ fraction) (fractionBelowOne : fraction < 1)
    (guardCorrect : guard = true ↔ 1 / 2 ≤ fraction) :
    (Counter.value (roundedBits guard integerBits) : ℤ) =
      round ((Counter.value integerBits : ℝ) + fraction) := by
  symm
  apply round_eq_iff.mpr
  rw [rounded_value]
  cases guard with
  | false =>
    have belowHalf : fraction < 1 / 2 := by simp only [Bool.false_eq_true,false_iff] at guardCorrect; linarith
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero,Int.cast_natCast]
    constructor <;> linarith
  | true =>
    have aboveHalf : 1 / 2 ≤ fraction := guardCorrect.mp rfl
    simp only [ite_true,Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_one,Int.cast_natCast]
    constructor <;> linarith

/-- The same executed machine recovers a natural coefficient whenever the
represented approximation is strictly less than half a unit from it. -/
theorem runs_recover_coefficient (guard : Bool) (integerBits : List Bool)
    (fractionTape : ℤ → Fin (alphabet+4)) (guardHead : ℤ)
    (guardRead : fractionTape guardHead = bitSymbol guard)
    (fraction : ℝ) (fractionNonnegative : 0 ≤ fraction) (fractionBelowOne : fraction < 1)
    (guardCorrect : guard = true ↔ 1 / 2 ≤ fraction) (coefficient : ℕ)
    (approximationClose : |(Counter.value integerBits : ℝ) + fraction - coefficient| < 1 / 2) :
    HoareTime program (· = bank integerBits fractionTape guardHead)
      (fun finalBank => ∃ recoveredBits, Counter.value recoveredBits = coefficient ∧
        finalBank = bank recoveredBits fractionTape guardHead)
      (2 * integerBits.length + 3) := by
  have exactRound : round ((Counter.value integerBits : ℝ) + fraction) = (coefficient : ℤ) := by
    apply round_eq_iff.mpr
    obtain ⟨lowerError,upperError⟩ := abs_lt.mp approximationClose
    simp only [Int.cast_natCast]
    constructor <;> linarith
  have recoveredValue : Counter.value (roundedBits guard integerBits) = coefficient := by
    exact_mod_cast (rounded_eq_round guard integerBits fraction fractionNonnegative
      fractionBelowOne guardCorrect).trans exactRound
  exact (runs_round guard integerBits fractionTape guardHead guardRead).consequence
    (fun _ hypothesis => hypothesis)
    (fun _ hypothesis => ⟨roundedBits guard integerBits,recoveredValue,hypothesis⟩)
    (cost_linear guard integerBits)

/-- The lower fractional bits contribute less than half a unit; the next
bit is the half-unit guard. Bits are stored least significant first. -/
noncomputable def fractionOf (lowerBits : List Bool) (guard : Bool) : ℝ :=
  (Counter.value lowerBits : ℝ) / (2 ^ lowerBits.length * 2) +
    (if guard then 1 / 2 else 0)

theorem fractionOf_spec (lowerBits : List Bool) (guard : Bool) :
    0 ≤ fractionOf lowerBits guard ∧ fractionOf lowerBits guard < 1 ∧
      (guard = true ↔ 1 / 2 ≤ fractionOf lowerBits guard) := by
  have denominatorPositive : (0 : ℝ) < 2 ^ lowerBits.length * 2 := by positivity
  have lowerNonnegative : (0 : ℝ) ≤ (Counter.value lowerBits : ℝ) / (2 ^ lowerBits.length * 2) := by positivity
  have lowerBound : (Counter.value lowerBits : ℝ) < 2 ^ lowerBits.length := by
    exact_mod_cast Counter.value_lt lowerBits
  have lowerBelowHalf : (Counter.value lowerBits : ℝ) / (2 ^ lowerBits.length * 2) < 1 / 2 := by
    apply (div_lt_iff₀ denominatorPositive).mpr
    nlinarith
  cases guard <;> simp only [fractionOf,Bool.false_eq_true,ite_false,ite_true,add_zero,true_iff,false_iff]
  · exact ⟨lowerNonnegative,by linarith,by linarith⟩
  · exact ⟨by linarith,by linarith,by linarith⟩

/-- This fractional semantics is the actual binary word divided by its
fixed-point scale, rather than an independently supplied rounding flag. -/
theorem fractionOf_value (lowerBits : List Bool) (guard : Bool) :
    fractionOf lowerBits guard =
      (Counter.value (lowerBits ++ [guard]) : ℝ) / 2 ^ (lowerBits.length + 1) := by
  rw [TwosComplement.value_append]
  cases guard <;> simp only [fractionOf,Counter.value,Bool.false_eq_true,ite_false,
    ite_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.cast_add,Nat.cast_pow,
    Nat.cast_ofNat,pow_succ]
  all_goals field_simp <;> ring

theorem fractional_guard_read (lowerBits : List Bool) (guard : Bool) :
    BinaryDescriptorStack.descriptor (a := alphabet) (lowerBits ++ [guard])
      (1 + lowerBits.length) = bitSymbol guard := by
  unfold BinaryDescriptorStack.descriptor
  rw [List.map_append,← putWord_append_forward,List.length_map]
  exact putWord_head _ _ _ _

/-- Rounding an encoded unsigned fixed-point coefficient, with no independent
guard-correctness assumption. The head is already positioned at the half-unit
bit; this program does not discover the precision or split signed records. -/
theorem runs_recover_fixedpoint (integerBits lowerBits : List Bool) (guard : Bool)
    (coefficient : ℕ)
    (approximationClose : |(Counter.value integerBits : ℝ) +
      (Counter.value (lowerBits ++ [guard]) : ℝ) / 2 ^ (lowerBits.length + 1) - coefficient| < 1 / 2) :
    HoareTime (program (alphabet := alphabet))
      (· = bank integerBits (BinaryDescriptorStack.descriptor (lowerBits ++ [guard])) (1 + lowerBits.length))
      (fun finalBank => ∃ recoveredBits, Counter.value recoveredBits = coefficient ∧
        finalBank = bank recoveredBits (BinaryDescriptorStack.descriptor (lowerBits ++ [guard])) (1 + lowerBits.length))
      (2 * integerBits.length + 3) := by
  obtain ⟨fractionNonnegative,fractionBelowOne,guardCorrect⟩ := fractionOf_spec lowerBits guard
  apply runs_recover_coefficient guard integerBits _ _ (fractional_guard_read lowerBits guard)
    (fractionOf lowerBits guard) fractionNonnegative fractionBelowOne guardCorrect coefficient
  simpa only [fractionOf_value] using approximationClose

end IntegerMultBounds.Machine.RecoverCoefficientRound
