module

public import IntegerMultBounds.Machine.UnitPhaseCoreReset
public import IntegerMultBounds.Machine.ButterflySigned

/-! Exact complex conjugation for the chirp pipeline on two native marked
radix-two fields. One fixed program preserves both sources, produces two
width-exact fields and erases every private source copy. The signed proof
excludes only the unrepresentable negation of the most negative imaginary
word; the real field needs no extra guard. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpConjugateNumerator
noncomputable section
open RadixLinearCombinationRefresh (Expr controls)
open RawLinearCombinationCleanup (clean empty_append)
open ButterflySigned (signedValue signed_bounds signed_cast signed_unique complexValue)

def expression (field : Fin 2) : Expr 2 := .term field (if field = 0 then 1 else -1)

def numerator {R : Type*} [Ring R] (values : Fin 2 → R) (field : Fin 2) : R :=
  if field = 0 then values 0 else -values 1

def words (field : Fin 2) (sources : ℕ → List (Fin 2)) :=
  RadixLinearCombination.result (expression field).erase sources

def input (sources : ℕ → List (Fin 2)) : Tapes 6 2 := UnitPhaseNumerator.coreInput sources

def output (sources : ℕ → List (Fin 2)) : Tapes 6 2 :=
  (controls sources).append ((clean (expression 0) (words 0 sources)).append (clean (expression 1) (words 1 sources)))

def program := SharedControlPair.program
  (RawLinearCombination.program (q := 2) (expression 0))
  (RawLinearCombination.program (q := 2) (expression 1))

theorem expression_cost (field : Fin 2) (width : ℕ) :
    RawLinearCombination.cost (expression field) width = 6*width+21 := by
  simp [RawLinearCombination.cost,expression,RadixLinearCombinationBootstrap.initCost,
    RawLinearCombination.refreshCost,RadixLinearCombinationRefresh.Expr.erase,
    RadixLinearCombination.runtime,RawLinearCombinationCleanup.cost]
  omega

/-- Both outputs are physically computed by the same fixed native program.
No conjugated word or arithmetic execution certificate is supplied. -/
theorem runs (sources : ℕ → List (Fin 2)) (width : ℕ)
    (fieldWidths : ∀ field,(sources field).length=width) :
    HoareTime program (· = input sources) (· = output sources) (12*width+43) := by
  have realRun := RawLinearCombination.runs (expression 0) sources width fieldWidths
  have imaginaryRun := RawLinearCombination.runs (expression 1) sources width fieldWidths
  have combined := SharedControlPair.runs _ _ (controls sources) _ _ _ _ realRun imaginaryRun
  simp only [empty_append,expression_cost] at combined
  exact combined.consequence (fun _ ready => ready) (fun _ finished => finished) (by omega)

theorem words_length (field : Fin 2) (sources : ℕ → List (Fin 2)) (width : ℕ)
    (fieldWidths : ∀ index,(sources index).length=width) : (words field sources).length=width :=
  RawLinearCombination.result_length (expression field) sources width fieldWidths

private theorem valid (field : Fin 2) : RadixLinearCombination.Valid (q := 2) (expression field).erase := by
  fin_cases field <;> norm_num [expression,RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.Valid]

theorem words_value (field : Fin 2) (sources : ℕ → List (Fin 2)) (width : ℕ)
    (fieldWidths : ∀ index,(sources index).length=width) :
    (RadixDigits.value (words field sources) : ZMod (2^width)) =
      numerator (fun index : Fin 2 => (RadixDigits.value (sources index.val) : ZMod (2^width))) field := by
  rw [words,RawLinearCombination.result_value _ (valid field) sources width fieldWidths]
  fin_cases field <;> simp [expression,numerator,RadixLinearCombinationRefresh.Expr.erase,
    RadixLinearCombination.valueMod,Swap.Modular.ratMod]

/-- Decode the actual computed words as signed integers. Only the imaginary
minimum is excluded; the real field's full centered interval is retained. -/
theorem words_signed (field : Fin 2) (sources : ℕ → List (Fin 2)) (widthPred : ℕ)
    (fieldWidths : ∀ index,(sources index).length=widthPred+1)
    (imaginaryNotMinimum : signedValue widthPred (sources 1) ≠ -(2^widthPred : ℕ)) :
    signedValue widthPred (words field sources) =
      numerator (fun index : Fin 2 => signedValue widthPred (sources index.val)) field := by
  apply signed_unique widthPred _ (words_length field sources (widthPred+1) fieldWidths)
    (numerator (fun index : Fin 2 => signedValue widthPred (sources index.val)) field)
  · fin_cases field
    · exact signed_bounds widthPred (sources 0) (fieldWidths 0)
    · have imaginaryBounds := signed_bounds widthPred (sources 1) (fieldWidths 1)
      change -(2^widthPred : ℕ) ≤ -signedValue widthPred (sources 1) ∧
        -signedValue widthPred (sources 1) < (2^widthPred : ℕ)
      constructor <;> omega
  · rw [words_value field sources (widthPred+1) fieldWidths]
    fin_cases field <;> simp [numerator,signed_cast]

theorem complex_conjugate (real imaginary : ℤ) (precision : ℕ) :
    complexValue real (-imaginary) precision = (starRingEnd ℂ) (complexValue real imaginary precision) := by
  have twoFixed : (starRingEnd ℂ) (2 : ℂ)=2 := by
    change (starRingEnd ℂ) ((2 : ℝ) : ℂ)=((2 : ℝ) : ℂ)
    exact Complex.conj_ofReal _
  simp [complexValue,map_add,map_mul,map_pow,twoFixed]

/-- The literal outputs represent the conjugate Gaussian dyadic value at the
original precision, with no extra rounding error. -/
theorem words_conjugate (sources : ℕ → List (Fin 2)) (widthPred precision : ℕ)
    (fieldWidths : ∀ index,(sources index).length=widthPred+1)
    (imaginaryNotMinimum : signedValue widthPred (sources 1) ≠ -(2^widthPred : ℕ)) :
    complexValue (signedValue widthPred (words 0 sources)) (signedValue widthPred (words 1 sources)) precision =
      (starRingEnd ℂ) (complexValue (signedValue widthPred (sources 0)) (signedValue widthPred (sources 1)) precision) := by
  rw [words_signed 0 sources widthPred fieldWidths imaginaryNotMinimum,
    words_signed 1 sources widthPred fieldWidths imaginaryNotMinimum]
  exact complex_conjugate _ _ _

/-- The original two-bit word-width slack makes negation representable for
any grid numerator bounded by its precision scale. No extra exclusion of the
most negative imaginary word is needed at such a chirp call. -/
theorem imaginary_not_minimum_of_bound (digits : List (Fin 2)) (widthPred precision : ℕ)
    (precisionFits : precision+2 ≤ widthPred+1)
    (numeratorBound : |signedValue widthPred digits| ≤ (2^precision : ℕ)) :
    signedValue widthPred digits ≠ -(2^widthPred : ℕ) := by
  have scaleBound : ((2^precision : ℕ) : ℤ) < (2^widthPred : ℕ) := by
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1<2) (show precision<widthPred by omega)
  intro minimum
  rw [minimum,abs_neg,abs_of_nonneg (by positivity)] at numeratorBound
  omega

/-- After output emission, clearing the two output ports recovers exactly the
shared source bank expected by the existing physical core reset. -/
theorem emitted_core (sources : ℕ → List (Fin 2)) :
    SharedPlacementAlphabet.setTape (SharedPlacementAlphabet.setTape (output sources) 2 (fun _ => blank) 0)
      4 (fun _ => blank) 0 = input sources := by
  apply congrArg₂ Tapes.mk <;> apply List.ofFn_injective <;> rfl

end
end IntegerMultBounds.Machine.ChirpConjugateNumerator
