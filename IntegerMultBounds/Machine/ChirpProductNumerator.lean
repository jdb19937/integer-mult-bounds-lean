module

public import IntegerMultBounds.Machine.ChirpConjugateNumerator

/-! Exact numerator addition after the four full chirp scalar products.
The input order is real-real, imaginary-imaginary, real-imaginary,
imaginary-real. Rounding is deliberately deferred until after these sums. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpProductNumerator
noncomputable section
open RadixLinearCombinationRefresh (Expr controls)
open RawLinearCombinationCleanup (clean empty_append)
open ButterflySigned (signedValue signed_bounds signed_cast signed_unique)

def expression (field : Fin 2) : Expr 4 :=
  if field=0 then .add (.term 0 1) (.term 1 (-1))
  else .add (.term 2 1) (.term 3 1)

def numerator {R : Type*} [Ring R] (products : Fin 4 → R) (field : Fin 2) : R :=
  if field=0 then products 0-products 1 else products 2+products 3

def words (field : Fin 2) (sources : ℕ → List (Fin 2)) :=
  RadixLinearCombination.result (expression field).erase sources

def input (sources : ℕ → List (Fin 2)) : Tapes 14 2 :=
  (controls sources).append (RadixLinearCombinationBootstrap.empty 10)

def output (sources : ℕ → List (Fin 2)) : Tapes 14 2 :=
  (controls sources).append ((clean (expression 0) (words 0 sources)).append (clean (expression 1) (words 1 sources)))

def program := SharedControlPair.program
  (RawLinearCombination.program (q := 2) (expression 0))
  (RawLinearCombination.program (q := 2) (expression 1))

theorem expression_cost (field : Fin 2) (width : ℕ) :
    RawLinearCombination.cost (expression field) width=18*width+63 := by
  fin_cases field <;>
    simp [RawLinearCombination.cost,expression,RadixLinearCombinationBootstrap.initCost,
      RawLinearCombination.refreshCost,RadixLinearCombinationRefresh.Expr.erase,
      RadixLinearCombination.runtime,RawLinearCombinationCleanup.cost] <;> omega

/-- Literal sums with retained sources and erased private source copies. -/
theorem runs (sources : ℕ → List (Fin 2)) (width : ℕ)
    (fieldWidths : ∀ index,(sources index).length=width) :
    HoareTime program (· = input sources) (· = output sources) (36*width+127) := by
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
    (RadixDigits.value (words field sources) : ZMod (2^width))=
      numerator (fun index : Fin 4 => (RadixDigits.value (sources index.val) : ZMod (2^width))) field := by
  rw [words,RawLinearCombination.result_value _ (valid field) sources width fieldWidths]
  fin_cases field <;> simp [expression,numerator,RadixLinearCombinationRefresh.Expr.erase,
    RadixLinearCombination.valueMod,Swap.Modular.ratMod,sub_eq_add_neg]

theorem numerator_bound (products : Fin 4 → ℤ) (bound : ℤ)
    (productBounds : ∀ index,|products index|≤bound) (field : Fin 2) :
    |numerator products field|≤2*bound := by
  have realReal := abs_le.mp (productBounds 0)
  have imaginaryImaginary := abs_le.mp (productBounds 1)
  have realImaginary := abs_le.mp (productBounds 2)
  have imaginaryReal := abs_le.mp (productBounds 3)
  fin_cases field <;> simp only [numerator,abs_le] <;> constructor <;> omega

/-- Centered guards give exact integer sums, rather than modular sums. -/
theorem words_signed (field : Fin 2) (sources : ℕ → List (Fin 2)) (widthPred : ℕ)
    (fieldWidths : ∀ index,(sources index).length=widthPred+1)
    (productBound : ℤ) (productBounds : ∀ index : Fin 4,|signedValue widthPred (sources index.val)|≤productBound)
    (sumFits : 2*productBound<(2^widthPred : ℕ)) :
    signedValue widthPred (words field sources)=
      numerator (fun index : Fin 4 => signedValue widthPred (sources index.val)) field := by
  apply signed_unique widthPred _ (words_length field sources (widthPred+1) fieldWidths)
    (numerator (fun index : Fin 4 => signedValue widthPred (sources index.val)) field)
  · have bounds := abs_le.mp (numerator_bound _ productBound productBounds field)
    constructor <;> omega
  · rw [words_value field sources (widthPred+1) fieldWidths]
    fin_cases field <;> simp [numerator,signed_cast]

/-- The same width slack used by widened chirp products discharges the
sum guard from the original scalar-product scale. -/
theorem words_signed_of_scale (field : Fin 2) (sources : ℕ → List (Fin 2)) (widthPred productScale : ℕ)
    (fieldWidths : ∀ index,(sources index).length=widthPred+1)
    (wideEnough : productScale+2≤widthPred)
    (productBounds : ∀ index : Fin 4,|signedValue widthPred (sources index.val)|≤(2 : ℤ)^productScale) :
    signedValue widthPred (words field sources)=
      numerator (fun index : Fin 4 => signedValue widthPred (sources index.val)) field := by
  apply words_signed field sources widthPred fieldWidths ((2 : ℤ)^productScale) productBounds
  have threshold : (2 : ℤ)^(productScale+1)<2^widthPred :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  simpa only [pow_succ,mul_comm,Nat.cast_pow,Nat.cast_ofNat] using threshold

end
end IntegerMultBounds.Machine.ChirpProductNumerator
