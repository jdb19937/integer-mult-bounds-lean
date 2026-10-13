module

public import IntegerMultBounds.Machine.SharedControlPair
public import IntegerMultBounds.Machine.ButterflySigned
public import IntegerMultBounds.Machine.NativeHadamardNormalizationFactor

/-! A fixed physical numerator kernel for native Hadamard normalization.
Both source controls are preserved, all private copies are erased, and two
width-exact output words remain. No loop proportional to the native visit width
is needed: one sum/difference and a denominator increase give the exact factor.
The stream traversal and physical denominator update are separate obligations. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationNumerator
noncomputable section
open RadixLinearCombinationRefresh (Expr controls)
open ButterflySigned (signedValue signed_cast signed_unique complexValue)
open NativeHadamardNormalizationFactor (denominatorIncrease)
open CompactComplexRecursiveGeometry (arity)

def expression (coordinate : Fin 2) : Expr 2 :=
  if coordinate=0 then .add (.term 0 1) (.term 1 1)
  else .add (.term 1 1) (.term 0 (-1))

def numerator {R : Type*} [Ring R] (values : Fin 2 → R) : Fin 2 → R :=
  ![values 0+values 1,values 1-values 0]

def words (coordinate : Fin 2) (sourceWords : ℕ → List (Fin 2)) :=
  RadixLinearCombination.result (expression coordinate).erase sourceWords

def privateOutput (coordinate : Fin 2) (sourceWords : ℕ → List (Fin 2)) :=
  RawLinearCombinationCleanup.clean (expression coordinate) (words coordinate sourceWords)

def input (sourceWords : ℕ → List (Fin 2)) : Tapes 12 2 :=
  (controls sourceWords).append (RadixLinearCombinationBootstrap.empty 10)

def output (sourceWords : ℕ → List (Fin 2)) : Tapes 12 2 :=
  (controls sourceWords).append ((privateOutput 0 sourceWords).append (privateOutput 1 sourceWords))

def program := SharedControlPair.program
  (RawLinearCombination.program (q:=2) (expression 0))
  (RawLinearCombination.program (q:=2) (expression 1))

theorem expression_cost (coordinate : Fin 2) (wordWidth : ℕ) :
    RawLinearCombination.cost (expression coordinate) wordWidth=18*wordWidth+63 := by
  fin_cases coordinate <;>
    simp [RawLinearCombination.cost,expression,RadixLinearCombinationBootstrap.initCost,
      RawLinearCombination.refreshCost,RadixLinearCombinationRefresh.Expr.erase,
      RadixLinearCombination.runtime,RawLinearCombinationCleanup.cost] <;> omega

/-- One fixed twelve-tape program computes both numerator words and reclaims
all private source copies. Its cost depends only on the represented word width. -/
theorem runs (sourceWords : ℕ → List (Fin 2)) (wordWidth : ℕ)
    (sourceWidths : ∀ index,(sourceWords index).length=wordWidth) :
    HoareTime program (fun bank => bank=input sourceWords) (fun bank => bank=output sourceWords)
      (36*wordWidth+127) := by
  have realRun := RawLinearCombination.runs (expression 0) sourceWords wordWidth sourceWidths
  have imaginaryRun := RawLinearCombination.runs (expression 1) sourceWords wordWidth sourceWidths
  have pairRun := SharedControlPair.runs _ _ (controls sourceWords) _ _ _ _ realRun imaginaryRun
  simp only [RawLinearCombinationCleanup.empty_append,expression_cost] at pairRun
  exact pairRun.consequence (fun _ equality => equality) (fun _ equality => equality) (by omega)

theorem words_length (coordinate : Fin 2) (sourceWords : ℕ → List (Fin 2)) (wordWidth : ℕ)
    (sourceWidths : ∀ index,(sourceWords index).length=wordWidth) :
    (words coordinate sourceWords).length=wordWidth :=
  RawLinearCombination.result_length _ _ _ sourceWidths

theorem valid (coordinate : Fin 2) : RadixLinearCombination.Valid (q:=2) (expression coordinate).erase := by
  fin_cases coordinate <;>
    norm_num [expression,RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.Valid]

theorem words_value (coordinate : Fin 2) (sourceWords : ℕ → List (Fin 2)) (wordWidth : ℕ)
    (sourceWidths : ∀ index,(sourceWords index).length=wordWidth) :
    (RadixDigits.value (words coordinate sourceWords) : ZMod (2^wordWidth))=
      numerator (fun index => (RadixDigits.value (sourceWords index.val) : ZMod (2^wordWidth))) coordinate := by
  rw [words,RawLinearCombination.result_value _ (valid coordinate) sourceWords wordWidth sourceWidths]
  fin_cases coordinate <;>
    simp [expression,numerator,RadixLinearCombinationRefresh.Expr.erase,
      RadixLinearCombination.valueMod,Swap.Modular.ratMod,sub_eq_add_neg]

theorem numerator_bound (values : Fin 2 → ℤ) (bound : ℤ)
    (sourceBounds : ∀ coordinate,|values coordinate|≤bound) (coordinate : Fin 2) :
    |numerator values coordinate|≤2*bound := by
  have realBound := abs_le.mp (sourceBounds 0)
  have imaginaryBound := abs_le.mp (sourceBounds 1)
  fin_cases coordinate <;> simp [numerator,abs_le] <;> constructor <;> omega

theorem words_signed (coordinate : Fin 2) (sourceWords : ℕ → List (Fin 2)) (halfWidth : ℕ)
    (sourceWidths : ∀ index,(sourceWords index).length=halfWidth+1)
    (values : Fin 2 → ℤ)
    (sourceResidues : ∀ index,(RadixDigits.value (sourceWords index.val) : ZMod (2^(halfWidth+1)))=
      (values index : ZMod (2^(halfWidth+1))))
    (bound : ℤ) (sourceBounds : ∀ index,|values index|≤bound)
    (signedGuard : 2*bound<(2^halfWidth : ℕ)) :
    signedValue halfWidth (words coordinate sourceWords)=numerator values coordinate := by
  apply signed_unique halfWidth _ (words_length coordinate sourceWords (halfWidth+1) sourceWidths) _
  · have resultBound := abs_le.mp (numerator_bound values bound sourceBounds coordinate)
    constructor <;> omega
  · rw [words_value coordinate sourceWords (halfWidth+1) sourceWidths]
    have residues := funext sourceResidues
    rw [residues]
    fin_cases coordinate <;> simp [numerator]

theorem complex_normalization (values : Fin 2 → ℤ) (denominator exponent : ℕ) :
    complexValue (numerator values 0) (numerator values 1)
        (denominator+denominatorIncrease (arity^exponent))=
      Networks.GaussianHadamardBridge.normalization^(arity^exponent)*
        complexValue (values 0) (values 1) denominator := by
  rw [NativeHadamardNormalizationFactor.native_normalization]
  simp only [complexValue,numerator,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Int.cast_add,Int.cast_sub,pow_add]
  field_simp
  linear_combination (values 1 : ℂ)*Complex.I_sq

/-- The actual arithmetic output has exact native normalization semantics with
no execution/correctness premise. Denominator advancement is a readout here;
installing the stream and updating the live denominator remain separate. -/
theorem runs_exact (sourceWords : ℕ → List (Fin 2)) (halfWidth denominator exponent : ℕ)
    (sourceWidths : ∀ index,(sourceWords index).length=halfWidth+1) (bound : ℤ)
    (sourceBounds : ∀ index : Fin 2,|signedValue halfWidth (sourceWords index.val)|≤bound)
    (signedGuard : 2*bound<(2^halfWidth : ℕ)) :
    HoareTime program (fun bank => bank=input sourceWords)
      (fun bank => bank=output sourceWords ∧
        complexValue (signedValue halfWidth (words 0 sourceWords))
          (signedValue halfWidth (words 1 sourceWords))
          (denominator+denominatorIncrease (arity^exponent))=
        Networks.GaussianHadamardBridge.normalization^(arity^exponent)*
          complexValue (signedValue halfWidth (sourceWords 0))
            (signedValue halfWidth (sourceWords 1)) denominator)
      (36*(halfWidth+1)+127) := by
  have resultSigned (coordinate : Fin 2) := words_signed coordinate sourceWords halfWidth sourceWidths
    (fun index => signedValue halfWidth (sourceWords index.val))
    (fun index => (signed_cast halfWidth (sourceWords index.val)).symm) bound sourceBounds signedGuard
  apply (runs sourceWords (halfWidth+1) sourceWidths).consequence (fun _ equality => equality) _ le_rfl
  intro bank equality
  refine ⟨equality,?_⟩
  rw [resultSigned 0,resultSigned 1]
  exact complex_normalization _ denominator exponent

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationNumerator
