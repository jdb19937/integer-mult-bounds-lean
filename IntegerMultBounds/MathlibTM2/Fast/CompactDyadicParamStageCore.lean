module

public import IntegerMultBounds.MathlibTM2.Fast.CompactDyadicDimension
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith
public import IntegerMultBounds.MathlibTM2.Mult.CRT

/-! Independent forty-variable dyadic dimension stage, importable by ParamProg. -/
@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Mult.Sizes

variable {A W w : ℕ}

def compactDyadicParamReg : Fin 7 → Fin 40 := ![1, 31, 3, 32, 33, 34, 35]

def compactDyadicParamClear : TblCode 40 :=
  tblBlock 40 [.zero 31, .zero 32, .zero 33, .zero 34] (.zero 35)

def compactDyadicParamStage : TblCode 40 :=
  compactDyadicDimensionC.rename compactDyadicParamReg ;; compactDyadicParamClear

/-- The dimension changes, borrowed scratch becomes zero, and every other value is retained. -/
def compactDyadicParamVals (v : Fin 40 → ℕ) (b : ℕ) (i : Fin 40) : ℕ :=
  if i = 3 then iroot 64 (b ^ 31) else if 31 ≤ i.val ∧ i.val ≤ 35 then 0 else v i

def compactDyadicParamAtoms (b : ℕ) : ℕ := 67 + 44 * iroot 64 (b ^ 31)

/-- Generic-word contract, including the entire forty-variable state and accumulator. -/
theorem compactDyadicParamStage_do (s : TblSt 40 A) {b : ℕ}
    (hb : s.val 1 = b) (hW : (b ^ 31 + 1) ^ 2 < 2 ^ W) (hkW : 8 < 2 ^ W) :
    TblDo A W w compactDyadicParamStage s
      (fun z => z.val = compactDyadicParamVals s.val b ∧ z.acc = s.acc)
      (compactDyadicParamAtoms b) := by
  have hdim := (compactDyadicDimensionC_do (W := W) (w := w)
    (s.restrict compactDyadicParamReg)
    (by simpa [TblSt.restrict, compactDyadicParamReg] using hb) hW hkW).rename
      (f := compactDyadicParamReg) (by decide)
  refine (hdim.seq (K₂ := 5) (fun z hz => ?_)).mono (fun _ h => h) ?_
  · have h1 : z.val 1 = b := by simpa [TblSt.restrict, compactDyadicParamReg] using hz.1.1
    have h3 : z.val 3 = iroot 64 (b ^ 31) := by
      simpa [TblSt.restrict, compactDyadicParamReg] using hz.1.2.2.1
    have hoff : ∀ i : Fin 40, i ≠ 1 → i ≠ 3 → i ≠ 31 → i ≠ 32 →
        i ≠ 33 → i ≠ 34 → i ≠ 35 → z.val i = s.val i := by
      intro i hi1 hi3 hi31 hi32 hi33 hi34 hi35
      apply hz.2 i
      intro j
      fin_cases j <;> simp_all [compactDyadicParamReg, ne_comm]
    refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ⟨funext fun i => ?_, ?_⟩
    · fin_cases i <;> simp [tblExactList, TblIns.exact, compactDyadicParamVals,
        h1, h3, hoff, hb]
    · simpa [tblExactList, TblIns.exact] using hz.1.2.2.2
  · simp [compactDyadicDimensionAtoms, compactDyadicParamAtoms]
    omega

/-- The cleaned stage fits the previous conservative dimension-stage atom allowance. -/
theorem compactDyadicParamAtoms_le (b : ℕ) :
    compactDyadicParamAtoms b ≤ 7 * 30 + 11 + iroot 64 (b ^ 31) * (6 * 30 + 8) := by
  unfold compactDyadicParamAtoms
  omega

end IntegerMultBounds.MathlibTM2.Fast.TableVM
