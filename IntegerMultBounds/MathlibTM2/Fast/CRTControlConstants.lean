module
public import IntegerMultBounds.MathlibTM2.Fast.TableVM
public import IntegerMultBounds.MathlibTM2.Fast.CRTBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.ENatToNat


/-!
# Loading permanent CRT constants into the scanner bank

Copy the target modulus and multiplier into variables 1 and 2, preserving
their permanent binary sources, the scanner's weighted value and validity,
and all temporary registers. The sources are external to the bank. Each
word takes at most `8*W+8` host steps, including clearing its old value.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Replace a word without consuming its permanent source. -/
def crtLoadPermanentWord (width tmp src dst spare : Fin T) : Pr P T Q A U :=
  .seq (uclear dst) (crtCpy width tmp src dst spare)

/-- The preserved word loader changes only the destination; both temporary
registers return empty. -/
theorem crtLoadPermanentWord_runs {width tmp src dst spare : Fin T}
    (hreg : [width, tmp, src, dst, spare].Nodup)
    (R : Regs T A) (word : List (Fin (A + 4))) (W : ℕ)
    (hw : (R width).length = W) (hword : word.length = W)
    (hsrc : R src = word) (hdst : (R dst).length = W)
    (htmp : R tmp = []) (hspare : R spare = []) :
    crtRuns body (crtLoadPermanentWord width tmp src dst spare) R
      (Function.update R dst word) (8 * W + 8) := by
  have hreg' := hreg
  regs_ne hreg'
  have h₁ := crtClear_runs (body := body) dst R
  let R₁ := Function.update R dst []
  have hwidth : (R₁ width).length = W := by simp [R₁, ‹width ≠ dst›, hw]
  have hsource : R₁ src = word := by simp [R₁, ‹src ≠ dst›, hsrc]
  have h₂ := crtCpy_runs (body := body) hreg R₁
    (by simp [R₁, ‹tmp ≠ dst›, htmp])
    (by simp [R₁, Ne.symm ‹dst ≠ spare›, hspare])
    (by rw [hwidth, hsource, hword])
  have hout : (R₁ src).take (R₁ width).length ++ R₁ dst = word := by
    rw [hsource, hwidth, ← hword]
    simp [R₁]
  rw [hout, hwidth] at h₂
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ h₂) ?_) ?_
  · simp [R₁]
  · rw [hdst]; omega

/-- State after loading target modulus and multiplier, with every other
variable and the accumulator preserved. -/
def crtControlConstantsState (S μ : ℕ) (st : TblSt 10 A) : TblSt 10 A :=
  ⟨Function.update (Function.update st.val 1 S) 2 μ, st.acc⟩

/-- Only the two binary destinations are replaced in the whole register file. -/
def crtControlConstantsRegs (rg : TblR 10 → Fin T) (W S μ : ℕ) (R : Regs T A) : Regs T A :=
  Function.update (Function.update R (rg (.v 1)) (binSyms W S)) (rg (.v 2)) (binSyms W μ)

/-- The resulting concrete registers represent the target constants without
altering the scanner's weighted value or validity. -/
theorem crtControlConstantsRegs_bank {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (W S μ : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    ∀ r, crtControlConstantsRegs rg W S μ R (rg r) =
      tblRho W wl nl (crtControlConstantsState S μ st) r := by
  intro r
  cases r with
  | v j =>
    simp [crtControlConstantsRegs, Function.update_apply, hrg.eq_iff, hR,
      crtControlConstantsState, tblRho]
    split_ifs <;> rfl
  | wr => simp [crtControlConstantsRegs, hrg.eq_iff, hR, tblRho]
  | wn => simp [crtControlConstantsRegs, hrg.eq_iff, hR, tblRho]
  | acc => simp [crtControlConstantsRegs, hrg.eq_iff, hR, crtControlConstantsState, tblRho]
  | z j => simp [crtControlConstantsRegs, hrg.eq_iff, hR, tblRho]

/-- Runtime loading of two permanent words into the scanner's bank. -/
def crtControlConstants (rg : TblR 10 → Fin T) (modulus multiplier : Fin T) : Pr P T Q A U :=
  .seq (crtLoadPermanentWord (rg .wr) (rg (.z 0)) modulus (rg (.v 1)) (rg (.z 1)))
    (crtLoadPermanentWord (rg .wr) (rg (.z 0)) multiplier (rg (.v 2)) (rg (.z 1)))

/-- Actual host contract for installing both constants from external binary
registers. Both sources remain unchanged; no arithmetic on their values is
performed, so there is no additional numerical fitting hypothesis. -/
theorem crtControlConstants_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (modulus multiplier : Fin T) (hmod : ∀ r, rg r ≠ modulus)
    (hmul : ∀ r, rg r ≠ multiplier) (W S μ : ℕ)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W)
    (st : TblSt 10 A) (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl st r)
    (hS : R modulus = binSyms W S) (hμ : R multiplier = binSyms W μ) :
    crtRuns body (crtControlConstants rg modulus multiplier) R
      (crtControlConstantsRegs rg W S μ R) (16 * W + 16) := by
  have h₁ := crtLoadPermanentWord_runs (body := body)
    (width := rg .wr) (tmp := rg (.z 0)) (src := modulus) (dst := rg (.v 1))
    (spare := rg (.z 1))
    (by simp [List.nodup_cons, hrg.eq_iff, hmod, Ne.symm, eq_comm])
    R (binSyms W S) W (by simpa [hR, tblRho] using hwl) (length_binSyms _ _) hS
    (by simp [hR, tblRho]) (by simp [hR, tblRho]) (by simp [hR, tblRho])
  let R₁ := Function.update R (rg (.v 1)) (binSyms W S)
  have h₂ := crtLoadPermanentWord_runs (body := body)
    (width := rg .wr) (tmp := rg (.z 0)) (src := multiplier) (dst := rg (.v 2))
    (spare := rg (.z 1))
    (by simp [List.nodup_cons, hrg.eq_iff, hmul, Ne.symm, eq_comm])
    R₁ (binSyms W μ) W
    (by simpa [R₁, hrg.eq_iff, hR, tblRho] using hwl) (length_binSyms _ _)
    (by simp [R₁, (hmul (.v 1)).symm, hμ])
    (by simp [R₁, hrg.eq_iff, hR, tblRho])
    (by simp [R₁, hrg.eq_iff, hR, tblRho])
    (by simp [R₁, hrg.eq_iff, hR, tblRho])
  exact crtRuns_mono (crtRuns_seq h₁ h₂) (by omega)

/-- The bridge preserves the scanner's canonical address, weighted value,
validity and accumulator, and sets the two required constant variables. -/
theorem crtControlConstantsState_spec (S μ : ℕ) (st : TblSt 10 A) :
    (crtControlConstantsState S μ st).val 1 = S ∧
    (crtControlConstantsState S μ st).val 2 = μ ∧
    (∀ j, j ≠ 1 → j ≠ 2 → (crtControlConstantsState S μ st).val j = st.val j) ∧
    (crtControlConstantsState S μ st).acc = st.acc := by
  refine ⟨by simp [crtControlConstantsState], by simp [crtControlConstantsState], ?_, rfl⟩
  intro j h1 h2
  simp [crtControlConstantsState, h1, h2]

end IntegerMultBounds.MathlibTM2.Fast
