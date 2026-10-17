module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlConstants
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlBank
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.ReduceModChar
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

/-! # Resetting the live CRT control bank between fibers

The address word is loaded separately. Reset all remaining arithmetic variables
and start with a valid flag; this discards the previous fiber's control sum and
offsets while preserving the accumulator and every external tape.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

def crtControlReset : TblCode 10 :=
  tblBlock 10 [.zero 1, .zero 2, .zero 3, .zero 4, .zero 5,
    .zero 6, .zero 7, .zero 8, .zero 9] (.inc 6)

/-- Ten interpreter atoms establish the canonical state for the next fiber. -/
theorem crtControlReset_do {A W w : ℕ} (hW : 0 < W) (st : TblSt 10 A) :
    TblDo A W w crtControlReset st
      (fun t => t = crtControlState (st.val 0) 0 true st.acc) 10 := by
  have hone : 1 < (2 : ℕ) ^ W := by
    have h : (2 : ℕ)^1 ≤ 2^W := Nat.pow_le_pow_right (by decide) hW
    simp only [pow_one] at h
    omega
  unfold crtControlReset
  apply TblDo.block [.zero 1, .zero 2, .zero 3, .zero 4, .zero 5,
    .zero 6, .zero 7, .zero 8, .zero 9] (.inc 6)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hone]
  · simp only [List.cons_append, List.nil_append, tblExactList, TblIns.exact]
    congr 1
    funext j
    fin_cases j <;> simp

/-- Resetting preserves the binary address and all non-bank registers. -/
theorem crtControlReset_runs {T Q A W w : ℕ} {U P : Type}
    {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (hW : 0 < W) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    crtRuns body (tblCompile rg crtControlReset) R
      (crtBankOverlay rg R (tblRho W wl nl (crtControlState (st.val 0) 0 true st.acc)))
      (10 * tblC W w) := by
  obtain ⟨st', hst', hr⟩ := (crtControlReset_do hW st).host
    (body := body) hrg wl nl hwl hnl hw hst
  subst st'
  exact crtRuns_of_tbl hrg hr R hR

/-- Load the outer loop's permanent address, then reset the per-fiber state. -/
def crtControlBegin {T Q A : ℕ} {U P : Type} (rg : TblR 10 → Fin T)
    (index : Fin T) : Pr P T Q A U :=
  .seq (crtLoadPermanentWord (rg .wr) (rg (.z 0)) index (rg (.v 0)) (rg (.z 1)))
    (tblCompile rg crtControlReset)

/-- The indexed loop's address becomes the scanner input without consuming it.
All state left by the preceding fiber is reset before the next scan. -/
theorem crtControlBegin_runs {T Q A W w : ℕ} {U P : Type}
    {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (index : Fin T) (hindex : ∀ r, rg r ≠ index)
    (hW : 0 < W) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (F : ℕ) (hF : F < 2 ^ W) (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl st r)
    (haddr : R index = binSyms W F) :
    crtRuns body (crtControlBegin rg index) R
      (crtBankOverlay rg R (tblRho W wl nl (crtControlState F 0 true st.acc)))
      (8 * W + 8 + 10 * tblC W w) := by
  let st₁ : TblSt 10 A := ⟨Function.update st.val 0 F, st.acc⟩
  let R₁ := Function.update R (rg (.v 0)) (binSyms W F)
  have hload := crtLoadPermanentWord_runs (body := body)
    (width := rg .wr) (tmp := rg (.z 0)) (src := index)
    (dst := rg (.v 0)) (spare := rg (.z 1))
    (by simp [List.nodup_cons, hrg.eq_iff, hindex, Ne.symm, eq_comm])
    R (binSyms W F) W (by simpa [hR, tblRho] using hwl) (length_binSyms _ _) haddr
    (by simp [hR, tblRho]) (by simp [hR, tblRho]) (by simp [hR, tblRho])
  have hR₁ : ∀ r, R₁ (rg r) = tblRho W wl nl st₁ r := by
    intro r
    cases r with
    | v j => simp [R₁, st₁, hrg.eq_iff, hR, tblRho, Function.update_apply]; split_ifs <;> rfl
    | wr => simp [R₁, hrg.eq_iff, hR, tblRho]
    | wn => simp [R₁, hrg.eq_iff, hR, tblRho]
    | acc => simp [R₁, st₁, hrg.eq_iff, hR, tblRho]
    | z j => simp [R₁, hrg.eq_iff, hR, tblRho]
  have hst₁ : ∀ j, st₁.val j < 2 ^ W := by
    intro j
    by_cases hj : j = 0 <;> simp [st₁, hj, hF, hst]
  have hreset := crtControlReset_runs (body := body) hrg hW wl nl hwl hnl hw st₁ hst₁ R₁ hR₁
  refine crtRuns_congr (crtRuns_seq hload hreset) ?_
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    simp [crtBankOverlay_on hrg, st₁]
  · have hk' : ∀ r, rg r ≠ k := by simpa using hk
    simp [crtBankOverlay_off _ _ _ _ hk', R₁, Ne.symm (hk' (.v 0))]

end IntegerMultBounds.MathlibTM2.Fast
