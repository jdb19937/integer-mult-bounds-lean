module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlBridge
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlFiber
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Direct offsets followed by a physical CRT fiber rotation

This fixed program computes offsets in the scanner bank, materializes them,
rotates or copies one fiber according to the preserved validity flag, and
clears both unary counters. All bank scratch is restored.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

private theorem overlay_update {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (R : Regs T A) (ρ : TblR 10 → List (Fin (A + 4))) (k : Fin T)
    (x : List (Fin (A + 4))) (hk : ∀ r, rg r ≠ k) :
    crtBankOverlay rg (Function.update R k x) ρ =
      Function.update (crtBankOverlay rg R ρ) k x := by
  funext j
  by_cases hj : ∃ r, rg r = j
  · obtain ⟨r, rfl⟩ := hj
    simp [crtBankOverlay_on hrg, hk]
  · have hj' : ∀ r, rg r ≠ j := by simpa using hj
    by_cases hkj : j = k
    · subst j; simp [crtBankOverlay_off _ _ _ _ hk]
    · simp [crtBankOverlay_off _ _ _ _ hj', hkj]

private theorem overlay_overlay {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (R : Regs T A) (ρ ρ' : TblR 10 → List (Fin (A + 4))) :
    crtBankOverlay rg (crtBankOverlay rg R ρ) ρ' = crtBankOverlay rg R ρ' := by
  funext j
  by_cases hj : ∃ r, rg r = j
  · obtain ⟨r, rfl⟩ := hj; simp [crtBankOverlay_on hrg]
  · have hj' : ∀ r, rg r ≠ j := by simpa using hj
    simp [crtBankOverlay_off _ _ _ _ hj']

/-- The offsets and physical rotation share one fixed ten-variable bank. -/
def crtControlRotate (rg : TblR 10 → Fin T) (fwd : Bool)
    (ts rb str acc : Fin T) : Pr P T Q A U :=
  .seq (crtControlOffsets rg)
    (.seq (crtControlFiberDir (rg (.v 6)) fwd (rg (.z 0)) (rg (.z 1))
      ts rb (rg (.z 2)) (rg (.z 3)) str acc (rg (.z 4)) (rg (.z 5)))
      (crtControlUnary10Clear rg))

/-- The direct-offset kernel and physical fiber execute without an assumed
intermediate run. Variables 3 and 4 receive the binary low/high offsets; every
other binary variable and all scratch registers are preserved. -/
theorem crtControlRotate_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (ts rb str acc : Fin T) (hext : [ts, rb, str, acc].Nodup)
    (hts : ∀ r, rg r ≠ ts) (hrb : ∀ r, rg r ≠ rb)
    (hstr : ∀ r, rg r ≠ str) (hacc : ∀ r, rg r ≠ acc)
    {W w : ℕ} (hW : 0 < W) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (hS : 0 < st.val 1) (hprod : st.val 2 * st.val 5 < 2 ^ W)
    (valid fwd : Bool) (hvalid : st.val 6 = if valid then 1 else 0)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r)
    (sl : List (List (Fin (A + 4)))) (hsl : ∀ x ∈ sl, x.length = (R rb).length)
    (hlen : sl.length = st.val 1 + (R ts).length)
    (rest : List (Fin (A + 4))) (hsource : R str = sl.flatten ++ rest) :
    ∃ st' : TblSt 10 A,
      st'.val 3 = st.val 2 * st.val 5 % st.val 1 ∧
      st'.val 4 = st.val 1 - st.val 2 * st.val 5 % st.val 1 ∧
      (∀ j, j ≠ 3 → j ≠ 4 → st'.val j = st.val j) ∧ st'.acc = st.acc ∧
      crtRuns body (crtControlRotate rg fwd ts rb str acc) R
        (Function.update (Function.update (crtBankOverlay rg R (tblRho W wl nl st')) str rest)
          acc ((if valid then (sl.take (st.val 1)).rotate
            (crtControlShift fwd (st.val 1) (st.val 2) (st.val 5)) ++ sl.drop (st.val 1)
            else sl).flatten.reverse ++ R acc))
        (3 * tblC W w + W * (4 * st.val 1 + 22) + 4 * st.val 1 +
          sl.length * (8 * (R rb).length + 9) + 34) := by
  obtain ⟨st', hlo, hhi, hpres, hstateacc, hoff⟩ :=
    crtControlOffsets_runs (body := body) hrg wl nl hwl hnl hw st hst hS hprod R hR
  refine ⟨st', hlo, hhi, hpres, hstateacc, ?_⟩
  let R₁ := crtBankOverlay rg R (crtControlUnary10Rho W wl nl st')
  have hon : ∀ r, R₁ (rg r) = crtControlUnary10Rho W wl nl st' r := by
    intro r; exact crtBankOverlay_on hrg _ _ _
  have hts' : R₁ ts = R ts := crtBankOverlay_off _ _ _ _ hts
  have hrb' : R₁ rb = R rb := crtBankOverlay_off _ _ _ _ hrb
  have hstr' : R₁ str = R str := crtBankOverlay_off _ _ _ _ hstr
  have hacc' : R₁ acc = R acc := crtBankOverlay_off _ _ _ _ hacc
  have hregs : [rg (.v 6), rg (.z 0), rg (.z 1), ts, rb, rg (.z 2), rg (.z 3), str,
      acc, rg (.z 4), rg (.z 5)].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hext
    simp [List.nodup_cons, hrg.eq_iff, hts, hrb, hstr, hacc, hext, Ne.symm]
  have hfiber := crtControlFiber_shift_runs (body := body) hregs R₁ W hW valid fwd
    (by simp [hon, crtControlUnary10Rho, hpres 6 (by decide) (by decide), hvalid])
    (by simp [hon, crtControlUnary10Rho]) (by simp [hon, crtControlUnary10Rho])
    (by simp [hon, crtControlUnary10Rho]) (by simp [hon, crtControlUnary10Rho])
    (st.val 1) (st.val 2) (st.val 5) hS
    (by simp [hon, crtControlUnary10Rho, hlo]) (by simp [hon, crtControlUnary10Rho, hhi])
    sl (by simpa only [hrb'] using hsl) (by simpa only [hts'] using hlen)
    rest (by simpa only [hstr'] using hsource)
  let out := (if valid then (sl.take (st.val 1)).rotate
    (crtControlShift fwd (st.val 1) (st.val 2) (st.val 5)) ++ sl.drop (st.val 1)
    else sl).flatten
  let R₂ := Function.update (Function.update R₁ str rest) acc (out.reverse ++ R acc)
  have hfiber' : crtRuns body
      (crtControlFiberDir (rg (.v 6)) fwd (rg (.z 0)) (rg (.z 1))
        ts rb (rg (.z 2)) (rg (.z 3)) str acc (rg (.z 4)) (rg (.z 5))) R₁ R₂
      (sl.length * (8 * (R rb).length + 9) + 18) := by
    simpa only [hrb', hacc'] using hfiber
  have hR₂ : ∀ r, R₂ (rg r) = crtControlUnary10Rho W wl nl st' r := by
    intro r
    simp only [R₂, Function.update_of_ne (hstr r), Function.update_of_ne (hacc r), hon]
  have hclear := crtRuns_of_tbl hrg
    (crtControlUnary10Clear_runs (body := body) hrg W wl nl st') R₂ hR₂
  have hsum : st'.val 3 + st'.val 4 = st.val 1 := by
    rw [hlo, hhi]
    exact Nat.add_sub_of_le (Nat.mod_lt _ hS).le
  rw [hsum] at hclear
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq hoff (crtRuns_seq hfiber' hclear)) ?_) (by omega)
  dsimp only [R₂, R₁]
  rw [overlay_update hrg _ _ acc _ hacc, overlay_update hrg _ _ str _ hstr,
    overlay_overlay hrg]

/-- A power-of-two envelope for offsets, physical movement, and cleanup.
The unary conversion is linear in the target modulus times word width. -/
theorem crtControlRotate_cost_le (W w S n k : ℕ) (hw : w ≤ W) :
    3 * tblC W w + W * (4 * S + 22) + 4 * S + n * (8 * k + 9) + 34 ≤
      2 ^ 9 * ((W + 4) ^ 2 + (W + 1) * S + n * (k + 1) + 1) := by
  unfold tblC
  nlinarith

end IntegerMultBounds.MathlibTM2.Fast
