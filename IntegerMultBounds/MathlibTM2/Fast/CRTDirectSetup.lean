module

import IntegerMultBounds.MathlibTM2.Fast.CRTReverse
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlWorkspace
public import IntegerMultBounds.MathlibTM2.Fast.CRTDrive
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Runtime setup for the direct CRT driver from legacy inputs -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Preserve a stream while constructing its reversed copy in an empty output. -/
def crtDirectReverseCopy (src dst work t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bcopy src work t₁ t₂) (crtMv work dst)

theorem crtDirectReverseCopy_runs {src dst work t₁ t₂ : Fin T}
    (hreg : [src, dst, work, t₁, t₂].Nodup) (R : Regs T A)
    (hd : R dst = []) (hw : R work = []) (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) :
    crtRuns body (crtDirectReverseCopy src dst work t₁ t₂) R
      (Function.update R dst (R src).reverse) (8 * (R src).length + 8) := by
  have hreg' := hreg
  regs_ne hreg'
  have h₁ := crtBcopy_runs (body := body) (a := src) (c := work) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) R ht₁ ht₂
  rw [hw, List.append_nil] at h₁
  let R₁ := Function.update R work (R src)
  have h₂ := crtMv_runs (body := body) (Ne.symm ‹dst ≠ work›) R₁
  have ho : Function.update (Function.update R₁ work []) dst ((R₁ work).reverse ++ R₁ dst) =
      Function.update R dst (R src).reverse := by
    have hz : Function.update R work [] = R := by
      funext r
      by_cases h : r = work
      · subst r; simp [hw]
      · simp [h]
    simp [R₁, Function.update_idem, ‹dst ≠ work›, hd, hz]
  rw [ho] at h₂
  refine crtRuns_mono (crtRuns_seq h₁ h₂) ?_
  simp [R₁]
  omega

/-- Cache the first unary entry and put the source entry back unchanged. -/
def crtDirectCacheHead (src dst work tmp : Fin T) : Pr P T Q A U :=
  .seq (crtPopEnt src work) (.seq (ucopy work dst tmp) (crtPushEnt work src))

theorem crtDirectCacheHead_runs {src dst work tmp : Fin T}
    (hreg : [src, dst, work, tmp].Nodup) (R : Regs T A) (a : ℕ) (as : List ℕ)
    (hsrc : R src = crtEnts (a :: as)) (hd : R dst = []) (hw : R work = []) (ht : R tmp = []) :
    crtRuns body (crtDirectCacheHead src dst work tmp) R
      (Function.update R dst (List.replicate a tick)) (8 * a + 12) := by
  have hreg' := hreg
  regs_ne hreg'
  have h₁ := crtPopEnt_runs (body := body) ‹src ≠ work› R a as hsrc hw
  let R₁ := Function.update (Function.update R src (crtEnts as)) work (List.replicate a tick)
  have h₂ := crtUcopy_runs (body := body) (Ne.symm ‹dst ≠ work›) ‹work ≠ tmp› ‹dst ≠ tmp› R₁
    (by simp [R₁, Ne.symm ‹work ≠ tmp›, Ne.symm ‹src ≠ tmp›, ht])
  have h₂' : crtRuns body (ucopy work dst tmp) R₁
      (Function.update R₁ dst (List.replicate a tick)) (4 * a + 4) := by
    simpa [R₁, ‹dst ≠ work›, Ne.symm ‹src ≠ dst›, hd] using h₂
  let R₂ := Function.update R₁ dst (List.replicate a tick)
  have h₃ := crtPushEnt_runs (body := body) (Ne.symm ‹src ≠ work›) R₂ a
    (by simp [R₂, R₁, Ne.symm ‹dst ≠ work›])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂' h₃)) ?_) (by omega)
  funext r
  by_cases hs : r = src
  · subst r; simp [R₂, R₁, ‹src ≠ dst›, ‹src ≠ work›, hsrc, crtEnts_cons]
  · by_cases hd' : r = dst
    · subst r; simp [R₂, R₁, Ne.symm ‹src ≠ dst›, ‹dst ≠ work›]
    · by_cases hw' : r = work
      · subst r; simp [R₂, R₁, Ne.symm ‹src ≠ work›, Ne.symm ‹dst ≠ work›, hw]
      · simp [R₂, R₁, hs, hd', hw']

/-- Count entries by removing their unary widths from the stream length and
halving the remaining separator count. Both input tapes are preserved. -/
def crtDirectCountAxes (src total dst work tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy src work tmp) <| .seq (usub total work tmp) <|
  .seq (udiv 2 work dst tmp) (uclear work)

theorem crtDirectCountAxes_runs {src total dst work tmp : Fin T}
    (hreg : [src, total, dst, work, tmp].Nodup) (R : Regs T A)
    (hd : R dst = []) (hw : R work = []) (ht : R tmp = []) :
    crtRuns body (crtDirectCountAxes src total dst work tmp) R
      (Function.update R dst (List.replicate (((R src).length - (R total).length) / 2) tick))
      (10 * (R src).length + 4 * (R total).length + 14) := by
  have hreg' := hreg
  regs_ne hreg'
  have h₁ := crtUcopy_runs (body := body) ‹src ≠ work› ‹src ≠ tmp› ‹work ≠ tmp› R ht
  rw [hw, List.append_nil] at h₁
  let R₁ := Function.update R work (List.replicate (R src).length tick)
  have h₂ := crtUsub_runs (body := body) ‹total ≠ work› ‹total ≠ tmp› ‹work ≠ tmp› R₁
    (by simp [R₁, Ne.symm ‹work ≠ tmp›, ht])
  let n := (R src).length - (R total).length
  let R₂ := Function.update R work (List.replicate n tick)
  have h₂' : crtRuns body (usub total work tmp) R₁ R₂ (4 * (R total).length + 4) := by
    simpa [R₁, R₂, n, ‹total ≠ work›, List.drop_replicate] using h₂
  have h₃ := crtReverseHalf_runs (body := body) (Ne.symm ‹dst ≠ work›) ‹work ≠ tmp› ‹dst ≠ tmp› R₂
    (by simp [R₂, Ne.symm ‹work ≠ tmp›, ht]) (by simp [R₂, ‹dst ≠ work›, hd])
  let R₃ := Function.update R₂ dst (List.replicate (n / 2) tick)
  have h₄ := crtClear_runs (body := body) work R₃
  have ho : Function.update R₃ work [] = Function.update R dst (List.replicate (n / 2) tick) := by
    funext r
    by_cases hrw : r = work
    · subst r; simp [R₃, R₂, Ne.symm ‹dst ≠ work›, hw]
    · by_cases hrd : r = dst
      · subst r; simp [R₃, R₂, ‹dst ≠ work›]
      · simp [R₃, R₂, hrw, hrd]
  rw [ho] at h₄
  have h₃' : crtRuns body (udiv 2 work dst tmp) R₂ R₃ (4 * n + 4) := by simpa [R₂, R₃] using h₃
  refine crtRuns_mono (crtRuns_seq h₁ (crtRuns_seq h₂' (crtRuns_seq h₃' h₄))) ?_
  simp [R₃, R₂, Ne.symm ‹dst ≠ work›]
  dsimp [n]
  omega

/-- Encode three times the record length, with all unary scratch returned. -/
def crtDirectTriple (src dst work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (umul 3 src work tmp) (.seq (crtEncP work saved dst tmp) (uclear work))

def crtDirectTripleCost (c : ℕ) : ℕ := (4 * c + 4) + (3 * c * (4 * (3 * c) + 9) + 6 * c + 4) + (6 * c + 2)

theorem crtDirectTriple_runs {src dst work saved tmp : Fin T}
    (hreg : [src, dst, work, saved, tmp].Nodup) (R : Regs T A)
    (hd : R dst = []) (hw : R work = []) (hs : R saved = []) (ht : R tmp = []) :
    crtRuns body (crtDirectTriple src dst work saved tmp) R
      (Function.update R dst ((GrowingCounterData.advance (3 * (R src).length) []).map bitSymbol))
      (crtDirectTripleCost (R src).length) := by
  have hreg' := hreg
  regs_ne hreg'
  have h₁ := crtUmul_runs (body := body) 3 ‹src ≠ work› ‹src ≠ tmp› ‹work ≠ tmp› R ht
  rw [hw, List.append_nil] at h₁
  let R₁ := Function.update R work (List.replicate (3 * (R src).length) tick)
  have h₂ := crtEncP_runs (body := body) (u := work) (tu := saved) (e := dst) (t := tmp)
    (by regs_nodup) R₁
    (by simp [R₁, Ne.symm ‹work ≠ saved›, hs]) (by simp [R₁, ‹dst ≠ work›, hd])
    (by simp [R₁, Ne.symm ‹work ≠ tmp›, ht])
  let R₂ := Function.update R₁ dst ((GrowingCounterData.advance (3 * (R src).length) []).map bitSymbol)
  have h₂' : crtRuns body (crtEncP work saved dst tmp) R₁ R₂
      (3 * (R src).length * (4 * (3 * (R src).length) + 9) + 6 * (R src).length + 4) := by
    simpa [R₁, R₂, ← Nat.mul_assoc] using h₂
  have h₃ := crtClear_runs (body := body) work R₂
  have ho : Function.update R₂ work [] =
      Function.update R dst ((GrowingCounterData.advance (3 * (R src).length) []).map bitSymbol) := by
    funext r
    by_cases hrw : r = work
    · subst r; simp [R₂, R₁, Ne.symm ‹dst ≠ work›, hw]
    · by_cases hrd : r = dst
      · subst r; simp [R₂, R₁, ‹dst ≠ work›]
      · simp [R₂, R₁, hrw, hrd]
  rw [ho] at h₃
  refine crtRuns_mono (crtRuns_seq h₁ (crtRuns_seq h₂' h₃)) ?_
  simp [R₂, R₁, Ne.symm ‹dst ≠ work›, crtDirectTripleCost]
  omega

/-- Construct the generator width directly from the preserved total-width tape. -/
def crtDirectBankWidth (src dst tmp : Fin T) : Pr P T Q A U :=
  .seq (umul 3 src dst tmp) (crtPush dst tick)

theorem crtDirectBankWidth_runs {src dst tmp : Fin T}
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (R : Regs T A) (hd : R dst = []) (ht : R tmp = []) :
    crtRuns body (crtDirectBankWidth src dst tmp) R
      (Function.update R dst (List.replicate (3 * (R src).length + 1) tick)) (4 * (R src).length + 5) := by
  have h₁ := crtUmul_runs (body := body) 3 hsd hst hdt R ht
  rw [hd, List.append_nil] at h₁
  have h₂ := crtPush_runs (body := body) dst tick
    (Function.update R dst (List.replicate (3 * (R src).length) tick))
  simpa [crtDirectBankWidth, List.replicate_succ] using crtRuns_seq h₁ h₂

/-- Setup uses only runtime tape operations. The legacy width/modulus streams,
total-width bit tape, record tape, data, and CRT constants remain unchanged. -/
def crtDirectSetup (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T) : Pr P T Q A U :=
  .seq (crtDirectReverseCopy (e 31) (e 1) (e 19) (e 20) (e 21)) <|
  .seq (crtDirectReverseCopy (e 32) (e 2) (e 19) (e 20) (e 21)) <|
  .seq (crtDirectCacheHead (e 1) (e 5) (e 19) (e 20)) <|
  .seq (crtDirectCountAxes (e 31) (e 8) (e 39) (e 19) (e 20)) <|
  .seq (crtDirectTriple (e 11) (e 12) (e 19) (e 20) (e 21))
    (crtDirectBankWidth (e 8) (rg .wr) (e 19))

def crtDirectSetupCost (widthsLen moduliLen a0 L c : ℕ) : ℕ :=
  18 * widthsLen + 8 * moduliLen + 8 * a0 + 8 * L + crtDirectTripleCost c + 47

def crtDirectSetupRegs (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (R : Regs T A) (a0 : ℕ) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update R (e 1) (R (e 31)).reverse) (e 2) (R (e 32)).reverse)
    (e 5) (List.replicate a0 tick)) (e 39)
    (List.replicate (((R (e 31)).length - (R (e 8)).length) / 2) tick))
    (e 12) ((GrowingCounterData.advance (3 * (R (e 11)).length) []).map bitSymbol))
    (rg .wr) (List.replicate (3 * (R (e 8)).length + 1) tick)

/-- Exact setup from the preserved legacy tapes, with no setup contract supplied
by the caller. The arithmetic bank count register remains unchanged (empty). -/
theorem crtDirectSetup_runs (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (he : Function.Injective e) (hwr : ∀ j, rg .wr ≠ e j)
    (R : Regs T A) (a0 : ℕ) (as : List ℕ)
    (hhead : (R (e 31)).reverse = crtEnts (a0 :: as))
    (hz : ∀ j ∈ ([1, 2, 5, 12, 19, 20, 21, 39] : List (Fin 40)), R (e j) = [])
    (hbank : R (rg .wr) = []) :
    crtRuns body (crtDirectSetup rg e) R (crtDirectSetupRegs rg e R a0)
      (crtDirectSetupCost (R (e 31)).length (R (e 32)).length a0 (R (e 8)).length (R (e 11)).length) := by
  have hn : ∀ j k : Fin 40, j ≠ k → e j ≠ e k := fun _ _ h => he.ne h
  have h₁ := crtDirectReverseCopy_runs (body := body) (src := e 31) (dst := e 1)
    (work := e 19) (t₁ := e 20) (t₂ := e 21) (by simp [he.eq_iff]) R
    (hz 1 (by simp)) (hz 19 (by simp)) (hz 20 (by simp)) (hz 21 (by simp))
  let R₁ := Function.update R (e 1) (R (e 31)).reverse
  have h₂ := crtDirectReverseCopy_runs (body := body) (src := e 32) (dst := e 2)
    (work := e 19) (t₁ := e 20) (t₂ := e 21) (by simp [he.eq_iff]) R₁
    (by simp [R₁, he.eq_iff, hz 2 (by simp)]) (by simp [R₁, he.eq_iff, hz 19 (by simp)])
    (by simp [R₁, he.eq_iff, hz 20 (by simp)]) (by simp [R₁, he.eq_iff, hz 21 (by simp)])
  let R₂ := Function.update R₁ (e 2) (R (e 32)).reverse
  have h₂' : crtRuns body (crtDirectReverseCopy (e 32) (e 2) (e 19) (e 20) (e 21)) R₁ R₂
      (8 * (R (e 32)).length + 8) := by simpa [R₁, R₂, he.eq_iff] using h₂
  have h₃ := crtDirectCacheHead_runs (body := body) (src := e 1) (dst := e 5)
    (work := e 19) (tmp := e 20) (by simp [he.eq_iff]) R₂ a0 as
    (by simp [R₂, R₁, he.eq_iff, hhead]) (by simp [R₂, R₁, he.eq_iff, hz 5 (by simp)])
    (by simp [R₂, R₁, he.eq_iff, hz 19 (by simp)]) (by simp [R₂, R₁, he.eq_iff, hz 20 (by simp)])
  let R₃ := Function.update R₂ (e 5) (List.replicate a0 tick)
  have h₄ := crtDirectCountAxes_runs (body := body) (src := e 31) (total := e 8)
    (dst := e 39) (work := e 19) (tmp := e 20) (by simp [he.eq_iff]) R₃
    (by simp [R₃, R₂, R₁, he.eq_iff, hz 39 (by simp)])
    (by simp [R₃, R₂, R₁, he.eq_iff, hz 19 (by simp)])
    (by simp [R₃, R₂, R₁, he.eq_iff, hz 20 (by simp)])
  let R₄ := Function.update R₃ (e 39)
    (List.replicate (((R (e 31)).length - (R (e 8)).length) / 2) tick)
  have h₄' : crtRuns body (crtDirectCountAxes (e 31) (e 8) (e 39) (e 19) (e 20)) R₃ R₄
      (10 * (R (e 31)).length + 4 * (R (e 8)).length + 14) := by
    simpa [R₄, R₃, R₂, R₁, he.eq_iff] using h₄
  have h₅ := crtDirectTriple_runs (body := body) (src := e 11) (dst := e 12)
    (work := e 19) (saved := e 20) (tmp := e 21) (by simp [he.eq_iff]) R₄
    (by simp [R₄, R₃, R₂, R₁, he.eq_iff, hz 12 (by simp)])
    (by simp [R₄, R₃, R₂, R₁, he.eq_iff, hz 19 (by simp)])
    (by simp [R₄, R₃, R₂, R₁, he.eq_iff, hz 20 (by simp)])
    (by simp [R₄, R₃, R₂, R₁, he.eq_iff, hz 21 (by simp)])
  let R₅ := Function.update R₄ (e 12)
    ((GrowingCounterData.advance (3 * (R (e 11)).length) []).map bitSymbol)
  have h₅' : crtRuns body (crtDirectTriple (e 11) (e 12) (e 19) (e 20) (e 21)) R₄ R₅
      (crtDirectTripleCost (R (e 11)).length) := by
    simpa [R₅, R₄, R₃, R₂, R₁, he.eq_iff] using h₅
  have h₆ := crtDirectBankWidth_runs (body := body) (src := e 8) (dst := rg .wr) (tmp := e 19)
    (hwr 8).symm (he.ne (by decide)) (hwr 19) R₅
    (by simp [R₅, R₄, R₃, R₂, R₁, hwr, hbank])
    (by simp [R₅, R₄, R₃, R₂, R₁, he.eq_iff, hz 19 (by simp)])
  have h₆' : crtRuns body (crtDirectBankWidth (e 8) (rg .wr) (e 19)) R₅
      (crtDirectSetupRegs rg e R a0) (4 * (R (e 8)).length + 5) := by
    simpa [crtDirectSetupRegs, R₅, R₄, R₃, R₂, R₁, he.eq_iff] using h₆
  refine crtRuns_mono (crtRuns_seq h₁ (crtRuns_seq h₂' (crtRuns_seq h₃
    (crtRuns_seq h₄' (crtRuns_seq h₅' h₆'))))) ?_
  unfold crtDirectSetupCost
  omega

theorem crtDirectEntriesLength (as : List ℕ) :
    (crtEnts (A := A) as).length = as.sum + 2 * as.length := by
  induction as with
  | nil => simp
  | cons a as ih => simp [crtEnts_cons, crtEnt, ih]; omega

/-- Reversing the legacy descending stream gives the required ascending copy. -/
theorem crtDirectReverseEntries {d : ℕ} (a : Fin d → ℕ) :
    (crtEnts (A := A) ((crtRevAx d).map a)).reverse = crtEnts (List.ofFn a) := by
  rw [crtEnts_reverse, ← List.map_reverse, crtRevAx_reverse]
  rw [List.take_of_length_le (by simp : (List.finRange d).length ≤ d)]
  rw [List.ofFn_eq_map]

/-- Mathematical description of the six values constructed from runtime inputs. -/
def crtDirectSetupResult {d : ℕ} (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (R : Regs T A) (a s : Fin (d + 1) → ℕ) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update R (e 1) (crtEnts (List.ofFn a))) (e 2) (crtEnts (List.ofFn s)))
    (e 5) (List.replicate (a 0) tick)) (e 39) (List.replicate (d + 1) tick))
    (e 12) ((GrowingCounterData.advance (3 * (R (e 11)).length) []).map bitSymbol))
    (rg .wr) (List.replicate (3 * crtPre a (d + 1) + 1) tick)

/-- The axis count is decoded from two separators per width entry, without
assuming a precomputed dimension tape. -/
theorem crtDirectSetupRegs_eq {d : ℕ} (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (R : Regs T A) (a s : Fin (d + 1) → ℕ)
    (hw : R (e 31) = crtEnts ((crtRevAx (d + 1)).map a))
    (hs : R (e 32) = crtEnts ((crtRevAx (d + 1)).map s))
    (htotal : (R (e 8)).length = crtPre a (d + 1)) :
    crtDirectSetupRegs rg e R (a 0) = crtDirectSetupResult rg e R a s := by
  have hlen : (R (e 31)).length = crtPre a (d + 1) + 2 * (d + 1) := by
    rw [hw, crtDirectEntriesLength]
    change crtW a (crtRevAx (d + 1)) + 2 * (((crtRevAx (d + 1)).map a).length) = _
    rw [crtW_revAx a (d + 1) le_rfl]
    simp [crtRevAx]
  simp only [crtDirectSetupRegs, hw, hs, crtDirectReverseEntries, htotal, crtDirectSetupResult]
  have hdim : ((crtEnts (A := A) ((crtRevAx (d + 1)).map a)).length - crtPre a (d + 1)) / 2 = d + 1 := by
    rw [← hw, hlen]
    omega
  rw [hdim]

/-- Specialized runtime setup contract for the existing descending CRT inputs. -/
theorem crtDirectSetup_legacy_runs {d : ℕ} (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (he : Function.Injective e) (hwr : ∀ j, rg .wr ≠ e j)
    (R : Regs T A) (a s : Fin (d + 1) → ℕ)
    (hw : R (e 31) = crtEnts ((crtRevAx (d + 1)).map a))
    (hs : R (e 32) = crtEnts ((crtRevAx (d + 1)).map s))
    (htotal : (R (e 8)).length = crtPre a (d + 1))
    (hz : ∀ j ∈ ([1, 2, 5, 12, 19, 20, 21, 39] : List (Fin 40)), R (e j) = [])
    (hbank : R (rg .wr) = []) :
    crtRuns body (crtDirectSetup rg e) R (crtDirectSetupResult rg e R a s)
      (crtDirectSetupCost (R (e 31)).length (R (e 32)).length (a 0)
        (crtPre a (d + 1)) (R (e 11)).length) := by
  have hhead : (R (e 31)).reverse = crtEnts (a 0 :: List.ofFn (fun j : Fin d => a j.succ)) := by
    rw [hw, crtDirectReverseEntries]
    simp [List.ofFn_succ]
  have h := crtDirectSetup_runs (body := body) rg e he hwr R (a 0) _ hhead hz hbank
  rw [crtDirectSetupRegs_eq rg e R a s hw hs htotal, htotal] at h
  exact h

/-- Every register outside the six setup outputs is preserved exactly. -/
theorem crtDirectSetupResult_off {d : ℕ} (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (R : Regs T A) (a s : Fin (d + 1) → ℕ) (r : Fin T)
    (h1 : r ≠ e 1) (h2 : r ≠ e 2) (h5 : r ≠ e 5) (h39 : r ≠ e 39)
    (h12 : r ≠ e 12) (hwr : r ≠ rg .wr) :
    crtDirectSetupResult rg e R a s r = R r := by
  simp only [crtDirectSetupResult, Function.update_of_ne hwr, Function.update_of_ne h12,
    Function.update_of_ne h39, Function.update_of_ne h5, Function.update_of_ne h2, Function.update_of_ne h1]

/-- Release exactly the six values constructed by direct setup. -/
def crtDirectSetupClear (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T) : Pr P T Q A U :=
  crtWorkspaceClear [e 1, e 2, e 5, e 12, e 39, rg .wr]

def crtDirectSetupClearBound {d : ℕ} (a s : Fin (d + 1) → ℕ) (c : ℕ) : ℕ :=
  ((List.ofFn a).sum + 2 * (d + 1)) + ((List.ofFn s).sum + 2 * (d + 1)) +
    a 0 + (GrowingCounterData.advance (3 * c) []).length + (d + 1) + (3 * crtPre a (d + 1) + 1)

def crtDirectSetupClearCost {d : ℕ} (a s : Fin (d + 1) → ℕ) (c : ℕ) : ℕ :=
  6 * (2 * crtDirectSetupClearBound a s c + 2) + 1

/-- Explicit cleanup restores the entire original legacy register file after
a direct driver whose only persistent change is its data output. -/
theorem crtDirectSetupClear_runs {d : ℕ} (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (he : Function.Injective e) (hwr : ∀ j, rg .wr ≠ e j)
    (R : Regs T A) (a s : Fin (d + 1) → ℕ)
    (hz : ∀ j ∈ ([1, 2, 5, 12, 39] : List (Fin 40)), R (e j) = []) (hbank : R (rg .wr) = []) :
    crtRuns body (crtDirectSetupClear rg e) (crtDirectSetupResult rg e R a s) R
      (crtDirectSetupClearCost a s (R (e 11)).length) := by
  let S := crtDirectSetupResult rg e R a s
  let M := crtDirectSetupClearBound a s (R (e 11)).length
  have hlen : ∀ r ∈ [e 1, e 2, e 5, e 12, e 39, rg .wr], (S r).length ≤ M := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [S, crtDirectSetupResult, he.eq_iff, fun j => (hwr j).symm,
      M, crtDirectSetupClearBound, crtDirectEntriesLength]
    all_goals omega
  have h := crtWorkspaceClear_runs (body := body) M [e 1, e 2, e 5, e 12, e 39, rg .wr] S hlen
  apply crtRuns_congr (show crtRuns body (crtDirectSetupClear rg e) S _
    (crtDirectSetupClearCost a s (R (e 11)).length) from h)
  funext r
  by_cases hr : r ∈ [e 1, e 2, e 5, e 12, e 39, rg .wr]
  · simp only [ite_eq_left hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hz 1 (by simp)).symm
    · exact (hz 2 (by simp)).symm
    · exact (hz 5 (by simp)).symm
    · exact (hz 12 (by simp)).symm
    · exact (hz 39 (by simp)).symm
    · exact hbank.symm
  · simp only [ite_eq_right hr]
    have hn : r ≠ e 1 ∧ r ≠ e 2 ∧ r ≠ e 5 ∧ r ≠ e 12 ∧ r ≠ e 39 ∧ r ≠ rg .wr := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hr
    exact crtDirectSetupResult_off rg e R a s r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.2.1 hn.2.2.2.1 hn.2.2.2.2.2

end IntegerMultBounds.MathlibTM2.Fast
