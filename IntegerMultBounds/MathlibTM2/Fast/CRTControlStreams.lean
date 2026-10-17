module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDrive
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Preserved reversed copies of runtime parameter streams
The existing driver stores descending unary entries. Descriptor generation
uses ascending copies, constructed once without changing the original streams.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def crtControlReverseCopy (src dst copy tmp saved : Fin T) : Pr P T Q A U :=
  .seq (bcopy src copy tmp saved) (crtMv copy dst)

theorem crtControlReverseCopy_runs {src dst copy tmp saved : Fin T}
    (hreg : [src, dst, copy, tmp, saved].Nodup) (R : Regs T A)
    (hdst : R dst = []) (hcopy : R copy = []) (htmp : R tmp = []) (hsaved : R saved = []) :
    crtRuns body (crtControlReverseCopy src dst copy tmp saved) R
      (Function.update R dst (R src).reverse) (8 * (R src).length + 8) := by
  have hreg' := hreg
  regs_ne hreg'
  have hc := crtBcopy_runs (body := body) (a := src) (c := copy) (t₁ := tmp) (t₂ := saved)
    (by regs_nodup) R htmp hsaved
  rw [hcopy, List.append_nil] at hc
  let R₁ := Function.update R copy (R src)
  have hm := crtMv_runs (body := body) (Ne.symm ‹dst ≠ copy›) R₁
  have hc0 : Function.update R copy [] = R := by
    funext k
    by_cases hk : k = copy
    · subst k; simp [hcopy]
    · simp [hk]
  have hout : Function.update (Function.update R₁ copy []) dst
      ((R₁ copy).reverse ++ R₁ dst) = Function.update R dst (R src).reverse := by
    simp [R₁, ‹dst ≠ copy›, hdst, hc0]
  apply crtRuns_mono (crtRuns_congr (crtRuns_seq hc hm) hout)
  simp [R₁]
  omega

/-- In particular, reverse-copying a descending entry stream supplies the
ascending descriptor-generator input and preserves the descending original. -/
theorem crtControlAscendingEntries_runs {src dst copy tmp saved : Fin T}
    (hreg : [src, dst, copy, tmp, saved].Nodup) (R : Regs T A) (xs : List ℕ)
    (hsrc : R src = crtEnts xs.reverse)
    (hdst : R dst = []) (hcopy : R copy = []) (htmp : R tmp = []) (hsaved : R saved = []) :
    crtRuns body (crtControlReverseCopy src dst copy tmp saved) R
      (Function.update R dst (crtEnts xs)) (8 * (crtEnts (A := A) xs).length + 8) := by
  have h := crtControlReverseCopy_runs (body := body) hreg R hdst hcopy htmp hsaved
  rw [hsrc, crtEnts_reverse, List.reverse_reverse] at h
  simpa only [← crtEnts_reverse, List.length_reverse] using h

end IntegerMultBounds.MathlibTM2.Fast
