module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlProg

/-!
# Validity-controlled physical CRT fibers

The scanner's binary validity flag is read without popping it. Valid fibers
rotate their modulus prefix by the materialized unary offset; invalid fibers
are copied. Both branches consume the complete fiber, prepend the reversed
output to the accumulator, and restore every other register.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Read the low binary bit without modifying the register. -/
def crtControlPeekBit (flag : Fin T) : Act T Q A U :=
  .peek (.rt flag) (fun v o => { v with flag := symBit (o.getD blank) }) .done

lemma crtControlPeekBit_run (flag : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (crtControlPeekBit flag : Act T Q A U).run (mk v S) =
      mk { v with flag := symBit ((S.R flag).head?.getD blank) } S := rfl

/-- Positive-width Boolean numerals carry their value in the first symbol. -/
lemma crtControlFlag_head (W : ℕ) (hW : 0 < W) (valid : Bool) :
    symBit ((binSyms (A := A) W (if valid then 1 else 0)).head?.getD blank) = valid := by
  cases W with
  | zero => omega
  | succ W => cases valid <;> simp [binSyms_succ]

/-- One fixed conditional fiber program. `cA` holds the rotation length and
`cB` its complement; selecting their directional roles needs no runtime loop. -/
def crtControlFiber (flag cA cB ts rb tc tr str acc tA tB : Fin T) : Pr P T Q A U :=
  .seq (.act (crtControlPeekBit flag))
    (.cond (·.flag) (crtRotFib cA cB ts rb tc tr str acc tA tB)
      (crtCopyFib cA cB ts rb tc tr str acc))

/-- Semantic output, including unrotated padding and invalid-control fibers. -/
def crtControlFiberOut {α : Type*} (valid : Bool) (sl : List (List α)) (a b : ℕ) : List α :=
  (if valid then (sl.take (a + b)).rotate a ++ sl.drop (a + b) else sl).flatten

/-- Complete physical execution, preserving the flag, unary counters, and
scratch registers. The only changes are consuming the source fiber and adding
the reversed output to the existing accumulator. -/
theorem crtControlFiber_runs {flag cA cB ts rb tc tr str acc tA tB : Fin T}
    (hreg : [flag, cA, cB, ts, rb, tc, tr, str, acc, tA, tB].Nodup)
    (R : Regs T A) (W : ℕ) (hW : 0 < W) (valid : Bool)
    (hflag : R flag = binSyms W (if valid then 1 else 0))
    (htc : R tc = []) (htr : R tr = []) (htA : R tA = []) (htB : R tB = [])
    (sl : List (List (Fin (A + 4)))) (hsl : ∀ x ∈ sl, x.length = (R rb).length)
    (hlen : sl.length = (R cA).length + (R cB).length + (R ts).length)
    (rest : List (Fin (A + 4))) (hstr : R str = sl.flatten ++ rest) :
    crtRuns body (crtControlFiber flag cA cB ts rb tc tr str acc tA tB) R
      (Function.update (Function.update R str rest) acc
        ((crtControlFiberOut valid sl (R cA).length (R cB).length).reverse ++ R acc))
      (sl.length * (8 * (R rb).length + 9) + 18) := by
  have hreg' := hreg
  regs_ne hreg'
  have hbit : symBit ((R flag).head?.getD blank) = valid := by
    rw [hflag]; exact crtControlFlag_head W hW valid
  intro v S hS hL
  have hpeek := Exec.act (body := body) (crtControlPeekBit flag) (mk v S)
  rw [crtControlPeekBit_run] at hpeek
  cases valid with
  | false =>
    have hc := crtCopyFib_runs (body := body) (cA := cA) (cB := cB) (ts := ts)
      (rb := rb) (tc := tc) (tr := tr) (str := str) (acc := acc)
      (by regs_nodup) R htc htr sl hsl hlen rest hstr
    obtain ⟨v', m, hu, hm, he⟩ := hc
      { v with flag := symBit ((S.R flag).head?.getD blank) } S hS hL
    refine ⟨v', 1 + (m + 1), hu, ?_, ?_⟩
    · nlinarith
    · simpa only [crtControlFiber, crtControlFiberOut, Bool.false_eq_true,
        ↓reduceIte] using Exec.seq hpeek (Exec.cond_false (by simpa [hS] using hbit) he)
  | true =>
    have hr := crtRotFib_runs (body := body) (cA := cA) (cB := cB) (ts := ts)
      (rb := rb) (tc := tc) (tr := tr) (str := str) (acc := acc) (tA := tA) (tB := tB)
      (by regs_nodup) R htc htr htA htB sl hsl hlen rest hstr
    obtain ⟨v', m, hu, hm, he⟩ := hr
      { v with flag := symBit ((S.R flag).head?.getD blank) } S hS hL
    refine ⟨v', 1 + (m + 1), hu, by omega, ?_⟩
    simpa only [crtControlFiber, crtControlFiberOut, ↓reduceIte] using
      Exec.seq hpeek (Exec.cond_true (by simpa [hS] using hbit) he)

/-- The direction is a fixed program parameter: forward rotation uses the
complement of the low offset, inverse rotation uses the low offset. -/
def crtControlFiberDir (flag : Fin T) (fwd : Bool)
    (lo hi ts rb tc tr str acc tA tB : Fin T) : Pr P T Q A U :=
  crtControlFiber flag (if fwd then hi else lo) (if fwd then lo else hi)
    ts rb tc tr str acc tA tB

/-- Materialized modular offset lengths give precisely the direct CRT shift
in either direction; padding and invalid-control fibers are copied unchanged. -/
theorem crtControlFiber_shift_runs {flag lo hi ts rb tc tr str acc tA tB : Fin T}
    (hreg : [flag, lo, hi, ts, rb, tc, tr, str, acc, tA, tB].Nodup)
    (R : Regs T A) (W : ℕ) (hW : 0 < W) (valid fwd : Bool)
    (hflag : R flag = binSyms W (if valid then 1 else 0))
    (htc : R tc = []) (htr : R tr = []) (htA : R tA = []) (htB : R tB = [])
    (S μ K : ℕ) (hS : 0 < S)
    (hlo : (R lo).length = (μ * K) % S) (hhi : (R hi).length = S - (μ * K) % S)
    (sl : List (List (Fin (A + 4)))) (hsl : ∀ x ∈ sl, x.length = (R rb).length)
    (hlen : sl.length = S + (R ts).length)
    (rest : List (Fin (A + 4))) (hstr : R str = sl.flatten ++ rest) :
    crtRuns body (crtControlFiberDir flag fwd lo hi ts rb tc tr str acc tA tB) R
      (Function.update (Function.update R str rest) acc
        ((if valid then (sl.take S).rotate (crtControlShift fwd S μ K) ++ sl.drop S
          else sl).flatten.reverse ++ R acc))
      (sl.length * (8 * (R rb).length + 9) + 18) := by
  have hswap : [flag, lo, hi, ts, rb, tc, tr, str, acc, tA, tB].Perm
      [flag, hi, lo, ts, rb, tc, tr, str, acc, tA, tB] :=
    List.Perm.cons _ (List.Perm.swap _ _ _)
  have hmod := Nat.mod_lt (μ * K) hS
  have hc : (R lo).length + (R hi).length = S := by omega
  have hc' : (R hi).length + (R lo).length = S := by omega
  cases fwd with
  | false =>
    have h := crtControlFiber_runs (body := body) (flag := flag) (cA := lo) (cB := hi)
      (ts := ts) (rb := rb) (tc := tc) (tr := tr) (str := str) (acc := acc)
      (tA := tA) (tB := tB) hreg R W hW valid hflag htc htr htA htB sl hsl
      (by rw [hc]; exact hlen) rest hstr
    simp only [crtControlFiberOut] at h
    rw [hc] at h
    simpa only [crtControlFiberDir, crtControlShift,
      Bool.false_eq_true, ↓reduceIte, hlo] using h
  | true =>
    have h := crtControlFiber_runs (body := body) (flag := flag) (cA := hi) (cB := lo)
      (ts := ts) (rb := rb) (tc := tc) (tr := tr) (str := str) (acc := acc)
      (tA := tA) (tB := tB) (hswap.nodup_iff.mp hreg) R W hW valid hflag htc htr htA htB sl hsl
      (by rw [hc']; exact hlen) rest hstr
    simp only [crtControlFiberOut] at h
    rw [hc'] at h
    simpa only [crtControlFiberDir, crtControlShift, ↓reduceIte, hhi] using h

/-- Power-of-two cost envelope for the conditional physical fiber. -/
theorem crtControlFiber_cost_le (n k : ℕ) :
    n * (8 * k + 9) + 18 ≤ 2 ^ 5 * (n * (k + 1) + 1) := by
  nlinarith

end IntegerMultBounds.MathlibTM2.Fast
