module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlTape

/-!
# A fixed runtime loop for CRT descriptor tapes

The executable scanner uses source-tape emptiness, not a program unrolled in
the number of axes. Its bank interface isolates the concrete loader/interpreter
embedding. A one-packet host contract suffices for the entire loop, arithmetic
semantics, sticky validity, and restoration of the original descriptor tape.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open TableVM

structure CrtControlScanState where
  address : ℕ
  value : ℕ
  valid : Bool
  deriving DecidableEq

/-- The live arithmetic state after consuming one descriptor. -/
def crtControlScanStep (s : CrtControlScanState) (f : CrtControlField) : CrtControlScanState :=
  ⟨s.address % f.place,
    s.value + (if f.active then s.address / f.place * f.weight else 0),
    s.valid && (!f.active || decide (s.address / f.place < f.bound))⟩

/-- Remaining address after all successive place divisions. -/
def crtControlRemainder : List CrtControlField → ℕ → ℕ
  | [], F => F
  | f :: fs, F => crtControlRemainder fs (F % f.place)

/-- Fold semantics explicitly preserve an incoming sum and a failed validity flag. -/
theorem crtControlScan_fold (fs : List CrtControlField) (s : CrtControlScanState) :
    fs.foldl crtControlScanStep s =
      ⟨crtControlRemainder fs s.address,
       s.value + crtControlValue fs s.address,
       s.valid && crtControlValid fs s.address⟩ := by
  induction fs generalizing s with
  | nil => simp [crtControlRemainder, crtControlValue, crtControlValid]
  | cons f fs ih =>
    rw [List.foldl_cons, ih]
    simp [crtControlScanStep, crtControlRemainder, crtControlValue,
      crtControlValid, Nat.add_assoc, Bool.and_assoc]

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Load four runtime words then execute the fixed arithmetic descriptor step. -/
def crtControlPacketStep (rg : TblR 10 → Fin T)
    (width tmp src saved spare : Fin T) : Pr P T Q A U :=
  .seq (crtLoadControl width tmp src saved spare
    (rg (.v 1)) (rg (.v 2)) (rg (.v 3)) (rg (.v 4)))
    (tblCompile rg crtControlConsume)

/-- Fixed program for arbitrarily many runtime descriptors, followed by restoration. -/
def crtControlScan (rg : TblR 10 → Fin T)
    (width tmp src saved spare : Fin T) : Pr P T Q A U :=
  .seq (crtWhile src (crtControlPacketStep rg width tmp src saved spare))
    (crtMv saved src)

/-- The concrete bank interface must describe exactly the source and saved tapes.
The arithmetic state is a parameter, so a concrete bank can expose its binary
register encoding without changing the scanner program. -/
structure CrtControlScanBank (W : ℕ) (src saved : Fin T) where
  regs : List CrtControlField → List CrtControlField → CrtControlScanState → Regs T A
  source : ∀ done rest s, regs done rest s src = crtControlTape W rest
  saved : ∀ done rest s, regs done rest s saved = (crtControlTape W done).reverse

private theorem crtControl_take_succ {α : Type*} (xs : List α) (n : ℕ)
    (hn : n < xs.length) : xs.take (n + 1) = xs.take n ++ [xs[n]] := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hn' : n < xs.length := by simpa using hn
      simpa only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ] using
        congrArg (List.cons x) (ih n hn')

/-- A one-packet contract on reachable prefixes yields the whole actual-host
scan. The output bank has the exact arithmetic fold; both descriptor tapes are
restored to their original positions. -/
theorem crtControlScan_runs (rg : TblR 10 → Fin T)
    (width tmp src saved spare : Fin T) (hne : saved ≠ src)
    (W : ℕ) (hW : 0 < W) (fs : List CrtControlField)
    (s : CrtControlScanState) (bank : CrtControlScanBank (T := T) (A := A) W src saved)
    (b : ℕ)
    (hstep : ∀ done f rest,
      done ++ f :: rest = fs →
      crtRuns body (crtControlPacketStep rg width tmp src saved spare)
        (bank.regs done (f :: rest) (done.foldl crtControlScanStep s))
        (bank.regs (done ++ [f]) rest
          (crtControlScanStep (done.foldl crtControlScanStep s) f)) b) :
    crtRuns body (crtControlScan rg width tmp src saved spare)
      (bank.regs [] fs s)
      (Function.update
        (Function.update (bank.regs fs [] (fs.foldl crtControlScanStep s)) saved [])
        src (crtControlTape W fs))
      (fs.length * (b + 2) + 2 + (8 * fs.length * W + 2)) := by
  let Ψ : ℕ → Regs T A := fun n =>
    bank.regs (fs.take n) (fs.drop n) ((fs.take n).foldl crtControlScanStep s)
  have hp : ∀ n < fs.length,
      Ψ n src ≠ [] ∧ crtRuns body
        (crtControlPacketStep rg width tmp src saved spare) (Ψ n) (Ψ (n + 1)) b := by
    intro n hn
    have hd : fs.drop n = fs[n] :: fs.drop (n + 1) := List.drop_eq_getElem_cons hn
    have ht := crtControl_take_succ fs n hn
    constructor
    · intro h
      have hempty : fs.drop n = [] := (crtControlTape_eq_nil W hW _).mp
        (by simpa only [Ψ, bank.source] using h)
      rw [hd] at hempty
      contradiction
    · have h := hstep (fs.take n) fs[n] (fs.drop (n + 1)) (by
        rw [← hd]; exact List.take_append_drop n fs)
      simpa only [Ψ, hd, ht, List.foldl_append, List.foldl_cons, List.foldl_nil] using h
  have hN : Ψ fs.length src = [] := by simp [Ψ, bank.source, crtControlTape]
  have hloop := crtWhile_runs (body := body) hp hN
  have hrestore := crtControlTape_restore (body := body) hne W fs (Ψ fs.length) hN
    (by simp [Ψ, bank.saved])
  simpa [crtControlScan, Ψ] using crtRuns_seq hloop hrestore

/-- The output of the scan has the original control evaluator's value and
validity, including an initially invalid state. -/
theorem crtControlScan_result (fs : List CrtControlField) (s : CrtControlScanState) :
    (fs.foldl crtControlScanStep s).address = crtControlRemainder fs s.address ∧
    (fs.foldl crtControlScanStep s).value = s.value + crtControlValue fs s.address ∧
    (fs.foldl crtControlScanStep s).valid = (s.valid && crtControlValid fs s.address) := by
  rw [crtControlScan_fold]
  exact ⟨rfl, rfl, rfl⟩

/-- With the concrete four-word loader and thirteen arithmetic atoms, the
entire scan and restoration are linear in descriptor count and quadratic in
binary word width. -/
theorem crtControlScan_cost_le (n W w : ℕ) (hw : w ≤ W) :
    n * ((48 * W + 56 + 13 * tblC W w) + 2) + 2 + (8 * n * W + 2) ≤
      2 ^ 10 * n * (W + 4) ^ 2 + 4 := by
  have hc : (48 * W + 56 + 13 * tblC W w) + 2 + 8 * W ≤
      2 ^ 10 * (W + 4) ^ 2 := by
    unfold tblC
    nlinarith
  have h := Nat.mul_le_mul_left n hc
  nlinarith

end IntegerMultBounds.MathlibTM2.Fast
