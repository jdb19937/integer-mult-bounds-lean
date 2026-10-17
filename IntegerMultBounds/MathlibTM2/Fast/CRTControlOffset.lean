module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlProg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Materializing computed CRT offsets on the finite host

The binary offset kernel is followed by two binary-to-unary conversions.
The low length lands in scratch register 0, its complement in register 1;
all conversion workspace is restored. These two registers can serve as the
rotation counters of `crtRotFib` (high first forward, low first inverse).
The conversion costs are linear in the modulus times the binary word width,
and must be charged separately from polynomial binary control arithmetic.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Binary-to-unary conversion as a framed table-bank contract. Only the
output register changes; the binary source and three scratch registers return
unchanged, as do the input/output streams and registers outside the bank. -/
theorem crtControl_toUnary_runs {n : ℕ} {rg : TblR n → Fin T}
    (hrg : Function.Injective rg) {a z w t t₂ : TblR n}
    (hd : [a, z, w, t, t₂].Nodup) (ρ : TblR n → List (Fin (A + 4)))
    {W x : ℕ} (hx : x < 2 ^ W) (ha : ρ a = binSyms W x)
    (hw : ρ w = []) (ht : ρ t = []) (ht₂ : ρ t₂ = []) :
    tblRuns body rg (toUnary (rg a) (rg z) (rg w) (rg t) (rg t₂)) ρ
      (Function.update ρ z (List.replicate x tick ++ ρ z))
      (W * (4 * x + 11) + 2 * x + 6) := by
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := toUnary_exec body (tbl_nodup hrg hd) hx v S
    (by rw [hS, ha]) (by rw [hS, hw]) (by rw [hS, ht]) (by rw [hS, ht₂])
  refine ⟨v', _, m, hu, hm, he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS z, hS]

/-- Convert the computed low offset and its complement to unary counters. -/
def crtControlOffsetUnary (rg : TblR 5 → Fin T) : Pr P T Q A U :=
  .seq (toUnary (rg (.v 3)) (rg (.z 0)) (rg (.z 2)) (rg (.z 3)) (rg (.z 4)))
    (toUnary (rg (.v 4)) (rg (.z 1)) (rg (.z 2)) (rg (.z 3)) (rg (.z 4)))

/-- Register file after materializing the two rotation lengths. -/
def crtControlOffsetRho (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 5 A) : TblR 5 → List (Fin (A + 4)) :=
  Function.update (Function.update (tblRho W wl nl st) (.z 0)
    (List.replicate (st.val 3) tick)) (.z 1) (List.replicate (st.val 4) tick)

/-- Both conversions retain the binary bank and restore every temporary
except the two explicitly returned unary lengths. -/
theorem crtControlOffsetUnary_runs {rg : TblR 5 → Fin T}
    (hrg : Function.Injective rg) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 5 A) (hlo : st.val 3 < 2 ^ W) (hhi : st.val 4 < 2 ^ W) :
    tblRuns body rg (crtControlOffsetUnary rg) (tblRho W wl nl st)
      (crtControlOffsetRho W wl nl st)
      (W * (4 * (st.val 3 + st.val 4) + 22) + 2 * (st.val 3 + st.val 4) + 12) := by
  have h₁ := crtControl_toUnary_runs (body := body) hrg
    (a := .v 3) (z := .z 0) (w := .z 2) (t := .z 3) (t₂ := .z 4)
    (by decide) (tblRho W wl nl st) hlo rfl rfl rfl rfl
  simp only [tblRho_z, List.append_nil] at h₁
  have h₂ := crtControl_toUnary_runs (body := body) hrg
    (a := .v 4) (z := .z 1) (w := .z 2) (t := .z 3) (t₂ := .z 4)
    (by decide) (Function.update (tblRho W wl nl st) (.z 0) (List.replicate (st.val 3) tick))
    hhi (by simp) (by simp) (by simp) (by simp)
  simp only [Function.update_of_ne (by decide : (TblR.z 1 : TblR 5) ≠ .z 0),
    tblRho_z, List.append_nil] at h₂
  exact (h₁.seq h₂).mono (by ring_nf; exact le_rfl)

/-- Actual finite-host program: compute the modular offset, then materialize
both directional rotation lengths. -/
def crtControlOffsetHost (rg : TblR 5 → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg crtControlOffset) (crtControlOffsetUnary rg)

/-- The offset bridge has an explicit step bound and a framed final bank.
The only nonempty scratch registers at return are the two unary outputs. -/
theorem crtControlOffsetHost_runs {rg : TblR 5 → Fin T}
    (hrg : Function.Injective rg) {W w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 5 A) (hst : ∀ j, st.val j < 2 ^ W)
    (hS : 0 < st.val 0) (hprod : st.val 1 * st.val 2 < 2 ^ W) :
    ∃ st' : TblSt 5 A,
      st'.val 3 = st.val 1 * st.val 2 % st.val 0 ∧
      st'.val 4 = st.val 0 - st.val 1 * st.val 2 % st.val 0 ∧
      (∀ j, j ≠ 3 → j ≠ 4 → st'.val j = st.val j) ∧ st'.acc = st.acc ∧
      tblRuns body rg (crtControlOffsetHost rg) (tblRho W wl nl st)
        (crtControlOffsetRho W wl nl st')
        (3 * tblC W w + W * (4 * st.val 0 + 22) + 2 * st.val 0 + 12) := by
  obtain ⟨st', hs, hr⟩ := (crtControlOffset_do st hS (hst 0) hprod).host
    (body := body) hrg wl nl hwl hnl hw hst
  obtain ⟨hlo, hhi, hpres, hacc⟩ := hs
  have hlt : st.val 1 * st.val 2 % st.val 0 < st.val 0 := Nat.mod_lt _ hS
  have hlo' : st'.val 3 < 2 ^ W := by rw [hlo]; exact hlt.trans (hst 0)
  have hhi' : st'.val 4 < 2 ^ W := by rw [hhi]; exact (Nat.sub_le _ _).trans_lt (hst 0)
  have hsum : st'.val 3 + st'.val 4 = st.val 0 := by rw [hlo, hhi]; omega
  refine ⟨st', hlo, hhi, hpres, hacc, ?_⟩
  have hu := crtControlOffsetUnary_runs (body := body) hrg W wl nl st' hlo' hhi'
  rw [hsum] at hu
  exact (hr.seq hu).mono (by omega)

/-- Unary counter lengths and the exact scratch-restoration contract. -/
theorem crtControlOffsetRho_spec (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 5 A) :
    (crtControlOffsetRho W wl nl st (.z 0)).length = st.val 3 ∧
    (crtControlOffsetRho W wl nl st (.z 1)).length = st.val 4 ∧
    (∀ j : Fin 12, j ≠ 0 → j ≠ 1 → crtControlOffsetRho W wl nl st (.z j) = []) ∧
    (∀ j, crtControlOffsetRho W wl nl st (.v j) = binSyms W (st.val j)) := by
  simp only [crtControlOffsetRho]
  refine ⟨by simp, by simp, ?_, by intro j; simp⟩
  intro j h0 h1
  simp [h0, h1]

/-- Clear the materialized counters after a rotation that preserves them. -/
def crtControlOffsetClear (rg : TblR 5 → Fin T) : Pr P T Q A U :=
  .seq (bclear (rg (.z 0))) (bclear (rg (.z 1)))

/-- Returning both unary outputs restores the original table-bank scratch
in `2*(low+high)+4` actual host steps. -/
theorem crtControlOffsetClear_runs {rg : TblR 5 → Fin T}
    (hrg : Function.Injective rg) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 5 A) :
    tblRuns body rg (crtControlOffsetClear rg) (crtControlOffsetRho W wl nl st)
      (tblRho W wl nl st) (2 * (st.val 3 + st.val 4) + 4) := by
  have h₁ := tbl_bclear_runs (body := body) hrg (.z 0) (crtControlOffsetRho W wl nl st)
  have h₂ := tbl_bclear_runs (body := body) hrg (.z 1)
    (Function.update (crtControlOffsetRho W wl nl st) (.z 0) [])
  have h := h₁.seq h₂
  have hout : Function.update (Function.update (crtControlOffsetRho W wl nl st) (.z 0) [])
      (.z 1) [] = tblRho W wl nl st := by
    funext j
    cases j with
    | v j => simp [crtControlOffsetRho]
    | wr => simp [crtControlOffsetRho]
    | wn => simp [crtControlOffsetRho]
    | acc => simp [crtControlOffsetRho]
    | z j =>
      by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp [crtControlOffsetRho, h0, h1]
  exact (h.congr hout).mono (by simp [crtControlOffsetRho]; omega)

end IntegerMultBounds.MathlibTM2.Fast
