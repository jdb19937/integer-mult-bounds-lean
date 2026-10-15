module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlBank
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlOffset

/-! # Offsets in the descriptor scanner's own bank

The scanner leaves its weighted value in variable 5 and validity in variable 6.
After loading the target modulus and multiplier into variables 1 and 2, this
bridge computes offsets in variables 3 and 4 without moving either live value.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Direct modular arithmetic in the ten-variable scanner bank. -/
def crtControlOffset10 : TblCode 10 :=
  tblBlock 10 [.mul 2 5 3, .mod 3 1 3] (.sub 1 3 4)

/-- The scanner's value and validity survive offset computation. -/
theorem crtControlOffset10_do {A W w : ℕ} (st : TblSt 10 A)
    (hS : 0 < st.val 1) (hSlt : st.val 1 < 2 ^ W)
    (hprod : st.val 2 * st.val 5 < 2 ^ W) :
    TblDo A W w crtControlOffset10 st (fun t =>
      t.val 3 = st.val 2 * st.val 5 % st.val 1 ∧
      t.val 4 = st.val 1 - st.val 2 * st.val 5 % st.val 1 ∧
      (∀ j, j ≠ 3 → j ≠ 4 → t.val j = st.val j) ∧ t.acc = st.acc) 3 := by
  have hlo := (Nat.mod_lt (st.val 2 * st.val 5) hS).le
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hprod, hlo, hSlt]
  · simp [tblExactList, TblIns.exact]
    intro j h3 h4
    simp [h3, h4]

/-- Materialize both rotation lengths using five of the bank's empty scratch
registers; variables 0, 5 and 6 remain the scanner's live state. -/
def crtControlUnary10 (rg : TblR 10 → Fin T) : Pr P T Q A U :=
  .seq (toUnary (rg (.v 3)) (rg (.z 0)) (rg (.z 2)) (rg (.z 3)) (rg (.z 4)))
    (toUnary (rg (.v 4)) (rg (.z 1)) (rg (.z 2)) (rg (.z 3)) (rg (.z 4)))

def crtControlUnary10Rho (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) : TblR 10 → List (Fin (A + 4)) :=
  Function.update (Function.update (tblRho W wl nl st) (.z 0)
    (List.replicate (st.val 3) tick)) (.z 1) (List.replicate (st.val 4) tick)

theorem crtControlUnary10_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) (hlo : st.val 3 < 2 ^ W) (hhi : st.val 4 < 2 ^ W) :
    tblRuns body rg (crtControlUnary10 rg) (tblRho W wl nl st)
      (crtControlUnary10Rho W wl nl st)
      (W * (4 * (st.val 3 + st.val 4) + 22) + 2 * (st.val 3 + st.val 4) + 12) := by
  have h₁ := crtControl_toUnary_runs (body := body) hrg
    (a := .v 3) (z := .z 0) (w := .z 2) (t := .z 3) (t₂ := .z 4)
    (by decide) (tblRho W wl nl st) hlo rfl rfl rfl rfl
  simp only [tblRho_z, List.append_nil] at h₁
  have h₂ := crtControl_toUnary_runs (body := body) hrg
    (a := .v 4) (z := .z 1) (w := .z 2) (t := .z 3) (t₂ := .z 4)
    (by decide) (Function.update (tblRho W wl nl st) (.z 0) (List.replicate (st.val 3) tick))
    hhi (by simp) (by simp) (by simp) (by simp)
  simp only [Function.update_of_ne (by decide : (TblR.z 1 : TblR 10) ≠ .z 0),
    tblRho_z, List.append_nil] at h₂
  exact (h₁.seq h₂).mono (by ring_nf; exact le_rfl)

/-- Compute and materialize offsets in the scanner's bank. -/
def crtControlOffsets (rg : TblR 10 → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg crtControlOffset10) (crtControlUnary10 rg)

theorem crtControlOffsets_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) {W w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (hS : 0 < st.val 1) (hprod : st.val 2 * st.val 5 < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    ∃ st' : TblSt 10 A,
      st'.val 3 = st.val 2 * st.val 5 % st.val 1 ∧
      st'.val 4 = st.val 1 - st.val 2 * st.val 5 % st.val 1 ∧
      (∀ j, j ≠ 3 → j ≠ 4 → st'.val j = st.val j) ∧ st'.acc = st.acc ∧
      crtRuns body (crtControlOffsets rg) R
        (crtBankOverlay rg R (crtControlUnary10Rho W wl nl st'))
        (3 * tblC W w + W * (4 * st.val 1 + 22) + 2 * st.val 1 + 12) := by
  obtain ⟨st', hs, hr⟩ := (crtControlOffset10_do st hS (hst 1) hprod).host
    (body := body) hrg wl nl hwl hnl hw hst
  obtain ⟨hlo, hhi, hpres, hacc⟩ := hs
  have hlt : st.val 2 * st.val 5 % st.val 1 < st.val 1 := Nat.mod_lt _ hS
  have hlo' : st'.val 3 < 2 ^ W := by rw [hlo]; exact hlt.trans (hst 1)
  have hhi' : st'.val 4 < 2 ^ W := by rw [hhi]; exact (Nat.sub_le _ _).trans_lt (hst 1)
  have hsum : st'.val 3 + st'.val 4 = st.val 1 := by rw [hlo, hhi]; omega
  refine ⟨st', hlo, hhi, hpres, hacc, ?_⟩
  have hu := crtControlUnary10_runs (body := body) hrg W wl nl st' hlo' hhi'
  rw [hsum] at hu
  exact crtRuns_of_tbl hrg ((hr.seq hu).mono (by omega)) R hR

/-- Unary counter lengths and the exact scratch-restoration contract. -/
theorem crtControlUnary10Rho_spec (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) :
    (crtControlUnary10Rho W wl nl st (.z 0)).length = st.val 3 ∧
    (crtControlUnary10Rho W wl nl st (.z 1)).length = st.val 4 ∧
    (∀ j : Fin 12, j ≠ 0 → j ≠ 1 → crtControlUnary10Rho W wl nl st (.z j) = []) ∧
    (∀ j, crtControlUnary10Rho W wl nl st (.v j) = binSyms W (st.val j)) := by
  simp only [crtControlUnary10Rho]
  refine ⟨by simp, by simp, ?_, by intro j; simp⟩
  intro j h0 h1
  simp [h0, h1]

/-- Clear the materialized counters after a rotation that preserves them. -/
def crtControlUnary10Clear (rg : TblR 10 → Fin T) : Pr P T Q A U :=
  .seq (bclear (rg (.z 0))) (bclear (rg (.z 1)))

/-- Returning both unary outputs restores the original table-bank scratch
in `2*(low+high)+4` actual host steps. -/
theorem crtControlUnary10Clear_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) :
    tblRuns body rg (crtControlUnary10Clear rg) (crtControlUnary10Rho W wl nl st)
      (tblRho W wl nl st) (2 * (st.val 3 + st.val 4) + 4) := by
  have h₁ := tbl_bclear_runs (body := body) hrg (.z 0) (crtControlUnary10Rho W wl nl st)
  have h₂ := tbl_bclear_runs (body := body) hrg (.z 1)
    (Function.update (crtControlUnary10Rho W wl nl st) (.z 0) [])
  have h := h₁.seq h₂
  have hout : Function.update (Function.update (crtControlUnary10Rho W wl nl st) (.z 0) [])
      (.z 1) [] = tblRho W wl nl st := by
    funext j
    cases j with
    | v j => simp [crtControlUnary10Rho]
    | wr => simp [crtControlUnary10Rho]
    | wn => simp [crtControlUnary10Rho]
    | acc => simp [crtControlUnary10Rho]
    | z j =>
      by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp [crtControlUnary10Rho, h0, h1]
  exact (h.congr hout).mono (by simp [crtControlUnary10Rho]; omega)

end IntegerMultBounds.MathlibTM2.Fast
