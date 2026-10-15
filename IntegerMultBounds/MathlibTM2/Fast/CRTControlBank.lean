module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlTape

/-! # Embedding the CRT arithmetic bank in the full register file -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Replace only the arithmetic bank, preserving every external register. -/
noncomputable def crtBankOverlay {n : ℕ} (rg : TblR n → Fin T)
    (R : Regs T A) (ρ : TblR n → List (Fin (A + 4))) : Regs T A := by
  classical
  exact fun k => if h : ∃ r, rg r = k then ρ h.choose else R k

@[simp] theorem crtBankOverlay_on {n : ℕ} {rg : TblR n → Fin T}
    (hrg : Function.Injective rg) (R : Regs T A) (ρ : TblR n → List (Fin (A + 4)))
    (r : TblR n) : crtBankOverlay rg R ρ (rg r) = ρ r := by
  unfold crtBankOverlay
  split
  · rename_i h
    rw [hrg h.choose_spec]
  · rename_i h
    exact False.elim (h ⟨r, rfl⟩)

@[simp] theorem crtBankOverlay_off {n : ℕ} (rg : TblR n → Fin T)
    (R : Regs T A) (ρ : TblR n → List (Fin (A + 4))) (k : Fin T)
    (hk : ∀ r, rg r ≠ k) : crtBankOverlay rg R ρ k = R k := by
  simp [crtBankOverlay, show ¬∃ r, rg r = k from by simpa using hk]

/-- Turn the interpreter's frame contract into a whole-file CRT contract. -/
theorem crtRuns_of_tbl {n : ℕ} {rg : TblR n → Fin T}
    (hrg : Function.Injective rg) {p : Pr P T Q A U}
    {ρ ρ' : TblR n → List (Fin (A + 4))} {b : ℕ}
    (h : tblRuns body rg p ρ ρ' b) (R : Regs T A)
    (hR : ∀ r, R (rg r) = ρ r) :
    crtRuns body p R (crtBankOverlay rg R ρ') b := by
  intro v S hS _
  obtain ⟨v', S', m, hu, hm, he, hhold, hf⟩ := h v S (by simpa [tblHolds, hS] using hR)
  have hR' : S'.R = crtBankOverlay rg R ρ' := by
    funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hk
      rw [crtBankOverlay_on hrg]
      exact hhold r
    · have hk' : ∀ r, rg r ≠ k := by simpa using hk
      rw [crtBankOverlay_off _ _ _ _ hk', hf.2.2.2 k hk', hS]
  have heq : S' = { S with R := crtBankOverlay rg R ρ' } := by
    cases S; cases S'; simp_all [tblFr]
  exact ⟨v', m, hu, hm, heq ▸ he⟩

/-- Arithmetic with descriptor cleanup, preserving all external tapes. -/
theorem crtControlConsume_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) {W w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (hfit : st.val 9 < st.val 4 → st.val 5 + st.val 0 / st.val 1 * st.val 3 < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    crtRuns body (tblCompile rg crtControlConsume) R
      (crtBankOverlay rg R (tblRho W wl nl (crtControlConsumeState w st)))
      (13 * tblC W w) := by
  obtain ⟨st', hst', hr⟩ := (crtControlConsume_do st hfit).host (body := body)
    hrg wl nl hwl hnl hw hst
  subst st'
  exact crtRuns_of_tbl hrg hr R hR

/-- Install the four fields, retaining the scan's live values. -/
def crtControlLoadState (f : CrtControlField) (st : TblSt 10 A) : TblSt 10 A :=
  ⟨Function.update (Function.update (Function.update (Function.update st.val
    1 f.place) 2 f.bound) 3 f.weight) 4 (if f.active then 1 else 0), st.acc⟩

/-- Whole-file result of loading one descriptor packet. -/
def crtControlLoadRegs (rg : TblR 10 → Fin T) (src saved : Fin T)
    (W : ℕ) (f : CrtControlField) (rest : List (Fin (A + 4))) (R : Regs T A) : Regs T A :=
  Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update R
      (rg (.v 1)) (binSyms W f.place)) (rg (.v 2)) (binSyms W f.bound))
      (rg (.v 3)) (binSyms W f.weight)) (rg (.v 4)) (binSyms W (if f.active then 1 else 0)))
    src rest) saved ((crtControlPacket W f).reverse ++ R saved)

/-- The loader's concrete file represents the updated table state. -/
theorem crtControlLoadRegs_bank {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (src saved : Fin T) (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A)
    (f : CrtControlField) (rest : List (Fin (A + 4))) (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    ∀ r, crtControlLoadRegs rg src saved W f rest R (rg r) =
      tblRho W wl nl (crtControlLoadState f st) r := by
  intro r
  simp only [crtControlLoadRegs, Function.update_of_ne (hsrc r),
    Function.update_of_ne (hsaved r)]
  cases r with
  | v j =>
      simp [Function.update_apply, hrg.eq_iff, hR, crtControlLoadState, tblRho]
      split_ifs <;> rfl
  | wr => simp [hrg.eq_iff, hR, tblRho]
  | wn => simp [hrg.eq_iff, hR, tblRho]
  | acc => simp [hrg.eq_iff, hR, crtControlLoadState, tblRho]
  | z j => simp [hrg.eq_iff, hR, tblRho]

/-- The descriptor loader uses the bank's width and two scratch registers.
Only the descriptor stream and saved stack lie outside the arithmetic bank. -/
theorem crtControlLoad_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (src saved : Fin T) (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved)
    (hne : src ≠ saved) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (st : TblSt 10 A) (f : CrtControlField)
    (rest : List (Fin (A + 4))) (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl st r)
    (htape : R src = crtControlPacket W f ++ rest) :
    crtRuns body
      (crtLoadControl (rg .wr) (rg (.z 0)) src saved (rg (.z 1))
        (rg (.v 1)) (rg (.v 2)) (rg (.v 3)) (rg (.v 4))) R
      (crtControlLoadRegs rg src saved W f rest R) (48 * W + 56) := by
  apply crtLoadControl_runs
  · simp [List.nodup_cons, hrg.eq_iff, hsrc, hsaved, hne, Ne.symm, eq_comm]
  · simpa [hR, tblRho] using hwl
  · exact htape
  all_goals simp [hR, tblRho, length_binSyms]

/-- Canonical live bank between packets. All descriptor and scratch variables
are zero; the emitted-symbol accumulator is an arbitrary preserved spectator. -/
def crtControlState (F K : ℕ) (valid : Bool) (acc : List (Fin (A + 4))) : TblSt 10 A :=
  ⟨fun j => if j = 0 then F else if j = 5 then K else if j = 6 then
    (if valid then 1 else 0) else 0, acc⟩

theorem crtControlState_load_input (f : CrtControlField) (F K : ℕ) (valid : Bool)
    (acc : List (Fin (A + 4))) :
    crtControlStepInput f F K valid (crtControlLoadState f (crtControlState F K valid acc)) := by
  simp [crtControlStepInput, crtControlLoadState, crtControlState]

/-- The cleaned arithmetic state depends only on the eight live input values. -/
theorem crtControlConsumeState_input {A : ℕ} (w : ℕ) (f : CrtControlField)
    (F K : ℕ) (valid : Bool) (st : TblSt 10 A)
    (hin : crtControlStepInput f F K valid st) :
    crtControlConsumeState w st =
      crtControlState (F % f.place)
        (K + if f.active then F / f.place * f.weight else 0)
        (valid && (!f.active || decide (F / f.place < f.bound))) st.acc := by
  obtain ⟨hF, hp, hb, hw, ha, hK, hv, hz⟩ := hin
  have hs := crtControlStepState_spec w st
  have hc := crtControlConsumeState_spec w st
  have hrest := hc.2.2.2.2.1
  have h0 := (hrest 0 (by decide) (by decide) (by decide) (by decide)).trans hs.1
  have h5 := (hrest 5 (by decide) (by decide) (by decide) (by decide)).trans hs.2.1
  have h6 := (hrest 6 (by decide) (by decide) (by decide) (by decide)).trans hs.2.2.1
  have h7 := (hrest 7 (by decide) (by decide) (by decide) (by decide)).trans hs.2.2.2.1
  have h8 := (hrest 8 (by decide) (by decide) (by decide) (by decide)).trans hs.2.2.2.2.1
  have h9 := (hrest 9 (by decide) (by decide) (by decide) (by decide)).trans
    (hs.2.2.2.2.2.1 9 (by decide) (by decide) (by decide) (by decide) (by decide))
  simp only [hF, hp, hb, hw, ha, hK, hv, hz] at h0 h5 h6 h9
  have hv6 : (crtControlConsumeState w st).val 6 =
      (if valid && (!f.active || decide (F / f.place < f.bound)) then 1 else 0) := by
    cases hactive : f.active <;> cases valid <;> by_cases hlt : F / f.place < f.bound <;>
      simpa [hactive, hlt] using h6
  have hv5 : (crtControlConsumeState w st).val 5 =
      K + if f.active then F / f.place * f.weight else 0 := by
    cases hactive : f.active <;> simpa [hactive] using h5
  apply (show ∀ x y : TblSt 10 A, x.val = y.val → x.acc = y.acc → x = y from by
    intro x y; cases x; cases y; simp_all)
  · funext j
    fin_cases j
    · exact h0
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1
    · exact hc.2.2.2.1
    · exact hv5
    · exact hv6
    · exact h7
    · exact h8
    · exact h9
  · exact hc.2.2.2.2.2

/-- Consuming a loaded descriptor returns exactly the canonical next bank. -/
theorem crtControlState_consume (w : ℕ) (f : CrtControlField) (F K : ℕ) (valid : Bool)
    (acc : List (Fin (A + 4))) :
    crtControlConsumeState w (crtControlLoadState f (crtControlState F K valid acc)) =
      crtControlState (F % f.place)
        (K + if f.active then F / f.place * f.weight else 0)
        (valid && (!f.active || decide (F / f.place < f.bound))) acc :=
  crtControlConsumeState_input w f F K valid _ (crtControlState_load_input f F K valid acc)

end IntegerMultBounds.MathlibTM2.Fast
