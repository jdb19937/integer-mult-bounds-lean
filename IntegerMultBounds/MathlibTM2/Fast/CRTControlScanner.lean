module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlBank
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlScan
import IntegerMultBounds.MathlibTM2.Fast.CRTControlBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! # Concrete fixed CRT descriptor scanner

The bank, loader, arithmetic interpreter, runtime loop, and restoration are
composed here. Only arithmetic fit and register-disjointness assumptions remain;
there is no assumed execution contract for a packet or loop body.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- The complete register file, including both external descriptor tapes. -/
noncomputable def crtControlConcreteBank (rg : TblR 10 → Fin T)
    (src saved : Fin T) (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved)
    (hne : src ≠ saved) (W : ℕ) (wl nl acc : List (Fin (A + 4))) (R : Regs T A) :
    CrtControlScanBank (A := A) W src saved where
  regs := fun done rest s => crtBankOverlay rg
    (Function.update (Function.update R src (crtControlTape W rest)) saved
      (crtControlTape W done).reverse)
    (tblRho W wl nl (crtControlState s.address s.value s.valid acc))
  source := by intro done rest s; simp [crtBankOverlay_off, hsrc, hne]
  saved := by intro done rest s; simp [crtBankOverlay_off, hsaved]

/-- The budget and address do not increase while scanning any prefix. -/
theorem crtControlScan_fold_budget (fs : List CrtControlField) (s : CrtControlScanState)
    (M : ℕ) (hf : ∀ f ∈ fs, 0 < f.place ∧ f.weight ≤ M) :
    (fs.foldl crtControlScanStep s).address ≤ s.address ∧
    (fs.foldl crtControlScanStep s).value + (fs.foldl crtControlScanStep s).address * M ≤
      s.value + s.address * M := by
  induction fs generalizing s with
  | nil => simp
  | cons f fs ih =>
    have hf' := hf f (by simp)
    have ht := ih (crtControlScanStep s f) (fun g hg => hf g (by simp [hg]))
    have ha : (crtControlScanStep s f).address ≤ s.address := Nat.mod_le _ _
    have hb : (crtControlScanStep s f).value + (crtControlScanStep s f).address * M ≤
        s.value + s.address * M := by
      have h := crtControl_accumulate_le f s.address s.value M
        (s.value + s.address * M) le_rfl hf'
      cases hactive : f.active <;> simp only [crtControlScanStep, hactive, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero] <;> omega
    exact ⟨ht.1.trans ha, ht.2.trans hb⟩

/-- One concrete packet load and arithmetic execution, with all external
registers preserved and no assumed machine-step premise. -/
theorem crtControlPacket_concrete {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (src saved : Fin T) (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved)
    (hne : src ≠ saved) (W w : ℕ) (hW : 0 < W)
    (wl nl acc : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) (R : Regs T A) (done rest : List CrtControlField)
    (f : CrtControlField) (s : CrtControlScanState) (M : ℕ)
    (hfields : 0 < f.place ∧ f.place < 2 ^ W ∧ f.bound < 2 ^ W ∧
      f.weight < 2 ^ W ∧ f.weight ≤ M)
    (hF : s.address < 2 ^ W) (hbudget : s.value + s.address * M < 2 ^ W) :
    let bank := crtControlConcreteBank rg src saved hsrc hsaved hne W wl nl acc R
    crtRuns body (crtControlPacketStep rg (rg .wr) (rg (.z 0)) src saved (rg (.z 1)))
      (bank.regs done (f :: rest) s)
      (bank.regs (done ++ [f]) rest (crtControlScanStep s f))
      (48 * W + 56 + 13 * tblC W w) := by
  let bank := crtControlConcreteBank rg src saved hsrc hsaved hne W wl nl acc R
  let st := crtControlState s.address s.value s.valid acc
  let R₀ := bank.regs done (f :: rest) s
  let R₁ := crtControlLoadRegs rg src saved W f (crtControlTape W rest) R₀
  have hR₀ : ∀ r, R₀ (rg r) = tblRho W wl nl st r := by
    intro r; exact crtBankOverlay_on hrg _ _ r
  have hload := crtControlLoad_runs (body := body) hrg src saved hsrc hsaved hne W
    wl nl hwl st f (crtControlTape W rest) R₀ hR₀
    (by rw [show R₀ src = crtControlTape W (f :: rest) from bank.source _ _ _];
        rfl)
  have hR₁ : ∀ r, R₁ (rg r) = tblRho W wl nl (crtControlLoadState f st) r :=
    crtControlLoadRegs_bank hrg src saved hsrc hsaved W wl nl st f _ R₀ hR₀
  have hone : 1 < (2 : ℕ) ^ W := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
    norm_num at h
    omega
  have hst : ∀ j, (crtControlLoadState f st).val j < 2 ^ W := by
    intro j
    have hK : s.value < 2 ^ W := by omega
    simp only [crtControlLoadState, st, crtControlState, Function.update_apply]
    split_ifs <;> first | assumption | omega
  have hfit : (crtControlLoadState f st).val 9 < (crtControlLoadState f st).val 4 →
      (crtControlLoadState f st).val 5 + (crtControlLoadState f st).val 0 /
        (crtControlLoadState f st).val 1 * (crtControlLoadState f st).val 3 < 2 ^ W := by
    intro _
    have hb := crtControl_accumulate_le f s.address s.value M
      (s.value + s.address * M) le_rfl ⟨hfields.1, hfields.2.2.2.2⟩
    simpa [st, crtControlLoadState, crtControlState] using
      (show s.value + s.address / f.place * f.weight < 2 ^ W by omega)
  have hconsume := crtControlConsume_runs (body := body) hrg wl nl hwl hnl hw
    (crtControlLoadState f st) hst hfit R₁ hR₁
  refine crtRuns_congr (crtRuns_seq hload hconsume) ?_
  rw [show crtControlConsumeState w (crtControlLoadState f st) =
    crtControlState (crtControlScanStep s f).address (crtControlScanStep s f).value
      (crtControlScanStep s f).valid acc from crtControlState_consume _ _ _ _ _ _]
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    simp only [crtControlConcreteBank, crtBankOverlay_on hrg]
  · have hk' : ∀ r, rg r ≠ k := by simpa using hk
    have hv : ∀ j, k ≠ rg (.v j) := fun j => Ne.symm (hk' (.v j))
    simp [R₁, R₀, bank, crtControlConcreteBank, crtControlLoadRegs,
      crtBankOverlay_off _ _ _ _ hk', hv, Function.update_apply,
      crtControlTape, List.flatMap_append, List.reverse_append]
    split_ifs <;> simp_all [crtBankOverlay_off]

/-- A complete runtime descriptor scan with restored descriptor tape, explicit
arithmetic output, and a power-of-two polynomial actual-host cost. All packet
execution and intermediate overflow obligations are proved from the initial
budget, even when control digits fail their validity tests. -/
theorem crtControlScanner_exact_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (src saved : Fin T) (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved)
    (hne : src ≠ saved) (W w : ℕ) (hW : 0 < W)
    (wl nl acc : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) (R : Regs T A) (fs : List CrtControlField)
    (s : CrtControlScanState) (M : ℕ)
    (hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ W ∧ f.bound < 2 ^ W ∧
      f.weight < 2 ^ W ∧ f.weight ≤ M)
    (hF : s.address < 2 ^ W) (hbudget : s.value + s.address * M < 2 ^ W) :
    let bank := crtControlConcreteBank rg src saved hsrc hsaved hne W wl nl acc R
    let out : CrtControlScanState := ⟨crtControlRemainder fs s.address,
      s.value + crtControlValue fs s.address, s.valid && crtControlValid fs s.address⟩
    crtRuns body (crtControlScan rg (rg .wr) (rg (.z 0)) src saved (rg (.z 1)))
      (bank.regs [] fs s)
      (Function.update (Function.update (bank.regs fs [] out) saved [])
        src (crtControlTape W fs))
      (fs.length * ((48 * W + 56 + 13 * tblC W w) + 2) + 2 +
        (8 * fs.length * W + 2)) := by
  let bank := crtControlConcreteBank rg src saved hsrc hsaved hne W wl nl acc R
  have h := crtControlScan_runs (body := body) rg (rg .wr) (rg (.z 0)) src saved
    (rg (.z 1)) (Ne.symm hne) W hW fs s bank (48 * W + 56 + 13 * tblC W w) (by
      intro done f rest hsplit
      have hd : ∀ g ∈ done, 0 < g.place ∧ g.weight ≤ M := by
        intro g hg
        have hm : g ∈ fs := by rw [← hsplit]; exact List.mem_append_left _ hg
        exact ⟨(hfields g hm).1, (hfields g hm).2.2.2.2⟩
      have hb := crtControlScan_fold_budget done s M hd
      apply crtControlPacket_concrete hrg src saved hsrc hsaved hne W w hW
        wl nl acc hwl hnl hw R done rest f (done.foldl crtControlScanStep s) M
      · apply hfields
        rw [← hsplit]
        simp
      · exact hb.1.trans_lt hF
      · exact hb.2.trans_lt hbudget)
  simpa only [crtControlScan_fold] using h

/-- Power-of-two envelope for the complete concrete scanner. -/
theorem crtControlScanner_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (src saved : Fin T) (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved)
    (hne : src ≠ saved) (W w : ℕ) (hW : 0 < W)
    (wl nl acc : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) (R : Regs T A) (fs : List CrtControlField)
    (s : CrtControlScanState) (M : ℕ)
    (hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ W ∧ f.bound < 2 ^ W ∧
      f.weight < 2 ^ W ∧ f.weight ≤ M)
    (hF : s.address < 2 ^ W) (hbudget : s.value + s.address * M < 2 ^ W) :
    let bank := crtControlConcreteBank rg src saved hsrc hsaved hne W wl nl acc R
    let out : CrtControlScanState := ⟨crtControlRemainder fs s.address,
      s.value + crtControlValue fs s.address, s.valid && crtControlValid fs s.address⟩
    crtRuns body (crtControlScan rg (rg .wr) (rg (.z 0)) src saved (rg (.z 1)))
      (bank.regs [] fs s)
      (Function.update (Function.update (bank.regs fs [] out) saved [])
        src (crtControlTape W fs))
      (2 ^ 10 * fs.length * (W + 4) ^ 2 + 4) := by
  exact crtRuns_mono
    (crtControlScanner_exact_runs hrg src saved hsrc hsaved hne W w hW
      wl nl acc hwl hnl hw R fs s M hfields hF hbudget)
    (crtControlScan_cost_le fs.length W w hw)

/-- Actual CRT fields can be scanned using three total-address-width blocks
plus one bit. This width also accommodates the later modular offset product. -/
theorem crtControlScanner_width_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (src saved : Fin T) (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved)
    (hne : src ≠ saved) {d : ℕ} (a s : Fin d → ℕ) (i B : ℕ) (o : List (Fin d))
    (hs : ∀ j, s j ≤ 2 ^ a j) (hB : (∑ j, a j) ≤ B) (ho : crtW a o ≤ B)
    (F w : ℕ) (hF : F < 2 ^ B) (wl nl acc : List (Fin (A + 4)))
    (hwl : wl.length = 3 * B + 1) (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (R : Regs T A) :
    let fs := crtControlFields a s i o
    let bank := crtControlConcreteBank rg src saved hsrc hsaved hne (3 * B + 1) wl nl acc R
    let out : CrtControlScanState := ⟨crtControlRemainder fs F,
      crtControlValue fs F, crtControlValid fs F⟩
    crtRuns body (crtControlScan rg (rg .wr) (rg (.z 0)) src saved (rg (.z 1)))
      (bank.regs [] fs ⟨F, 0, true⟩)
      (Function.update (Function.update (bank.regs fs [] out) saved [])
        src (crtControlTape (3 * B + 1) fs))
      (2 ^ 10 * o.length * (3 * B + 5) ^ 2 + 4) := by
  let fs := crtControlFields a s i o
  have he : (2 : ℕ) ^ (B + 1) ≤ 2 ^ (3 * B + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ (3 * B + 1) ∧
      f.bound < 2 ^ (3 * B + 1) ∧ f.weight < 2 ^ (3 * B + 1) ∧ f.weight ≤ 2 ^ B := by
    intro f hf
    have hfit := crtControlFields_fit a s hs i B o hB ho f hf
    have hweight := (crtControlFields_weight_le a s hs i o f hf).2
    exact ⟨hfit.1, hfit.2.1.trans_le he, hfit.2.2.1.trans_le he,
      hfit.2.2.2.trans_le he,
      hweight.trans (Nat.pow_le_pow_right (by decide) hB)⟩
  have hF' : F < 2 ^ (3 * B + 1) := hF.trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hbudget : 0 + F * 2 ^ B < 2 ^ (3 * B + 1) := by
    have hp := Nat.mul_lt_mul_of_pos_right hF (show 0 < (2 : ℕ) ^ B by positivity)
    have heq : (2 : ℕ) ^ B * 2 ^ B = 2 ^ (2 * B) := by
      rw [← pow_add]; congr 1; omega
    rw [heq] at hp
    have hpow : (2 : ℕ) ^ (2 * B) ≤ 2 ^ (3 * B + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    simpa only [Nat.zero_add] using hp.trans_le hpow
  have hlength : ∀ o : List (Fin d), (crtControlFields a s i o).length = o.length := by
    intro o
    induction o with
    | nil => rfl
    | cons j o ih => simpa only [crtControlFields, List.length_cons] using congrArg Nat.succ ih
  have hlen : fs.length = o.length := hlength o
  have h := crtControlScanner_runs (body := body) hrg src saved hsrc hsaved hne
    (3 * B + 1) w (by omega) wl nl acc hwl hnl hw R fs ⟨F, 0, true⟩ (2 ^ B)
    hfields hF' hbudget
  simpa only [Nat.zero_add, Bool.true_and, hlen, show 3 * B + 1 + 4 = 3 * B + 5 by omega] using h

end IntegerMultBounds.MathlibTM2.Fast
