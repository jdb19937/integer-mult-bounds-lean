module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlScanner
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlConstants
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlRotate
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlReset

/-! # One complete directly controlled CRT fiber

Scan the runtime descriptors, restore their tape, load permanent modulus and
multiplier words, then compute offsets and rotate or copy one physical fiber.
This module does not claim an outer pass over all fiber addresses.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Canonical arithmetic bank after scanning one fiber's descriptors. -/
def crtControlPassState (fs : List CrtControlField) (F : ℕ)
    (acc : List (Fin (A + 4))) : TblSt 10 A :=
  crtControlState (crtControlRemainder fs F) (crtControlValue fs F)
    (crtControlValid fs F) acc

/-- Whole-file scanner contract: permanent external registers, including the
restored descriptor tape, retain their original contents. -/
theorem crtControlScanner_frame_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (src saved : Fin T) (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved)
    (hne : src ≠ saved) {W w : ℕ} (hW : 0 < W)
    (wl nl acc : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) (fs : List CrtControlField) (F M : ℕ)
    (hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ W ∧ f.bound < 2 ^ W ∧
      f.weight < 2 ^ W ∧ f.weight ≤ M)
    (hF : F < 2 ^ W) (hbudget : F * M < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl (crtControlState F 0 true acc) r)
    (htape : R src = crtControlTape W fs) (hsave : R saved = []) :
    crtRuns body (crtControlScan rg (rg .wr) (rg (.z 0)) src saved (rg (.z 1))) R
      (crtBankOverlay rg R (tblRho W wl nl (crtControlPassState fs F acc)))
      (fs.length * ((48 * W + 56 + 13 * tblC W w) + 2) + 2 +
        (8 * fs.length * W + 2)) := by
  let bank := crtControlConcreteBank rg src saved hsrc hsaved hne W wl nl acc R
  have h := crtControlScanner_exact_runs (body := body) hrg src saved hsrc hsaved hne W w hW
    wl nl acc hwl hnl hw R fs ⟨F, 0, true⟩ M hfields hF (by simpa using hbudget)
  have hin : bank.regs [] fs ⟨F, 0, true⟩ = R := by
    funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hk
      simpa only [bank, crtControlConcreteBank, crtBankOverlay_on hrg] using (hR r).symm
    · have hk' : ∀ r, rg r ≠ k := by simpa using hk
      simp only [bank, crtControlConcreteBank, crtBankOverlay_off _ _ _ _ hk',
        crtControlTape, List.flatMap_nil]
      by_cases hs : k = saved <;> by_cases ht : k = src <;>
        simp_all [Function.update_apply, crtControlTape]
  apply crtRuns_congr (crtRuns_congr_left h hin.symm)
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    simp [crtControlConcreteBank, Function.update_of_ne (hsrc r),
      Function.update_of_ne (hsaved r), crtBankOverlay_on hrg, crtControlPassState]
  · have hk' : ∀ r, rg r ≠ k := by simpa using hk
    simp only [crtControlConcreteBank, crtBankOverlay_off _ _ _ _ hk']
    by_cases hs : k = saved <;> by_cases ht : k = src <;>
      simp_all

/-- Fixed program for one full directly controlled fiber. -/
def crtControlPass (rg : TblR 10 → Fin T) (fwd : Bool)
    (desc saved modulus multiplier ts rb str acc : Fin T) : Pr P T Q A U :=
  .seq (crtControlScan rg (rg .wr) (rg (.z 0)) desc saved (rg (.z 1)))
    (.seq (crtControlConstants rg modulus multiplier) (crtControlRotate rg fwd ts rb str acc))

/-- One fiber from its address and runtime descriptors through physical output.
The descriptor tape and permanent constants are restored; output is accumulated
in reverse as required by the surrounding streaming passes. -/
theorem crtControlPass_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (desc saved modulus multiplier ts rb str acc : Fin T)
    (hext : [desc, saved, modulus, multiplier, ts, rb, str, acc].Nodup)
    (hbank : ∀ r k, k ∈ [desc, saved, modulus, multiplier, ts, rb, str, acc] → rg r ≠ k)
    {W w : ℕ} (hW : 0 < W) (wl nl bankAcc : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (fs : List CrtControlField) (F M S μ : ℕ)
    (hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ W ∧ f.bound < 2 ^ W ∧
      f.weight < 2 ^ W ∧ f.weight ≤ M)
    (hF : F < 2 ^ W) (hbudget : F * M < 2 ^ W)
    (hS : 0 < S) (hSlt : S < 2 ^ W) (hμ : μ < 2 ^ W)
    (hprod : μ * crtControlValue fs F < 2 ^ W) (fwd : Bool)
    (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl (crtControlState F 0 true bankAcc) r)
    (htape : R desc = crtControlTape W fs) (hsave : R saved = [])
    (hmod : R modulus = binSyms W S) (hmul : R multiplier = binSyms W μ)
    (sl : List (List (Fin (A + 4)))) (hsl : ∀ x ∈ sl, x.length = (R rb).length)
    (hlen : sl.length = S + (R ts).length)
    (rest : List (Fin (A + 4))) (hsource : R str = sl.flatten ++ rest) :
    ∃ st' : TblSt 10 A,
      st'.val 3 = μ * crtControlValue fs F % S ∧
      st'.val 4 = S - μ * crtControlValue fs F % S ∧
      (∀ j, j ≠ 3 → j ≠ 4 → st'.val j =
        (crtControlConstantsState S μ (crtControlPassState fs F bankAcc)).val j) ∧
      st'.acc = bankAcc ∧
      crtRuns body (crtControlPass rg fwd desc saved modulus multiplier ts rb str acc) R
        (Function.update (Function.update (crtBankOverlay rg R (tblRho W wl nl st')) str rest)
          acc ((if crtControlValid fs F then (sl.take S).rotate
            (crtControlShift fwd S μ (crtControlValue fs F)) ++ sl.drop S
            else sl).flatten.reverse ++ R acc))
        (fs.length * ((48 * W + 56 + 13 * tblC W w) + 2) + 2 +
          (8 * fs.length * W + 2) + (16 * W + 16) +
          (3 * tblC W w + W * (4 * S + 22) + 4 * S +
            sl.length * (8 * (R rb).length + 9) + 34)) := by
  have hd : ∀ r, rg r ≠ desc := fun r => hbank r _ (by simp)
  have hs : ∀ r, rg r ≠ saved := fun r => hbank r _ (by simp)
  have hm : ∀ r, rg r ≠ modulus := fun r => hbank r _ (by simp)
  have hmu : ∀ r, rg r ≠ multiplier := fun r => hbank r _ (by simp)
  have ht : ∀ r, rg r ≠ ts := fun r => hbank r _ (by simp)
  have hb : ∀ r, rg r ≠ rb := fun r => hbank r _ (by simp)
  have hstr : ∀ r, rg r ≠ str := fun r => hbank r _ (by simp)
  have ha : ∀ r, rg r ≠ acc := fun r => hbank r _ (by simp)
  have hds : desc ≠ saved := by
    have h := (List.nodup_cons.mp hext).1
    intro hds; apply h; simp [hds]
  have hphysical : [ts, rb, str, acc].Nodup := by
    exact (List.nodup_cons.mp (List.nodup_cons.mp
      (List.nodup_cons.mp (List.nodup_cons.mp hext).2).2).2).2
  let scanned := crtControlPassState fs F bankAcc
  let R₁ := crtBankOverlay rg R (tblRho W wl nl scanned)
  have hscan := crtControlScanner_frame_runs (body := body) hrg desc saved hd hs hds hW
    wl nl bankAcc hwl hnl hw fs F M hfields hF hbudget R hR htape hsave
  have hR₁ : ∀ r, R₁ (rg r) = tblRho W wl nl scanned r := by
    intro r; exact crtBankOverlay_on hrg _ _ _
  have hload := crtControlConstants_runs (body := body) hrg modulus multiplier hm hmu
    W S μ wl nl hwl scanned R₁ hR₁
    (by simpa only [R₁, crtBankOverlay_off _ _ _ _ hm] using hmod)
    (by simpa only [R₁, crtBankOverlay_off _ _ _ _ hmu] using hmul)
  let R₂ := crtControlConstantsRegs rg W S μ R₁
  let loaded := crtControlConstantsState S μ scanned
  have hR₂ : ∀ r, R₂ (rg r) = tblRho W wl nl loaded r :=
    crtControlConstantsRegs_bank hrg W S μ wl nl scanned R₁ hR₁
  have hoff : ∀ k, (∀ r, rg r ≠ k) → R₂ k = R k := by
    intro k hk
    simp only [R₂, crtControlConstantsRegs, Function.update_of_ne (Ne.symm (hk (.v 2))),
      Function.update_of_ne (Ne.symm (hk (.v 1))), R₁, crtBankOverlay_off _ _ _ _ hk]
  have hweights : ∀ f ∈ fs, 0 < f.place ∧ f.weight ≤ M := by
    intro f hf; exact ⟨(hfields f hf).1, (hfields f hf).2.2.2.2⟩
  have hK : crtControlValue fs F < 2 ^ W :=
    (crtControlValue_le_mul fs F M hweights).trans_lt hbudget
  have hrem : crtControlRemainder fs F < 2 ^ W := by
    have h := (crtControlScan_fold_budget fs ⟨F, 0, true⟩ M hweights).1
    rw [crtControlScan_fold] at h
    exact h.trans_lt hF
  have hone : 1 < (2 : ℕ) ^ W := by
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
    norm_num at hp; omega
  have hfit : ∀ j, loaded.val j < 2 ^ W := by
    intro j
    simp only [loaded, scanned, crtControlConstantsState, crtControlPassState,
      crtControlState, Function.update_apply]
    split_ifs <;> omega
  have hsval : loaded.val 1 = S := by simp [loaded, crtControlConstantsState]
  have hmuval : loaded.val 2 = μ := by simp [loaded, crtControlConstantsState]
  have hkval : loaded.val 5 = crtControlValue fs F := by
    simp [loaded, scanned, crtControlConstantsState, crtControlPassState, crtControlState]
  obtain ⟨st', hlo, hhi, hpres, hstateacc, hrotate⟩ := crtControlRotate_runs (body := body)
    hrg ts rb str acc hphysical ht hb hstr ha hW wl nl hwl hnl hw loaded hfit
    (by simpa only [hsval] using hS) (by simpa only [hmuval, hkval] using hprod)
    (crtControlValid fs F) fwd
    (by simp [loaded, scanned, crtControlConstantsState, crtControlPassState, crtControlState])
    R₂ hR₂ sl (by simpa only [hoff rb hb] using hsl)
    (by simpa only [hsval, hoff ts ht] using hlen)
    rest (by simpa only [hoff str hstr] using hsource)
  refine ⟨st', ?_, ?_, hpres, hstateacc, ?_⟩
  · simpa only [hmuval, hkval, hsval] using hlo
  · simpa only [hmuval, hkval, hsval] using hhi
  · have ho : crtBankOverlay rg R₂ (tblRho W wl nl st') =
        crtBankOverlay rg R (tblRho W wl nl st') := by
      funext k
      by_cases hk : ∃ r, rg r = k
      · obtain ⟨r, rfl⟩ := hk; simp only [crtBankOverlay_on hrg]
      · have hk' : ∀ r, rg r ≠ k := by simpa using hk
        simp only [crtBankOverlay_off _ _ _ _ hk', hoff k hk']
    simp only [hsval, hmuval, hkval, hoff rb hb, hoff acc ha, ho] at hrotate
    exact crtRuns_mono (crtRuns_seq hscan (crtRuns_seq hload hrotate)) (by omega)

/-- Reset after a complete fiber so the next indexed address can be loaded
into a canonical bank. The residual decoded address is preserved. -/
def crtControlPassReset (rg : TblR 10 → Fin T) (fwd : Bool)
    (desc saved modulus multiplier ts rb str acc : Fin T) : Pr P T Q A U :=
  .seq (crtControlPass rg fwd desc saved modulus multiplier ts rb str acc)
    (tblCompile rg crtControlReset)

/-- Complete one fiber and restore the canonical live bank, including an empty
weighted sum and a true validity flag. All external changes are still exactly
the consumed source fiber and its reversed output on the accumulator. -/
theorem crtControlPassReset_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (desc saved modulus multiplier ts rb str acc : Fin T)
    (hext : [desc, saved, modulus, multiplier, ts, rb, str, acc].Nodup)
    (hbank : ∀ r k, k ∈ [desc, saved, modulus, multiplier, ts, rb, str, acc] → rg r ≠ k)
    {W w : ℕ} (hW : 0 < W) (wl nl bankAcc : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (fs : List CrtControlField) (F M S μ : ℕ)
    (hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ W ∧ f.bound < 2 ^ W ∧
      f.weight < 2 ^ W ∧ f.weight ≤ M)
    (hF : F < 2 ^ W) (hbudget : F * M < 2 ^ W)
    (hS : 0 < S) (hSlt : S < 2 ^ W) (hμ : μ < 2 ^ W)
    (hprod : μ * crtControlValue fs F < 2 ^ W) (fwd : Bool)
    (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl (crtControlState F 0 true bankAcc) r)
    (htape : R desc = crtControlTape W fs) (hsave : R saved = [])
    (hmod : R modulus = binSyms W S) (hmul : R multiplier = binSyms W μ)
    (sl : List (List (Fin (A + 4)))) (hsl : ∀ x ∈ sl, x.length = (R rb).length)
    (hlen : sl.length = S + (R ts).length)
    (rest : List (Fin (A + 4))) (hsource : R str = sl.flatten ++ rest) :
    crtRuns body (crtControlPassReset rg fwd desc saved modulus multiplier ts rb str acc) R
      (Function.update (Function.update (crtBankOverlay rg R
        (tblRho W wl nl (crtControlState (crtControlRemainder fs F) 0 true bankAcc))) str rest)
        acc ((if crtControlValid fs F then (sl.take S).rotate
          (crtControlShift fwd S μ (crtControlValue fs F)) ++ sl.drop S
          else sl).flatten.reverse ++ R acc))
      (fs.length * ((48 * W + 56 + 13 * tblC W w) + 2) + 2 +
        (8 * fs.length * W + 2) + (16 * W + 16) +
        (3 * tblC W w + W * (4 * S + 22) + 4 * S +
          sl.length * (8 * (R rb).length + 9) + 34) + 10 * tblC W w) := by
  obtain ⟨st', hlo, hhi, hpres, hstateacc, hpass⟩ := crtControlPass_runs (body := body)
    hrg desc saved modulus multiplier ts rb str acc hext hbank hW wl nl bankAcc hwl hnl hw
    fs F M S μ hfields hF hbudget hS hSlt hμ hprod fwd R hR htape hsave hmod hmul
    sl hsl hlen rest hsource
  have hstr : ∀ r, rg r ≠ str := fun r => hbank r _ (by simp)
  have ha : ∀ r, rg r ≠ acc := fun r => hbank r _ (by simp)
  let out := (if crtControlValid fs F then (sl.take S).rotate
    (crtControlShift fwd S μ (crtControlValue fs F)) ++ sl.drop S else sl).flatten
  let R₃ := Function.update (Function.update (crtBankOverlay rg R (tblRho W wl nl st')) str rest)
    acc (out.reverse ++ R acc)
  have hR₃ : ∀ r, R₃ (rg r) = tblRho W wl nl st' r := by
    intro r
    simp only [R₃, Function.update_of_ne (ha r), Function.update_of_ne (hstr r),
      crtBankOverlay_on hrg]
  have hweights : ∀ f ∈ fs, 0 < f.place ∧ f.weight ≤ M := by
    intro f hf; exact ⟨(hfields f hf).1, (hfields f hf).2.2.2.2⟩
  have hK : crtControlValue fs F < 2 ^ W :=
    (crtControlValue_le_mul fs F M hweights).trans_lt hbudget
  have hrem : crtControlRemainder fs F < 2 ^ W := by
    have h := (crtControlScan_fold_budget fs ⟨F, 0, true⟩ M hweights).1
    rw [crtControlScan_fold] at h
    exact h.trans_lt hF
  have hone : 1 < (2 : ℕ) ^ W := by
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
    norm_num at hp; omega
  have hfit : ∀ j, st'.val j < 2 ^ W := by
    intro j
    by_cases h3 : j = 3
    · subst j; rw [hlo]; exact (Nat.mod_lt _ hS).trans hSlt
    by_cases h4 : j = 4
    · subst j; rw [hhi]; exact (Nat.sub_le _ _).trans_lt hSlt
    rw [hpres j h3 h4]
    simp only [crtControlConstantsState, crtControlPassState, crtControlState,
      Function.update_apply]
    split_ifs <;> omega
  have hzero : st'.val 0 = crtControlRemainder fs F := by
    simpa [crtControlConstantsState, crtControlPassState, crtControlState] using
      hpres 0 (by decide) (by decide)
  have hreset := crtControlReset_runs (body := body) hrg hW wl nl hwl hnl hw st' hfit R₃ hR₃
  rw [hzero, hstateacc] at hreset
  apply crtRuns_congr (crtRuns_seq hpass hreset)
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    simp only [crtBankOverlay_on hrg, Function.update_of_ne (ha r),
      Function.update_of_ne (hstr r)]
  · have hk' : ∀ r, rg r ≠ k := by simpa using hk
    simp only [crtBankOverlay_off _ _ _ _ hk', R₃, Function.update_apply]
    split_ifs <;> simp_all [out]

end IntegerMultBounds.MathlibTM2.Fast
