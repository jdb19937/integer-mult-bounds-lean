module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerate
public import IntegerMultBounds.MathlibTM2.Fast.CRTDrive

/-! # Runtime traversal for descriptor production -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Read a preserved unary input into one fixed-width binary bank variable. -/
def crtControlReadUnary (rg : TblR 10 → Fin T) (src saved : Fin T) (j : Fin 10) :
    Pr P T Q A U :=
  .seq (tblCompile rg (.ins (.zero j)))
    (crtFor src saved (tblCompile rg (.ins (.inc j))))

theorem crtControlReadUnary_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (src saved : Fin T) (hne : src ≠ saved)
    (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved)
    (j : Fin 10) {W w n : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ k, st.val k < 2 ^ W) (hn : n < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r)
    (hlen : (R src).length = n) (hempty : R saved = []) :
    crtRuns body (crtControlReadUnary rg src saved j) R
      (crtBankOverlay rg R (tblRho W wl nl ⟨Function.update st.val j n, st.acc⟩))
      (tblC W w + (n * (tblC W w + 3) + 2 * n + 4)) := by
  let state (k : ℕ) : TblSt 10 A := ⟨Function.update st.val j k, st.acc⟩
  let Ψ (k : ℕ) := crtBankOverlay rg R (tblRho W wl nl (state k))
  have ho : ∀ k r, (∀ b, rg b ≠ r) → Ψ k r = R r := fun k r h =>
    crtBankOverlay_off _ _ _ _ h
  have hzdo := TblDo.insX (.zero j) (st := st) (A := A) (W := W) (w := w)
    trivial (P := fun s => s = state 0) rfl
  obtain ⟨st₀, hst₀, hz⟩ := hzdo.host (body := body) hrg wl nl hwl hnl hw hst
  subst st₀
  have hz' : crtRuns body (tblCompile rg (.ins (.zero j))) R (Ψ 0) (tblC W w) := by
    simpa only [Nat.one_mul] using crtRuns_of_tbl hrg hz R hR
  have hiter : crtIter (body := body) (tblCompile rg (.ins (.inc j))) src saved Ψ (tblC W w) n := by
    intro k hk Rk hkeep
    have hRk : ∀ r, Rk (rg r) = tblRho W wl nl (state k) r := by
      intro r
      rw [hkeep _ (hsrc r) (hsaved r)]
      exact crtBankOverlay_on hrg _ _ r
    have hfit : (state k).val j + 1 < 2 ^ W := by simp [state]; omega
    have hstate : ∀ r, (state k).val r < 2 ^ W := by
      intro r
      by_cases hr : r = j
      · subst r; simp [state]; omega
      · simpa [state, hr] using hst r
    have hstep := TblDo.insX (.inc j) (st := state k) (A := A) (W := W) (w := w)
      hfit (P := fun s => s = state (k + 1)) (by simp [state, TblIns.exact])
    obtain ⟨st', hst', hs⟩ := hstep.host (body := body) hrg wl nl hwl hnl hw hstate
    subst st'
    have hrun := crtRuns_of_tbl hrg hs Rk hRk
    apply crtRuns_congr (by simpa only [Nat.one_mul] using hrun)
    funext r
    by_cases hr : ∃ b, rg b = r
    · obtain ⟨b, rfl⟩ := hr
      simp [crtBankOverlay_on hrg, hsrc b, hsaved b, Ψ]
    · have hr' : ∀ b, rg b ≠ r := by simpa using hr
      rw [crtBankOverlay_off _ _ _ _ hr']
      by_cases hrs : r = saved
      · simp [hrs]
      · by_cases hrr : r = src
        · simp [hrr]
        · simp [hrs, hrr, hkeep r hrr hrs, ho _ r hr']
  have hf := crtFor_runs hne hiter (R src) hlen
  have hframe : ∀ k, crtForRegs src saved (Ψ k) (R src) [] = Ψ k := by
    intro k
    funext r
    by_cases hrs : r = saved
    · subst r; simp [crtForRegs, hne.symm, ho _ _ hsaved, hempty]
    · by_cases hrr : r = src
      · subst r; simp [crtForRegs, ho _ _ hsrc]
      · simp [crtForRegs, hrs, hrr]
  rw [hframe, hframe] at hf
  exact crtRuns_seq hz' hf

/-- Prepend one packet in order, then release its transient packet register. -/
def crtControlEmitAndClear (packet dst t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bcopy packet dst t₁ t₂) (uclear packet)

theorem crtControlEmitAndClear_runs {packet dst t₁ t₂ : Fin T}
    (hreg : [packet, dst, t₁, t₂].Nodup) (R : Regs T A)
    (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) :
    crtRuns body (crtControlEmitAndClear packet dst t₁ t₂) R
      (Function.update (Function.update R dst (R packet ++ R dst)) packet [])
      (8 * (R packet).length + 8) := by
  have hreg' := hreg
  regs_ne hreg'
  have hb := crtBcopy_runs (body := body) hreg R ht₁ ht₂
  have hc := crtClear_runs (body := body) packet
    (Function.update R dst (R packet ++ R dst))
  apply crtRuns_mono (crtRuns_seq hb hc)
  rw [Function.update_of_ne ‹packet ≠ dst›]
  omega

/-- At the target, discard its packet and insert the deferred zero packet.
The deferred packet is stored reversed, so one move inserts it in order. -/
def crtControlInsertZero (packet zero dst past : Fin T) : Pr P T Q A U :=
  .seq (uclear packet) (.seq (crtMv zero dst) (crtPush past tick))

def crtControlInsertZeroRegs (packet zero dst past : Fin T) (R : Regs T A) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update R packet [])
    zero []) dst ((R zero).reverse ++ R dst)) past (tick :: R past)

theorem crtControlInsertZero_runs {packet zero dst past : Fin T}
    (hreg : [packet, zero, dst, past].Nodup) (R : Regs T A) :
    crtRuns body (crtControlInsertZero packet zero dst past) R
      (crtControlInsertZeroRegs packet zero dst past R)
      (2 * (R packet).length + 2 * (R zero).length + 5) := by
  have hreg' := hreg
  regs_ne hreg'
  have hc := crtClear_runs (body := body) packet R
  let R₁ := Function.update R packet []
  have hm := crtMv_runs (body := body) ‹zero ≠ dst› R₁
  let R₂ := Function.update (Function.update R₁ zero []) dst ((R₁ zero).reverse ++ R₁ dst)
  have hp := crtPush_runs (body := body) past tick R₂
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq hc (crtRuns_seq hm hp)) ?_) ?_
  · simp [R₂, R₁, crtControlInsertZeroRegs, Ne.symm ‹packet ≠ zero›,
      Ne.symm ‹packet ≠ dst›, Ne.symm ‹packet ≠ past›, Ne.symm ‹zero ≠ past›,
      Ne.symm ‹dst ≠ past›]
  · simp [R₁, Ne.symm ‹packet ≠ zero›]; omega

/-- Runtime selection: before the target, defer the first (zero) packet;
at the target, insert that deferred packet; afterwards emit every packet.
`seen` is the saved width-entry stack, so even a zero-width first entry makes
it nonempty. `left` counts axes remaining before the target. -/
def crtControlSelectPacket (left seen past packet zero dst t₁ t₂ : Fin T) : Pr P T Q A U :=
  crtIfR left
    (crtIfR seen (crtControlEmitAndClear packet dst t₁ t₂) (crtMv packet zero))
    (crtIfR past (crtControlEmitAndClear packet dst t₁ t₂)
      (crtControlInsertZero packet zero dst past))

def crtControlSelectRegs (left seen past packet zero dst : Fin T) (R : Regs T A) : Regs T A :=
  if R left = [] then
    if R past = [] then crtControlInsertZeroRegs packet zero dst past R
    else Function.update (Function.update R dst (R packet ++ R dst)) packet []
  else
    if R seen = [] then Function.update (Function.update R packet []) zero ((R packet).reverse ++ R zero)
    else Function.update (Function.update R dst (R packet ++ R dst)) packet []

theorem crtControlSelectPacket_runs {left seen past packet zero dst t₁ t₂ : Fin T}
    (hreg : [left, seen, past, packet, zero, dst, t₁, t₂].Nodup)
    (R : Regs T A) (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) :
    crtRuns body (crtControlSelectPacket left seen past packet zero dst t₁ t₂) R
      (crtControlSelectRegs left seen past packet zero dst R)
      (8 * (R packet).length + 2 * (R zero).length + 12) := by
  have hreg' := hreg
  regs_ne hreg'
  have he := crtControlEmitAndClear_runs (body := body)
    (packet := packet) (dst := dst) (t₁ := t₁) (t₂ := t₂) (by regs_nodup) R ht₁ ht₂
  have hz := crtControlInsertZero_runs (body := body)
    (packet := packet) (zero := zero) (dst := dst) (past := past) (by regs_nodup) R
  have hm := crtMv_runs (body := body) ‹packet ≠ zero› R
  unfold crtControlSelectPacket
  apply crtIfR_runs
  · intro hl
    apply crtIfR_runs
    · intro hs
      simpa [crtControlSelectRegs, hl, hs] using crtRuns_mono he
        (show 8 * (R packet).length + 8 ≤ 8 * (R packet).length + 2 * (R zero).length + 8 by omega)
    · intro hs
      simpa [crtControlSelectRegs, hl, hs] using crtRuns_mono hm
        (show 2 * (R packet).length + 2 ≤ 8 * (R packet).length + 2 * (R zero).length + 8 by omega)
  · intro hl
    apply crtIfR_runs
    · intro hp
      simpa [crtControlSelectRegs, hl, hp] using crtRuns_mono he
        (show 8 * (R packet).length + 8 ≤ 8 * (R packet).length + 2 * (R zero).length + 8 by omega)
    · intro hp
      simpa [crtControlSelectRegs, hl, hp] using crtRuns_mono hz
        (show 2 * (R packet).length + 2 * (R zero).length + 5 ≤
          8 * (R packet).length + 2 * (R zero).length + 8 by omega)

/-- Registers outside the selector's four outputs are untouched. -/
lemma crtControlSelectRegs_off (left seen past packet zero dst : Fin T)
    (R : Regs T A) (r : Fin T) (hp : r ≠ packet) (hz : r ≠ zero)
    (hd : r ≠ dst) (ht : r ≠ past) :
    crtControlSelectRegs left seen past packet zero dst R r = R r := by
  unfold crtControlSelectRegs
  split_ifs <;> simp [crtControlInsertZeroRegs, hp, hz, hd, ht]

private lemma crtGenerate_overlay_twice {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (R : Regs T A) (ρ σ : TblR 10 → List (Fin (A + 4))) :
    crtBankOverlay rg (crtBankOverlay rg R ρ) σ = crtBankOverlay rg R σ := by
  funext r
  by_cases hr : ∃ j, rg j = r
  · obtain ⟨j, rfl⟩ := hr; simp [crtBankOverlay_on hrg]
  · have h : ∀ j, rg j ≠ r := by simpa using hr
    simp [crtBankOverlay_off _ _ _ _ h]

private lemma crtGenerate_state_fit {W : ℕ} (hW : 0 < W) (st : TblSt 10 A)
    (hst : ∀ j, st.val j < 2 ^ W) :
    ∀ j, (crtControlGeneratedState st).val j < 2 ^ W := by
  intro j
  have h1 : 1 < 2 ^ W := Nat.one_lt_two_pow hW.ne'
  by_cases hj7 : j = 7
  · subst j
    simp only [crtControlGeneratedState, Function.update_self, crtControlGeneratedField]
    split_ifs <;> apply lt_of_le_of_lt (Nat.div_le_self _ _) <;> apply hst
  · by_cases hj8 : j = 8
    · subst j
      simp [crtControlGeneratedState]
      split_ifs <;> omega
    · simpa [crtControlGeneratedState, hj7, hj8] using hst j

/-- The arithmetic and target-selection part of one traversal step. -/
def crtControlGenerateSelect (rg : TblR 10 → Fin T)
    (left seen past packet zero dst : Fin T) : Pr P T Q A U :=
  .seq (crtControlGeneratePacket rg packet)
    (.seq (crtControlSelectPacket left seen past packet zero dst (rg (.z 0)) (rg (.z 1)))
      (.seq (tblCompile rg crtControlAdvanceWeight) (tblCompile rg (.ins (.inc 0)))))

def crtControlGenerateNextState (st : TblSt 10 A) : TblSt 10 A :=
  let t := crtControlGeneratedState st
  ⟨Function.update (Function.update t.val 6 (st.val 6 * st.val 5)) 0 (st.val 0 + 1), t.acc⟩

noncomputable def crtControlGenerateSelectRegs (rg : TblR 10 → Fin T)
    (left seen past packet zero dst : Fin T) (W : ℕ)
    (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A) : Regs T A :=
  let R₁ := Function.update (crtBankOverlay rg R (tblRho W wl nl (crtControlGeneratedState st)))
    packet (crtControlPacket W (crtControlGeneratedField st) ++ R packet)
  crtBankOverlay rg (crtControlSelectRegs left seen past packet zero dst R₁)
    (tblRho W wl nl (crtControlGenerateNextState st))

theorem crtControlGenerateSelect_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (left seen past packet zero dst : Fin T)
    (hreg : [left, seen, past, packet, zero, dst].Nodup)
    (hdisj : ∀ j, ∀ r ∈ [left, seen, past, packet, zero, dst], rg j ≠ r)
    {W w : ℕ} (hW : 0 < W) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (hweight : st.val 6 * st.val 5 < 2 ^ W) (hindex : st.val 0 + 1 < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r)
    (hp : R packet = []) :
    crtRuns body (crtControlGenerateSelect rg left seen past packet zero dst) R
      (crtControlGenerateSelectRegs rg left seen past packet zero dst W wl nl st R)
      (7 * tblC W w + 56 * W + 2 * (R zero).length + 36) := by
  have hreg' := hreg
  regs_ne hreg'
  have hd : ∀ j, rg j ≠ packet := fun j => hdisj j packet (by simp)
  have hz : ∀ j, rg j ≠ zero := fun j => hdisj j zero (by simp)
  have hdst : ∀ j, rg j ≠ dst := fun j => hdisj j dst (by simp)
  have hpa : ∀ j, rg j ≠ past := fun j => hdisj j past (by simp)
  let t := crtControlGeneratedState st
  let R₁ := Function.update (crtBankOverlay rg R (tblRho W wl nl t)) packet
    (crtControlPacket W (crtControlGeneratedField st) ++ R packet)
  have hg := crtControlGeneratePacket_runs (body := body) hrg packet hd hW wl nl hwl hnl hw st hst R hR
  have hbank₁ : ∀ j, R₁ (rg j) = tblRho W wl nl t j := by
    intro j; simp [R₁, hd j, crtBankOverlay_on hrg]
  have hreg₁ : [left, seen, past, packet, zero, dst, rg (.z 0), rg (.z 1)].Nodup := by
    rw [show [left, seen, past, packet, zero, dst, rg (.z 0), rg (.z 1)] =
      [left, seen, past, packet, zero, dst] ++ [rg (.z 0), rg (.z 1)] from rfl,
      List.nodup_append]
    refine ⟨hreg, by simp [hrg.eq_iff], ?_⟩
    intro r hr b hb he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hdisj (.z 0) r hr he.symm
    · exact hdisj (.z 1) r hr he.symm
  have hs := crtControlSelectPacket_runs (body := body) hreg₁ R₁
    (by rw [hbank₁]; rfl) (by rw [hbank₁]; rfl)
  let R₂ := crtControlSelectRegs left seen past packet zero dst R₁
  have hbank₂ : ∀ j, R₂ (rg j) = tblRho W wl nl t j := by
    intro j
    dsimp only [R₂]
    rw [crtControlSelectRegs_off _ _ _ _ _ _ _ _ (hd j) (hz j) (hdst j) (hpa j), hbank₁]
  have ht : ∀ j, t.val j < 2 ^ W := crtGenerate_state_fit hW st hst
  have hwt : t.val 6 * t.val 5 < 2 ^ W := by
    simpa [t, crtControlGeneratedState] using hweight
  have hm := crtControlAdvanceWeight_runs (body := body) hrg wl nl hwl hnl hw t ht hwt R₂ hbank₂
  let u : TblSt 10 A := ⟨Function.update t.val 6 (t.val 6 * t.val 5), t.acc⟩
  let R₃ := crtBankOverlay rg R₂ (tblRho W wl nl u)
  have hu : ∀ j, u.val j < 2 ^ W := by
    intro j
    by_cases hj : j = 6
    · subst j; simpa [u] using hwt
    · simpa [u, hj] using ht j
  have hi := TblDo.insX (.inc 0) (st := u) (A := A) (W := W) (w := w)
    (by simpa [u, t, crtControlGeneratedState, TblIns.fits] using hindex)
    (P := fun v => v = (.inc 0 : TblIns 10).exact A w u) rfl
  obtain ⟨v, hv, hr⟩ := hi.host (body := body) hrg wl nl hwl hnl hw hu
  subst v
  have hr' := crtRuns_of_tbl hrg hr R₃ (fun j => crtBankOverlay_on hrg _ _ j)
  have hout : crtBankOverlay rg R₃ (tblRho W wl nl ((.inc 0 : TblIns 10).exact A w u)) =
      crtControlGenerateSelectRegs rg left seen past packet zero dst W wl nl st R := by
    rw [crtGenerate_overlay_twice hrg]
    congr 1
  rw [hout] at hr'
  refine crtRuns_mono (crtRuns_seq hg (crtRuns_seq hs (crtRuns_seq hm hr'))) ?_
  have hpacket : (R₁ packet).length = 4 * W := by simp [R₁, hp]
  have hzero : R₁ zero = R zero := by
    simp [R₁, Ne.symm ‹packet ≠ zero›, crtBankOverlay_off _ _ _ _ hz]
  rw [hpacket, hzero]
  omega

/-- Load the modulus and refresh the original lower-width power from unary
runtime registers, preserving both unary sources. -/
def crtControlPrepareAxis (rg : TblR 10 → Fin T) (modulus lower pad tmp : Fin T) :
    Pr P T Q A U :=
  .seq (crtControlReadUnary rg modulus pad 5)
    (.seq (uclear (rg (.v 2)))
      (crtControlPow2 (rg .wr) lower (rg (.v 2)) pad tmp))

def crtControlPreparedState (st : TblSt 10 A) (b e : ℕ) : TblSt 10 A :=
  ⟨Function.update (Function.update st.val 5 b) 2 (2 ^ e), st.acc⟩

theorem crtControlPrepareAxis_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (modulus lower pad tmp : Fin T)
    (hreg : [modulus, lower, pad, tmp].Nodup)
    (hdisj : ∀ j, ∀ r ∈ [modulus, lower, pad, tmp], rg j ≠ r)
    {W w b e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W) (hb : b < 2 ^ W) (he : e < W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r)
    (hmod : (R modulus).length = b) (hlower : (R lower).length = e)
    (hpad : R pad = []) (htmp : R tmp = []) :
    crtRuns body (crtControlPrepareAxis rg modulus lower pad tmp) R
      (crtBankOverlay rg R (tblRho W wl nl (crtControlPreparedState st b e)))
      (tblC W w + (b * (tblC W w + 3) + 2 * b + 4) +
        (2 * W + 2) + (10 * W + 8 * e + 24)) := by
  have hreg' := hreg
  regs_ne hreg'
  have hm : ∀ j, rg j ≠ modulus := fun j => hdisj j _ (by simp)
  have hl : ∀ j, rg j ≠ lower := fun j => hdisj j _ (by simp)
  have hp : ∀ j, rg j ≠ pad := fun j => hdisj j _ (by simp)
  have ht : ∀ j, rg j ≠ tmp := fun j => hdisj j _ (by simp)
  have h₁ := crtControlReadUnary_runs (body := body) hrg modulus pad ‹modulus ≠ pad›
    hm hp 5 wl nl hwl hnl hw st hst hb R hR hmod hpad
  let t : TblSt 10 A := ⟨Function.update st.val 5 b, st.acc⟩
  let R₁ := crtBankOverlay rg R (tblRho W wl nl t)
  have h₂ := crtClear_runs (body := body) (rg (.v 2)) R₁
  let R₂ := Function.update R₁ (rg (.v 2)) []
  have h₃ := crtControlPow2_runs (body := body) (width := rg .wr)
    (exponent := lower) (dst := rg (.v 2)) (pad := pad) (tmp := tmp)
    (by simp [List.nodup_cons, hrg.eq_iff, hl, hp, ht,
      Ne.symm (hl (.v 2)), ‹lower ≠ pad›, ‹lower ≠ tmp›, ‹pad ≠ tmp›])
    R₂ W e (by simp [R₂, R₁, hrg.eq_iff, crtBankOverlay_on hrg, tblRho, hwl])
    (by simp [R₂, R₁, Ne.symm (hl (.v 2)), crtBankOverlay_off _ _ _ _ hl, hlower])
    he (by simp [R₂])
    (by simp [R₂, R₁, Ne.symm (hp (.v 2)), crtBankOverlay_off _ _ _ _ hp, hpad])
    (by simp [R₂, R₁, Ne.symm (ht (.v 2)), crtBankOverlay_off _ _ _ _ ht, htmp])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ h₃)) ?_) ?_
  · funext r
    by_cases hr : ∃ j, rg j = r
    · obtain ⟨j, rfl⟩ := hr
      cases j <;> simp [R₂, R₁, crtBankOverlay_on hrg, hrg.eq_iff, tblRho,
        crtControlPreparedState, t, Function.update_apply]
      split_ifs <;> rfl
    · have hr' : ∀ j, rg j ≠ r := by simpa using hr
      simp [R₂, R₁, Ne.symm (hr' (.v 2)), crtBankOverlay_off _ _ _ _ hr']
  · have hlen : (R₁ (rg (.v 2))).length = W := by
      simp [R₁, crtBankOverlay_on hrg, tblRho]
    rw [hlen]
    omega

/-- All external registers except packet/zero/output/past are framed by the
concrete generate-select-arithmetic sequence. -/
lemma crtControlGenerateSelectRegs_off (rg : TblR 10 → Fin T)
    (left seen past packet zero dst : Fin T) (W : ℕ)
    (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A)
    (r : Fin T) (hdisj : ∀ j, rg j ≠ r)
    (hp : r ≠ packet) (hz : r ≠ zero) (hd : r ≠ dst) (ht : r ≠ past) :
    crtControlGenerateSelectRegs rg left seen past packet zero dst W wl nl st R r = R r := by
  unfold crtControlGenerateSelectRegs
  rw [crtBankOverlay_off _ _ _ _ hdisj,
    crtControlSelectRegs_off _ _ _ _ _ _ _ _ hp hz hd ht,
    Function.update_of_ne hp, crtBankOverlay_off _ _ _ _ hdisj]

/-- One concrete runtime axis operation. The width and modulus entry streams
are consumed in lockstep and saved as entries for final restoration. -/
def crtControlGenerateAxis (rg : TblR 10 → Fin T)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T) : Pr P T Q A U :=
  .seq (crtPopEnt widths axisWidth) <|
  .seq (crtPopEnt moduli axisModulus) <|
  .seq (crtControlPrepareAxis rg axisModulus lower pad tmp) <|
  .seq (crtControlGenerateSelect rg left savedWidths past packet zero dst) <|
  .seq (ucopy axisWidth lower tmp) <|
  .seq (crtPop left) <|
  .seq (crtPushEnt axisWidth savedWidths) (crtPushEnt axisModulus savedModuli)

def crtControlPoppedRegs (widths moduli axisWidth axisModulus : Fin T)
    (R : Regs T A) (a b : ℕ) (as bs : List ℕ) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update R widths (crtEnts as))
    axisWidth (List.replicate a tick)) moduli (crtEnts bs)) axisModulus (List.replicate b tick)

noncomputable def crtControlGenerateAxisRegs (rg : TblR 10 → Fin T)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst : Fin T) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) (R : Regs T A) (a b e : ℕ) (as bs : List ℕ) : Regs T A :=
  let Rp := crtControlPoppedRegs widths moduli axisWidth axisModulus R a b as bs
  let t := crtControlPreparedState st b e
  let Rq := crtBankOverlay rg Rp (tblRho W wl nl t)
  let Rs := crtControlGenerateSelectRegs rg left savedWidths past packet zero dst W wl nl t Rq
  let R₁ := Function.update Rs lower (List.replicate a tick ++ Rs lower)
  let R₂ := Function.update R₁ left (R₁ left).tail
  let R₃ := Function.update (Function.update R₂ axisWidth []) savedWidths (crtEnt a ++ R₂ savedWidths)
  Function.update (Function.update R₃ axisModulus []) savedModuli (crtEnt b ++ R₃ savedModuli)

def crtControlGenerateAxisCost (W w a b e z : ℕ) : ℕ :=
  (2 * a + 4) + (2 * b + 4) +
    (tblC W w + (b * (tblC W w + 3) + 2 * b + 4) + (2 * W + 2) + (10 * W + 8 * e + 24)) +
    (7 * tblC W w + 56 * W + 2 * z + 36) + (4 * a + 4) + 1 + (2 * a + 4) + (2 * b + 4)

/-- Concrete one-axis contract: no assumed arithmetic or packet-processing
oracle. This reads both unary entries, generates/selects the packet, advances
the original binary weight/index, and preserves both entries on saved stacks. -/
theorem crtControlGenerateAxis_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T)
    (hreg : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus, lower, left,
      past, packet, zero, dst, pad, tmp].Nodup)
    (hdisj : ∀ j, ∀ r ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst, pad, tmp], rg j ≠ r)
    {W w : ℕ} (hW : 0 < W) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (a b e : ℕ) (as bs : List ℕ) (hb : b < 2 ^ W) (he : e < W)
    (hweight : st.val 6 * b < 2 ^ W) (hindex : st.val 0 + 1 < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r)
    (hwidths : R widths = crtEnts (a :: as)) (hmoduli : R moduli = crtEnts (b :: bs))
    (haw : R axisWidth = []) (ham : R axisModulus = [])
    (hlower : (R lower).length = e) (hpacket : R packet = [])
    (hpad : R pad = []) (htmp : R tmp = []) :
    crtRuns body (crtControlGenerateAxis rg widths moduli savedWidths savedModuli
      axisWidth axisModulus lower left past packet zero dst pad tmp) R
      (crtControlGenerateAxisRegs rg widths moduli savedWidths savedModuli
        axisWidth axisModulus lower left past packet zero dst W wl nl st R a b e as bs)
      (crtControlGenerateAxisCost W w a b e (R zero).length) := by
  have hreg' := hreg
  regs_ne hreg'
  have hbank (j) (r) (hr : r ∈ [widths, moduli, savedWidths, savedModuli, axisWidth,
      axisModulus, lower, left, past, packet, zero, dst, pad, tmp]) : rg j ≠ r := hdisj j r hr
  have h₁ := crtPopEnt_runs (body := body) ‹widths ≠ axisWidth› R a as hwidths haw
  let R₁ := Function.update (Function.update R widths (crtEnts as)) axisWidth (List.replicate a tick)
  have h₂ := crtPopEnt_runs (body := body) ‹moduli ≠ axisModulus› R₁ b bs
    (by simp [R₁, ‹moduli ≠ axisWidth›, Ne.symm ‹widths ≠ moduli›, hmoduli])
    (by simp [R₁, Ne.symm ‹axisWidth ≠ axisModulus›, Ne.symm ‹widths ≠ axisModulus›, ham])
  let Rp := crtControlPoppedRegs widths moduli axisWidth axisModulus R a b as bs
  have hpoff : ∀ r, r ≠ widths → r ≠ moduli → r ≠ axisWidth → r ≠ axisModulus → Rp r = R r := by
    intro r h₁ h₂ h₃ h₄
    simp [Rp, crtControlPoppedRegs, h₁, h₂, h₃, h₄]
  have hRp : ∀ j, Rp (rg j) = tblRho W wl nl st j := by
    intro j
    rw [hpoff _ (hbank j _ (by simp)) (hbank j _ (by simp))
      (hbank j _ (by simp)) (hbank j _ (by simp)), hR]
  have hmod : (Rp axisModulus).length = b := by simp [Rp, crtControlPoppedRegs]
  have hlp : Rp lower = R lower := hpoff _ (Ne.symm ‹widths ≠ lower›)
    (Ne.symm ‹moduli ≠ lower›) (Ne.symm ‹axisWidth ≠ lower›) (Ne.symm ‹axisModulus ≠ lower›)
  have hpp : Rp pad = [] := by
    rw [hpoff _ (Ne.symm ‹widths ≠ pad›) (Ne.symm ‹moduli ≠ pad›)
      (Ne.symm ‹axisWidth ≠ pad›) (Ne.symm ‹axisModulus ≠ pad›), hpad]
  have hpt : Rp tmp = [] := by
    rw [hpoff _ (Ne.symm ‹widths ≠ tmp›) (Ne.symm ‹moduli ≠ tmp›)
      (Ne.symm ‹axisWidth ≠ tmp›) (Ne.symm ‹axisModulus ≠ tmp›), htmp]
  have h₃ := crtControlPrepareAxis_runs (body := body) hrg axisModulus lower pad tmp
    (by regs_nodup) (fun j r hr => hbank j r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) wl nl hwl hnl hw st hst hb he Rp hRp hmod
    (by rw [hlp]; exact hlower) hpp hpt
  let t := crtControlPreparedState st b e
  let Rq := crtBankOverlay rg Rp (tblRho W wl nl t)
  have htfit : ∀ j, t.val j < 2 ^ W := by
    intro j
    by_cases h2 : j = 2
    · subst j; simpa [t, crtControlPreparedState] using Nat.pow_lt_pow_right (by decide : 1 < 2) he
    · by_cases h5 : j = 5
      · subst j; simpa [t, crtControlPreparedState] using hb
      · simpa [t, crtControlPreparedState, h2, h5] using hst j
  have hqoff : ∀ r, (∀ j, rg j ≠ r) → Rq r = Rp r := fun r hr => crtBankOverlay_off _ _ _ _ hr
  have hqp : Rq packet = [] := by
    rw [hqoff _ (fun j => hbank j _ (by simp)), hpoff _ (Ne.symm ‹widths ≠ packet›)
      (Ne.symm ‹moduli ≠ packet›) (Ne.symm ‹axisWidth ≠ packet›)
      (Ne.symm ‹axisModulus ≠ packet›), hpacket]
  have h₄ := crtControlGenerateSelect_runs (body := body) hrg left savedWidths past packet zero dst
    (by regs_nodup) (fun j r hr => hbank j r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)) hW wl nl hwl hnl hw t htfit
    (by simpa [t, crtControlPreparedState] using hweight)
    (by simpa [t, crtControlPreparedState] using hindex) Rq
    (fun j => crtBankOverlay_on hrg _ _ j) hqp
  let Rs := crtControlGenerateSelectRegs rg left savedWidths past packet zero dst W wl nl t Rq
  have hsoff : ∀ r, (∀ j, rg j ≠ r) → r ≠ packet → r ≠ zero → r ≠ dst → r ≠ past → Rs r = Rq r := by
    intro r hd hp hz hx ht
    exact crtControlGenerateSelectRegs_off _ _ _ _ _ _ _ _ _ _ _ _ _ hd hp hz hx ht
  have hsw : Rs axisWidth = List.replicate a tick := by
    rw [hsoff _ (fun j => hbank j _ (by simp)) ‹axisWidth ≠ packet› ‹axisWidth ≠ zero›
      ‹axisWidth ≠ dst› ‹axisWidth ≠ past›, hqoff _ (fun j => hbank j _ (by simp))]
    simp [Rp, crtControlPoppedRegs, ‹axisWidth ≠ axisModulus›, Ne.symm ‹moduli ≠ axisWidth›]
  have hsm : Rs axisModulus = List.replicate b tick := by
    rw [hsoff _ (fun j => hbank j _ (by simp)) ‹axisModulus ≠ packet› ‹axisModulus ≠ zero›
      ‹axisModulus ≠ dst› ‹axisModulus ≠ past›, hqoff _ (fun j => hbank j _ (by simp))]
    simp [Rp, crtControlPoppedRegs]
  have hstmp : Rs tmp = [] := by
    rw [hsoff _ (fun j => hbank j _ (by simp)) (Ne.symm ‹packet ≠ tmp›) (Ne.symm ‹zero ≠ tmp›)
      (Ne.symm ‹dst ≠ tmp›) (Ne.symm ‹past ≠ tmp›), hqoff _ (fun j => hbank j _ (by simp)), hpt]
  have h₅ := crtUcopy_runs (body := body) ‹axisWidth ≠ lower› ‹axisWidth ≠ tmp› ‹lower ≠ tmp› Rs hstmp
  rw [hsw, List.length_replicate] at h₅
  let Ra := Function.update Rs lower (List.replicate a tick ++ Rs lower)
  have h₆ := crtPop_runs (body := body) left Ra
  let Rb := Function.update Ra left (Ra left).tail
  have h₇ := crtPushEnt_runs (body := body) (Ne.symm ‹savedWidths ≠ axisWidth›) Rb a
    (by simp [Rb, Ra, ‹axisWidth ≠ left›, ‹axisWidth ≠ lower›, hsw])
  let Rc := Function.update (Function.update Rb axisWidth []) savedWidths (crtEnt a ++ Rb savedWidths)
  have h₈ := crtPushEnt_runs (body := body) (Ne.symm ‹savedModuli ≠ axisModulus›) Rc b
    (by simp [Rc, Rb, Ra, Ne.symm ‹savedWidths ≠ axisModulus›, Ne.symm ‹axisWidth ≠ axisModulus›,
      ‹axisModulus ≠ left›, ‹axisModulus ≠ lower›, hsm])
  refine crtRuns_mono (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ (crtRuns_seq h₄
    (crtRuns_seq h₅ (crtRuns_seq h₆ (crtRuns_seq h₇ h₈))))))) ?_
  have hzq : Rq zero = R zero := by
    rw [hqoff _ (fun j => hbank j _ (by simp)), hpoff _ (Ne.symm ‹widths ≠ zero›)
      (Ne.symm ‹moduli ≠ zero›) (Ne.symm ‹axisWidth ≠ zero›) (Ne.symm ‹axisModulus ≠ zero›)]
  rw [hzq]
  unfold crtControlGenerateAxisCost
  omega

/-- The complete fixed traversal program. Both original entry streams are
restored in their original order by the two final moves. -/
def crtControlGenerateLoop (rg : TblR 10 → Fin T)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T) : Pr P T Q A U :=
  .seq (crtWhile widths (crtControlGenerateAxis rg widths moduli savedWidths savedModuli
    axisWidth axisModulus lower left past packet zero dst pad tmp)) <|
  .seq (crtMv savedWidths widths) <|
  .seq (crtMv savedModuli moduli) <|
  .seq (uclear lower) (uclear past)

/-- Frame-level traversal composition. The per-axis invariant is an explicit
proof obligation; this theorem adds the actual runtime loop, restoration of
both entry streams, and cleanup costs without assuming those operations free. -/
theorem crtControlGenerateLoop_runs {rg : TblR 10 → Fin T}
    {widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T}
    (hreg : [widths, moduli, savedWidths, savedModuli, lower, past].Nodup)
    (Ψ : ℕ → Regs T A) (a s : List ℕ) (b : ℕ)
    (hstep : ∀ j < a.length,
      Ψ j widths ≠ [] ∧
      crtRuns body (crtControlGenerateAxis rg widths moduli savedWidths savedModuli
        axisWidth axisModulus lower left past packet zero dst pad tmp)
        (Ψ j) (Ψ (j + 1)) b)
    (hwidths : Ψ a.length widths = []) (hmoduli : Ψ a.length moduli = [])
    (hsavedWidths : Ψ a.length savedWidths = (crtEnts a).reverse)
    (hsavedModuli : Ψ a.length savedModuli = (crtEnts s).reverse) :
    crtRuns body (crtControlGenerateLoop rg widths moduli savedWidths savedModuli
      axisWidth axisModulus lower left past packet zero dst pad tmp) (Ψ 0)
      (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Ψ a.length)
          savedWidths []) widths (crtEnts a)) savedModuli []) moduli (crtEnts s)) lower []) past [])
      (a.length * (b + 2) + 2 + (2 * (crtEnts (A := A) a).length + 2) +
        (2 * (crtEnts (A := A) s).length + 2) +
        (2 * (Ψ a.length lower).length + 2) + (2 * (Ψ a.length past).length + 2)) := by
  have hreg' := hreg
  regs_ne hreg'
  have hl := crtWhile_runs hstep hwidths
  have hw := crtMv_runs (body := body) (Ne.symm ‹widths ≠ savedWidths›) (Ψ a.length)
  rw [hsavedWidths, hwidths, List.reverse_reverse, List.append_nil] at hw
  let R₁ := Function.update (Function.update (Ψ a.length) savedWidths []) widths (crtEnts a)
  have hs := crtMv_runs (body := body) (Ne.symm ‹moduli ≠ savedModuli›) R₁
  have h₁s : R₁ savedModuli = (crtEnts s).reverse := by
    simp [R₁, Ne.symm ‹widths ≠ savedModuli›, Ne.symm ‹savedWidths ≠ savedModuli›, hsavedModuli]
  have h₁m : R₁ moduli = [] := by
    simp [R₁, Ne.symm ‹widths ≠ moduli›, ‹moduli ≠ savedWidths›, hmoduli]
  rw [h₁s, h₁m, List.reverse_reverse, List.append_nil] at hs
  let R₂ := Function.update (Function.update R₁ savedModuli []) moduli (crtEnts s)
  have hc := crtClear_runs (body := body) lower R₂
  let R₃ := Function.update R₂ lower []
  have hp := crtClear_runs (body := body) past R₃
  have he := crtRuns_seq hl (crtRuns_seq hw (crtRuns_seq hs (crtRuns_seq hc hp)))
  apply crtRuns_mono he
  simp [R₃, R₂, R₁, Ne.symm ‹lower ≠ past›, Ne.symm ‹moduli ≠ past›,
    Ne.symm ‹savedModuli ≠ past›, Ne.symm ‹widths ≠ past›, Ne.symm ‹savedWidths ≠ past›,
    Ne.symm ‹moduli ≠ lower›, Ne.symm ‹savedModuli ≠ lower›, Ne.symm ‹widths ≠ lower›,
    Ne.symm ‹savedWidths ≠ lower›]
  omega

/-- Every concrete axis transition leaves the binary bank in its exact next state. -/
theorem crtControlGenerateAxisRegs_bank {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst : Fin T)
    (hd : ∀ j, ∀ r ∈ [savedWidths, savedModuli, axisWidth, axisModulus, lower, left], rg j ≠ r)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A)
    (a b e : ℕ) (as bs : List ℕ) (j : TblR 10) :
    crtControlGenerateAxisRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst W wl nl st R a b e as bs (rg j) =
      tblRho W wl nl (crtControlGenerateNextState (crtControlPreparedState st b e)) j := by
  simp only [crtControlGenerateAxisRegs, Function.update_of_ne (hd j savedModuli (by simp)),
    Function.update_of_ne (hd j axisModulus (by simp)),
    Function.update_of_ne (hd j savedWidths (by simp)),
    Function.update_of_ne (hd j axisWidth (by simp)),
    Function.update_of_ne (hd j left (by simp)),
    Function.update_of_ne (hd j lower (by simp)), crtControlGenerateSelectRegs,
    crtBankOverlay_on hrg]

/-- The selector always consumes its current packet, including the parked-zero case. -/
theorem crtControlSelectRegs_packet (left seen past packet zero dst : Fin T)
    (hpz : packet ≠ zero) (hpd : packet ≠ dst) (hpp : packet ≠ past) (R : Regs T A) :
    crtControlSelectRegs left seen past packet zero dst R packet = [] := by
  unfold crtControlSelectRegs
  split_ifs <;> simp [crtControlInsertZeroRegs, hpz, hpd, hpp]

/-- Structural invariant of an axis transition, independent of descriptor arithmetic. -/
theorem crtControlGenerateAxisRegs_streams {rg : TblR 10 → Fin T}
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T)
    (hreg : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus, lower, left,
      past, packet, zero, dst, pad, tmp].Nodup)
    (hd : ∀ j, ∀ r ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst, pad, tmp], rg j ≠ r)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A)
    (a b e : ℕ) (as bs : List ℕ) :
    let S := crtControlGenerateAxisRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst W wl nl st R a b e as bs
    S widths = crtEnts as ∧ S moduli = crtEnts bs ∧
    S savedWidths = crtEnt a ++ R savedWidths ∧ S savedModuli = crtEnt b ++ R savedModuli ∧
    S axisWidth = [] ∧ S axisModulus = [] ∧
    S lower = List.replicate a tick ++ R lower ∧ S left = (R left).tail ∧
    S packet = [] ∧ S pad = R pad ∧ S tmp = R tmp := by
  have hreg' := hreg
  regs_ne hreg'
  let Rp := crtControlPoppedRegs widths moduli axisWidth axisModulus R a b as bs
  let t := crtControlPreparedState st b e
  let Rq := crtBankOverlay rg Rp (tblRho W wl nl t)
  let Rs := crtControlGenerateSelectRegs rg left savedWidths past packet zero dst W wl nl t Rq
  have hoff : ∀ r ∈ [widths, moduli, savedWidths, savedModuli, lower, left, pad, tmp],
      Rs r = Rp r := by
    intro r hr
    have hm : r ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
        lower, left, past, packet, zero, dst, pad, tmp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    have hn : r ≠ packet ∧ r ≠ zero ∧ r ≠ dst ∧ r ≠ past := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals refine ⟨?_, ?_, ?_, ?_⟩
      all_goals first | assumption | exact Ne.symm (by assumption)
    dsimp only [Rs, Rq]
    rw [crtControlGenerateSelectRegs_off _ _ _ _ _ _ _ _ _ _ _ _ _ (fun j => hd j r hm)
      hn.1 hn.2.1 hn.2.2.1 hn.2.2.2, crtBankOverlay_off _ _ _ _ (fun j => hd j r hm)]
  have hp : Rs packet = [] := by
    dsimp only [Rs, crtControlGenerateSelectRegs]
    rw [crtBankOverlay_off _ _ _ _ (fun j => hd j packet (by simp)),
      crtControlSelectRegs_packet _ _ _ _ _ _ ‹packet ≠ zero› ‹packet ≠ dst› (Ne.symm ‹past ≠ packet›)]
  let R₁ := Function.update Rs lower (List.replicate a tick ++ Rs lower)
  let R₂ := Function.update R₁ left (R₁ left).tail
  let R₃ := Function.update (Function.update R₂ axisWidth []) savedWidths (crtEnt a ++ R₂ savedWidths)
  let S := Function.update (Function.update R₃ axisModulus []) savedModuli (crtEnt b ++ R₃ savedModuli)
  change S widths = _ ∧ S moduli = _ ∧ S savedWidths = _ ∧ S savedModuli = _ ∧
    S axisWidth = _ ∧ S axisModulus = _ ∧ S lower = _ ∧ S left = _ ∧ S packet = _ ∧ S pad = _ ∧ S tmp = _
  have h₁ := hoff widths (by simp)
  have h₂ := hoff moduli (by simp)
  have h₃ := hoff savedWidths (by simp)
  have h₄ := hoff savedModuli (by simp)
  have h₅ := hoff lower (by simp)
  have h₆ := hoff left (by simp)
  have h₇ := hoff pad (by simp)
  have h₈ := hoff tmp (by simp)
  simp (disch := first | assumption | (apply Ne.symm; assumption)) only
    [S, R₃, R₂, R₁, Function.update_of_ne, Function.update_self,
      h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, hp, Rp, crtControlPoppedRegs, and_self]

end IntegerMultBounds.MathlibTM2.Fast
