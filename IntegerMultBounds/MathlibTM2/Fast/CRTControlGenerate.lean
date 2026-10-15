module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlBank

/-! # Runtime CRT descriptor production

Fixed host kernels build binary place values and prepend descriptor packets.
Input words are preserved and scratch registers restored. The parameter-list
traversal and exposed-order packet assembly remain separate integration work.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Prepend the four runtime words in packet order, keeping each source. -/
def crtControlEmitPacket (place bound weight active dst t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bcopy active dst t₁ t₂) (.seq (bcopy weight dst t₁ t₂)
    (.seq (bcopy bound dst t₁ t₂) (bcopy place dst t₁ t₂)))

theorem crtControlEmitPacket_runs {place bound weight active dst t₁ t₂ : Fin T}
    (hreg : [place, bound, weight, active, dst, t₁, t₂].Nodup)
    (R : Regs T A) (W : ℕ) (f : CrtControlField)
    (hp : R place = binSyms W f.place) (hb : R bound = binSyms W f.bound)
    (hw : R weight = binSyms W f.weight)
    (ha : R active = binSyms W (if f.active then 1 else 0))
    (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) :
    crtRuns body (crtControlEmitPacket place bound weight active dst t₁ t₂) R
      (Function.update R dst (crtControlPacket W f ++ R dst)) (24 * W + 24) := by
  have hreg' := hreg
  regs_ne hreg'
  have s₁ := crtBcopy_runs (body := body) (a := active) (c := dst)
    (t₁ := t₁) (t₂ := t₂) (by regs_nodup) R ht₁ ht₂
  let R₁ := Function.update R dst (R active ++ R dst)
  have s₂ := crtBcopy_runs (body := body) (a := weight) (c := dst)
    (t₁ := t₁) (t₂ := t₂) (by regs_nodup) R₁
    (by simp [R₁, Ne.symm ‹dst ≠ t₁›, ht₁]) (by simp [R₁, Ne.symm ‹dst ≠ t₂›, ht₂])
  let R₂ := Function.update R₁ dst (R₁ weight ++ R₁ dst)
  have s₃ := crtBcopy_runs (body := body) (a := bound) (c := dst)
    (t₁ := t₁) (t₂ := t₂) (by regs_nodup) R₂
    (by simp [R₂, R₁, Ne.symm ‹dst ≠ t₁›, ht₁])
    (by simp [R₂, R₁, Ne.symm ‹dst ≠ t₂›, ht₂])
  let R₃ := Function.update R₂ dst (R₂ bound ++ R₂ dst)
  have s₄ := crtBcopy_runs (body := body) (a := place) (c := dst)
    (t₁ := t₁) (t₂ := t₂) (by regs_nodup) R₃
    (by simp [R₃, R₂, R₁, Ne.symm ‹dst ≠ t₁›, ht₁])
    (by simp [R₃, R₂, R₁, Ne.symm ‹dst ≠ t₂›, ht₂])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃ s₄))) ?_) ?_
  · simp [R₃, R₂, R₁, ‹place ≠ dst›, ‹bound ≠ dst›, ‹weight ≠ dst›,
      hp, hb, hw, ha, crtControlPacket, crtControlWords]
  · simp only [R₃, R₂, R₁, Function.update_of_ne ‹place ≠ dst›,
      Function.update_of_ne ‹bound ≠ dst›, Function.update_of_ne ‹weight ≠ dst›,
      hp, hb, hw, ha, length_binSyms]
    omega

/-- A place word is built in space proportional to its bit width, never in
unary space proportional to its numeric value. -/
def crtControlPow2 (width exponent dst pad tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy width pad tmp) (.seq (usub exponent pad tmp)
    (.seq (crtPop pad) (.seq (zeroBits pad dst tmp)
      (.seq (crtPush dst (bitSymbol true))
        (.seq (zeroBits exponent dst tmp) (uclear pad))))))

lemma crtControl_binSyms_pow2 (W e : ℕ) (he : e < W) :
    (binSyms W (2 ^ e) : List (Fin (A + 4))) =
      List.replicate e (bitSymbol false) ++ bitSymbol true ::
        List.replicate (W - e - 1) (bitSymbol false) := by
  induction e generalizing W with
  | zero =>
      cases W with
      | zero => omega
      | succ W => simp [binSyms_succ, binSyms_zero_right]
  | succ e ih =>
      cases W with
      | zero => omega
      | succ W =>
          rw [binSyms_succ]
          have hd : 2 ^ (e + 1) / 2 = 2 ^ e := by simp [pow_succ]
          have hb : (2 ^ (e + 1)).testBit 0 = false := by
            simp [pow_succ, Nat.testBit_zero]
          rw [hd, hb, ih W (by omega)]
          simp [List.replicate_succ, List.cons_append]

theorem crtControlPow2_runs {width exponent dst pad tmp : Fin T}
    (hreg : [width, exponent, dst, pad, tmp].Nodup) (R : Regs T A)
    (W e : ℕ) (hW : (R width).length = W) (he : (R exponent).length = e) (heW : e < W)
    (hdst : R dst = []) (hpad : R pad = []) (htmp : R tmp = []) :
    crtRuns body (crtControlPow2 width exponent dst pad tmp) R
      (Function.update R dst (binSyms W (2 ^ e))) (10 * W + 8 * e + 24) := by
  have hreg' := hreg
  regs_ne hreg'
  have s₁ := crtUcopy_runs (body := body) ‹width ≠ pad› ‹width ≠ tmp› ‹pad ≠ tmp› R htmp
  let R₁ := Function.update R pad (List.replicate W tick)
  have h₁ : Function.update R pad (List.replicate (R width).length tick ++ R pad) = R₁ := by
    simp [R₁, hW, hpad]
  rw [h₁] at s₁
  have s₂ := crtUsub_runs (body := body) ‹exponent ≠ pad› ‹exponent ≠ tmp› ‹pad ≠ tmp› R₁
    (by simp [R₁, Ne.symm ‹pad ≠ tmp›, htmp])
  let R₂ := Function.update R pad (List.replicate (W - e) tick)
  have h₂ : Function.update R₁ pad ((R₁ pad).drop (R₁ exponent).length) = R₂ := by
    simp [R₂, R₁, ‹exponent ≠ pad›, he]
  rw [h₂] at s₂
  have s₃ := crtPop_runs (body := body) pad R₂
  let R₃ := Function.update R pad (List.replicate (W - e - 1) tick)
  have h₃ : Function.update R₂ pad (R₂ pad).tail = R₃ := by simp [R₃, R₂]
  rw [h₃] at s₃
  have s₄ := crtZeroBits_runs (body := body) (Ne.symm ‹dst ≠ pad›) ‹pad ≠ tmp› ‹dst ≠ tmp› R₃
    (by simp [R₃, Ne.symm ‹pad ≠ tmp›, htmp])
  let R₄ := Function.update R₃ dst (binSyms (W - e - 1) 0)
  have h₄ : Function.update R₃ dst (binSyms (R₃ pad).length 0 ++ R₃ dst) = R₄ := by
    simp [R₄, R₃, ‹dst ≠ pad›, hdst]
  rw [h₄] at s₄
  have s₅ := crtPush_runs (body := body) dst (bitSymbol true) R₄
  let R₅ := Function.update R₄ dst (bitSymbol true :: R₄ dst)
  have s₆ := crtZeroBits_runs (body := body) ‹exponent ≠ dst› ‹exponent ≠ tmp› ‹dst ≠ tmp› R₅
    (by simp [R₅, R₄, R₃, Ne.symm ‹dst ≠ tmp›, Ne.symm ‹pad ≠ tmp›, htmp])
  let R₆ := Function.update R₅ dst (binSyms (R₅ exponent).length 0 ++ R₅ dst)
  have s₇ := crtClear_runs (body := body) pad R₆
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ (crtRuns_seq s₅ (crtRuns_seq s₆ s₇)))))) ?_) ?_
  · funext k
    by_cases hk : k = dst
    · subst k
      simp [R₆, R₅, R₄, R₃, ‹dst ≠ pad›, ‹exponent ≠ dst›, ‹exponent ≠ pad›,
        he, crtControl_binSyms_pow2 W e heW, binSyms_zero_right]
    · by_cases hkp : k = pad
      · subst k; simp [hk, hpad]
      · simp [R₆, R₅, R₄, R₃, hk, hkp]
  · simp [R₆, R₅, R₄, R₃, R₁, hW, he, ‹exponent ≠ dst›,
      ‹exponent ≠ pad›, Ne.symm ‹dst ≠ pad›]
    omega

/-- Generator register meanings: axis index (0), target index (1), binary
power of original lower width (2), target width power (3), zero width power
(4), modulus (5), original mixed-radix weight (6), generated place (7),
generated active flag (8), and target's original lower-width power (9).
Only outputs 7 and 8 change. Target omission belongs to the outer iterator. -/
def crtControlGenerateKernel : TblCode 10 :=
  .seq (.ins (.zero 8))
    (.ite 0 1
      (.seq (.ins (.inc 8)) (.ite 0 8 (.ins (.div 9 4 7)) (.ins (.div 2 4 7))))
      (.ins (.div 2 3 7)))

def crtControlGeneratedField {A : ℕ} (st : TblSt 10 A) : CrtControlField :=
  ⟨if st.val 0 < st.val 1 then
      (if st.val 0 = 0 then st.val 9 else st.val 2) / st.val 4
    else st.val 2 / st.val 3,
    st.val 5, st.val 6, decide (st.val 0 < st.val 1)⟩

def crtControlGeneratedState {A : ℕ} (st : TblSt 10 A) : TblSt 10 A :=
  ⟨Function.update (Function.update st.val 8 (if st.val 0 < st.val 1 then 1 else 0))
    7 (crtControlGeneratedField st).place, st.acc⟩

theorem crtControlGenerateKernel_do {A W w : ℕ} (st : TblSt 10 A) (hW : 0 < W) :
    TblDo A W w crtControlGenerateKernel st
      (fun s => s = crtControlGeneratedState st) 5 := by
  let s := (.zero 8 : TblIns 10).exact A w st
  have hz := TblDo.insX (.zero 8) (st := st) (A := A) (W := W) (w := w)
    trivial (P := fun t => t = s) rfl
  have hb : TblDo A W w
      (.ite 0 1 (.seq (.ins (.inc 8))
        (.ite 0 8 (.ins (.div 9 4 7)) (.ins (.div 2 4 7)))) (.ins (.div 2 3 7)))
      s (fun t => t = crtControlGeneratedState st) 4 := by
    by_cases hlt : st.val 0 < st.val 1
    · have hlt' : s.val 0 < s.val 1 := by simpa [s, TblIns.exact] using hlt
      let t := (.inc 8 : TblIns 10).exact A w s
      have hone : 1 < 2 ^ W := Nat.one_lt_two_pow hW.ne'
      have hi := TblDo.insX (.inc 8) (st := s) (A := A) (W := W) (w := w)
        (by simpa [s, TblIns.exact, TblIns.fits] using hone) (P := fun u => u = t) rfl
      have hd : TblDo A W w (.ite 0 8 (.ins (.div 9 4 7)) (.ins (.div 2 4 7))) t
          (fun u => u = crtControlGeneratedState st) 2 := by
        by_cases hzero : st.val 0 = 0
        · have hpos : 0 < st.val 1 := by omega
          apply TblDo.iteT
          · simp [t, s, TblIns.exact, hzero]
          · apply TblDo.insX (.div 9 4 7) trivial
            simp [t, s, TblIns.exact, crtControlGeneratedState, crtControlGeneratedField,
              hzero, hpos]
        · apply TblDo.iteF
          · simpa [t, s, TblIns.exact] using (show ¬st.val 0 < 1 by omega)
          · apply TblDo.insX (.div 2 4 7) trivial
            simp [t, s, TblIns.exact, crtControlGeneratedState, crtControlGeneratedField,
              hlt, hzero]
      exact TblDo.iteT hlt' (hi.seq (fun u hu => hu ▸ hd))
    · have hlt' : ¬s.val 0 < s.val 1 := by simpa [s, TblIns.exact] using hlt
      have hd : TblDo A W w (.ins (.div 2 3 7)) s
          (fun u => u = crtControlGeneratedState st) 1 := by
        apply TblDo.insX (.div 2 3 7) trivial
        simp [s, TblIns.exact, crtControlGeneratedState, crtControlGeneratedField, hlt]
      exact (TblDo.iteF hlt' hd).mono (fun _ h => h) (by decide)
  exact hz.seq (fun t ht => ht ▸ hb)

/-- Fixed executable arithmetic kernel with a whole-register-file frame. -/
theorem crtControlGenerateKernel_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) {W w : ℕ} (hW : 0 < W)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    crtRuns body (tblCompile rg crtControlGenerateKernel) R
      (crtBankOverlay rg R (tblRho W wl nl (crtControlGeneratedState st)))
      (5 * tblC W w) := by
  obtain ⟨st', hst', hr⟩ := (crtControlGenerateKernel_do st hW).host (body := body)
    hrg wl nl hwl hnl hw hst
  subst st'
  exact crtRuns_of_tbl hrg hr R hR

/-- Arithmetic generation followed by packet emission on an external tape. -/
def crtControlGeneratePacket (rg : TblR 10 → Fin T) (dst : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg crtControlGenerateKernel)
    (crtControlEmitPacket (rg (.v 7)) (rg (.v 5)) (rg (.v 6)) (rg (.v 8))
      dst (rg (.z 0)) (rg (.z 1)))

theorem crtControlGeneratePacket_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (dst : Fin T) (hdisj : ∀ r, rg r ≠ dst)
    {W w : ℕ} (hW : 0 < W) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    crtRuns body (crtControlGeneratePacket rg dst) R
      (Function.update (crtBankOverlay rg R (tblRho W wl nl (crtControlGeneratedState st)))
        dst (crtControlPacket W (crtControlGeneratedField st) ++ R dst))
      (5 * tblC W w + (24 * W + 24)) := by
  have hk := crtControlGenerateKernel_runs (body := body) hrg hW wl nl hwl hnl hw st hst R hR
  let R₁ := crtBankOverlay rg R (tblRho W wl nl (crtControlGeneratedState st))
  have hp := crtControlEmitPacket_runs (body := body)
    (place := rg (.v 7)) (bound := rg (.v 5)) (weight := rg (.v 6))
    (active := rg (.v 8)) (dst := dst) (t₁ := rg (.z 0)) (t₂ := rg (.z 1))
    (by simp [List.nodup_cons, hrg.eq_iff, hdisj, Ne.symm (hdisj (.z 0)),
      Ne.symm (hdisj (.z 1))]) R₁ W (crtControlGeneratedField st)
    (by simp [R₁, crtBankOverlay_on hrg, tblRho, crtControlGeneratedState])
    (by simp [R₁, crtBankOverlay_on hrg, tblRho, crtControlGeneratedState, crtControlGeneratedField])
    (by simp [R₁, crtBankOverlay_on hrg, tblRho, crtControlGeneratedState, crtControlGeneratedField])
    (by simp [R₁, crtBankOverlay_on hrg, tblRho, crtControlGeneratedState, crtControlGeneratedField])
    (by simp [R₁, crtBankOverlay_on hrg, tblRho])
    (by simp [R₁, crtBankOverlay_on hrg, tblRho])
  have hd : R₁ dst = R dst := crtBankOverlay_off _ _ _ _ hdisj
  rw [hd] at hp
  exact crtRuns_seq hk hp

/-- Binary division of powers removes precisely the width of the omitted axis. -/
lemma crtControl_power_div (m n : ℕ) (h : n ≤ m) :
    2 ^ m / 2 ^ n = 2 ^ (m - n) := by
  rw [← Nat.pow_sub_mul_pow 2 h, Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ n)]

open IntegerMultBounds.MathlibTM2.Mult in
/-- The generator retains original mixed-radix weights and marks exactly the
lower control axes, while calculating the exposed-layout place exponent. -/
theorem crtControlGeneratedField_spec {d A : ℕ} (s : Fin d → ℕ)
    (j i : Fin d) (Pj Pi ai a0 : ℕ) (st : TblSt 10 A)
    (h0 : st.val 0 = j.val) (h1 : st.val 1 = i.val)
    (h2 : st.val 2 = 2 ^ Pj) (h3 : st.val 3 = 2 ^ ai)
    (h4 : st.val 4 = 2 ^ a0) (h5 : st.val 5 = s j)
    (h6 : st.val 6 = prefixProd s j) (h9 : st.val 9 = 2 ^ Pi)
    (hlo : j.val < i.val → a0 ≤ if j.val = 0 then Pi else Pj)
    (hhi : ¬j.val < i.val → ai ≤ Pj) :
    crtControlGeneratedField st =
      ⟨2 ^ (if j.val < i.val then (if j.val = 0 then Pi else Pj) - a0 else Pj - ai),
        s j, prefixProd s j, decide (j.val < i.val)⟩ := by
  simp only [crtControlGeneratedField, h0, h1, h2, h3, h4, h5, h6, h9]
  congr 1
  split_ifs with hlt hz
  · exact crtControl_power_div _ _ (by simpa [hz] using hlo hlt)
  · exact crtControl_power_div _ _ (by simpa [hz] using hlo hlt)
  · exact crtControl_power_div _ _ (hhi hlt)

/-- Advance the original mixed-radix weight after emitting a descriptor.
The modulus source is preserved; the only changed variable is weight (6). -/
def crtControlAdvanceWeight : TblCode 10 := .ins (.mul 6 5 6)

theorem crtControlAdvanceWeight_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) {W w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (hst : ∀ j, st.val j < 2 ^ W)
    (hfit : st.val 6 * st.val 5 < 2 ^ W)
    (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    crtRuns body (tblCompile rg crtControlAdvanceWeight) R
      (crtBankOverlay rg R (tblRho W wl nl
        ⟨Function.update st.val 6 (st.val 6 * st.val 5), st.acc⟩)) (tblC W w) := by
  have hi := TblDo.insX (.mul 6 5 6) (st := st) (A := A) (W := W) (w := w)
    hfit (P := fun t => t = (.mul 6 5 6 : TblIns 10).exact A w st) rfl
  obtain ⟨st', hst', hr⟩ := hi.host (body := body) hrg wl nl hwl hnl hw hst
  subst st'
  simpa only [Nat.one_mul, crtControlAdvanceWeight, TblIns.exact] using
    crtRuns_of_tbl hrg hr R hR

/-- The executable multiplication is exactly the next prefix product. -/
theorem crtControlAdvanceWeight_spec {d A : ℕ} (s : Fin d → ℕ)
    {j : ℕ} (hj : j < d) (st : TblSt 10 A)
    (hb : st.val 5 = s ⟨j, hj⟩) (hw : st.val 6 = crtProd s j) :
    st.val 6 * st.val 5 = crtProd s (j + 1) := by
  rw [hb, hw, crtProd_succ s hj]

end IntegerMultBounds.MathlibTM2.Fast
