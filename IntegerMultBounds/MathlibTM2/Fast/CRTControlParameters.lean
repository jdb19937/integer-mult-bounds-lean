module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateSetup

/-! # Preparing the exposed rotation's runtime parameters

The old driver supplies unary moduli and multipliers. Convert these to
preserved binary words with a returned arithmetic workspace, and construct
the unary padding and fiber-address widths from the existing unary widths.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Encode a preserved unary source, returning the bank empty. -/
def crtControlUnaryWord (rg : TblR 10 → Fin T) (src saved dst : Fin T) : Pr P T Q A U :=
  .seq (crtControlGenerateInit rg)
    (.seq (crtControlReadUnary rg src saved 1)
      (.seq (bcopy (rg (.v 1)) dst (rg (.z 0)) (rg (.z 1)))
        (crtControlWorkspaceClear rg)))

def crtControlUnaryWordCost (W w n : ℕ) : ℕ :=
  (10 * (4 * W + 4) + 1 + 2 * tblC W w) +
    ((tblC W w + (n * (tblC W w + 3) + 2 * n + 4)) +
      ((6 * W + 6) + (10 * (2 * W + 2) + 1)))

theorem crtControlUnaryWord_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (src saved dst : Fin T) (hreg : [src, saved, dst].Nodup)
    (hsrc : ∀ r, rg r ≠ src) (hsaved : ∀ r, rg r ≠ saved) (hdst : ∀ r, rg r ≠ dst)
    {W w n : ℕ} (hW : 0 < W) (hn : n < 2 ^ W)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (R : Regs T A) (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hv : ∀ j, R (rg (.v j)) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (hsource : (R src).length = n) (hs : R saved = []) (hd : R dst = []) :
    crtRuns body (crtControlUnaryWord rg src saved dst) R
      (Function.update R dst (binSyms W n)) (crtControlUnaryWordCost W w n) := by
  let st₀ := crtControlGenerateInitial (R (rg .acc))
  let st₁ : TblSt 10 A := ⟨Function.update st₀.val 1 n, st₀.acc⟩
  let R₀ := crtBankOverlay rg R (tblRho W wl nl st₀)
  let R₁ := crtBankOverlay rg R (tblRho W wl nl st₁)
  let R' := Function.update R dst (binSyms W n)
  have hinit := crtControlGenerateInit_runs (body := body) hrg hW wl nl hwl hnl hw R hwr hwn hv hz
  have hfit : ∀ j, st₀.val j < 2 ^ W := by
    intro j
    simp only [st₀, crtControlGenerateInitial]
    split_ifs
    · exact Nat.one_lt_two_pow hW.ne'
    · positivity
  have hread := crtControlReadUnary_runs (body := body) hrg src saved (by have hreg' := hreg; regs_ne hreg'; assumption) hsrc hsaved 1
    wl nl hwl hnl hw st₀ hfit hn R₀ (crtBankOverlay_on hrg _ _)
    (by simp [R₀, crtBankOverlay_off _ _ _ _ hsrc, hsource])
    (by simp [R₀, crtBankOverlay_off _ _ _ _ hsaved, hs])
  have hout : crtBankOverlay rg R₀ (tblRho W wl nl st₁) = R₁ := by
    funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hk; simp [R₁, crtBankOverlay_on hrg]
    · have hk' : ∀ r, rg r ≠ k := by simpa using hk
      simp [R₁, R₀, crtBankOverlay_off _ _ _ _ hk']
  have hcopy := crtBcopy_runs (body := body)
    (a := rg (.v 1)) (c := dst) (t₁ := rg (.z 0)) (t₂ := rg (.z 1))
    (by simp [List.nodup_cons, hrg.eq_iff, hdst, Ne.symm (hdst (.z 0)), Ne.symm (hdst (.z 1))]) R₁
    (by simp [R₁, crtBankOverlay_on hrg, tblRho])
    (by simp [R₁, crtBankOverlay_on hrg, tblRho])
  have hword : R₁ (rg (.v 1)) = binSyms W n := by simp [R₁, st₁, crtBankOverlay_on hrg, tblRho]
  have hblank : R₁ dst = [] := by simp [R₁, crtBankOverlay_off _ _ _ _ hdst, hd]
  rw [hword, hblank, List.append_nil, length_binSyms] at hcopy
  have hcopyout : Function.update R₁ dst (binSyms W n) =
      crtBankOverlay rg R' (tblRho W wl nl st₁) := by
    funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hk; simp [R₁, crtBankOverlay_on hrg, hdst]
    · have hk' : ∀ r, rg r ≠ k := by simpa using hk
      by_cases hkd : k = dst
      · subst k; simp [R', crtBankOverlay_off _ _ _ _ hdst]
      · simp [R₁, R', hkd, crtBankOverlay_off _ _ _ _ hk']
  have hclear := crtControlWorkspace_restore (body := body) hrg W wl nl st₁ R'
    (by intro j; simp [R', hdst, hv]) (by intro j; simp [R', hdst, hz])
    (by simp [R', hdst, hwr]) (by simp [R', hdst, hwn])
    (by simp [st₁, st₀, crtControlGenerateInitial, R', hdst])
  exact crtRuns_seq hinit (crtRuns_seq (crtRuns_congr hread hout)
    (crtRuns_seq (crtRuns_congr hcopy hcopyout) hclear))

/-- Build the target-axis padding in unary while preserving both inputs. -/
def crtControlPadding (axis modulus padding tmp saved : Fin T) : Pr P T Q A U :=
  .seq (crtPush padding tick)
    (.seq (upow2 axis padding tmp saved) (usub modulus padding tmp))

theorem crtControlPadding_runs {axis modulus padding tmp saved : Fin T}
    (hreg : [axis, modulus, padding, tmp, saved].Nodup) (R : Regs T A)
    (hpadding : R padding = []) (htmp : R tmp = []) (hsaved : R saved = []) :
    crtRuns body (crtControlPadding axis modulus padding tmp saved) R
      (Function.update R padding (List.replicate (2 ^ (R axis).length - (R modulus).length) tick))
      (4 * 2 ^ (R axis).length + 9 * (R axis).length + 4 * (R modulus).length + 9) := by
  have hreg' := hreg
  regs_ne hreg'
  have hpush := crtPush_runs (body := body) padding tick R
  let R₁ := Function.update R padding [tick]
  have hpush' : crtRuns body (crtPush padding tick) R R₁ 1 := by simpa [R₁, hpadding] using hpush
  have hpow := crtUpow2_runs (body := body) (a := axis) (b := padding) (t₁ := tmp) (t₂ := saved)
    (by regs_nodup) R₁ (by simp [R₁, Ne.symm ‹padding ≠ tmp›, htmp])
    (by simp [R₁, Ne.symm ‹padding ≠ saved›, hsaved])
  have ha : R₁ axis = R axis := by simp [R₁, ‹axis ≠ padding›]
  rw [ha] at hpow
  simp only [R₁, Function.update_self, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_cons, List.length_nil] at hpow
  let R₂ := Function.update R padding (List.replicate (2 ^ (R axis).length) tick)
  have hpow' : crtRuns body (upow2 axis padding tmp saved) R₁ R₂
      (4 * 2 ^ (R axis).length + 9 * (R axis).length + 4) := by
    simpa [R₁, R₂] using hpow
  have hsub := crtUsub_runs (body := body) ‹modulus ≠ padding› ‹modulus ≠ tmp› ‹padding ≠ tmp› R₂
    (by simp [R₂, Ne.symm ‹padding ≠ tmp›, htmp])
  apply crtRuns_mono (crtRuns_congr (crtRuns_seq hpush' (crtRuns_seq hpow' hsub)) ?_) ?_
  · simp [R₂, ‹modulus ≠ padding›]
  · simp [R₂, ‹modulus ≠ padding›]; omega

/-- The exposed outer address width is total width minus target-axis width. -/
def crtControlPrefixWidth (total axis outer tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy total outer tmp) (usub axis outer tmp)

theorem crtControlPrefixWidth_runs {total axis outer tmp : Fin T}
    (hreg : [total, axis, outer, tmp].Nodup) (R : Regs T A)
    (hp : R outer = []) (ht : R tmp = []) :
    crtRuns body (crtControlPrefixWidth total axis outer tmp) R
      (Function.update R outer (List.replicate ((R total).length - (R axis).length) tick))
      (4 * (R total).length + 4 * (R axis).length + 8) := by
  have hreg' := hreg
  regs_ne hreg'
  have hc := crtUcopy_runs (body := body) ‹total ≠ outer› ‹total ≠ tmp› ‹outer ≠ tmp› R ht
  rw [hp, List.append_nil] at hc
  let R₁ := Function.update R outer (List.replicate (R total).length tick)
  have hs := crtUsub_runs (body := body) ‹axis ≠ outer› ‹axis ≠ tmp› ‹outer ≠ tmp› R₁
    (by simp [R₁, Ne.symm ‹outer ≠ tmp›, ht])
  apply crtRuns_mono (crtRuns_congr (crtRuns_seq hc hs) ?_) ?_
  · simp [R₁, ‹axis ≠ outer›]
  · simp [R₁, ‹axis ≠ outer›]; omega

/-- Return the two words, unary padding, and outer width after their use. -/
def crtControlParametersClear (e : Fin 4 → Fin T) : Pr P T Q A U :=
  .seq (uclear (e 0)) (.seq (uclear (e 1)) (.seq (uclear (e 2)) (uclear (e 3))))

theorem crtControlParametersClear_runs (e : Fin 4 → Fin T) (he : Function.Injective e)
    (R : Regs T A) (W padding outer : ℕ)
    (h0 : (R (e 0)).length = W) (h1 : (R (e 1)).length = W)
    (h2 : (R (e 2)).length = padding) (h3 : (R (e 3)).length = outer) :
    crtRuns body (crtControlParametersClear e) R
      (Function.update (Function.update (Function.update (Function.update R (e 0) []) (e 1) []) (e 2) []) (e 3) [])
      (4 * W + 2 * padding + 2 * outer + 8) := by
  let R₁ := Function.update R (e 0) []
  let R₂ := Function.update R₁ (e 1) []
  let R₃ := Function.update R₂ (e 2) []
  have h := crtRuns_seq (crtClear_runs (body := body) (e 0) R)
    (crtRuns_seq (crtClear_runs (body := body) (e 1) R₁)
      (crtRuns_seq (crtClear_runs (body := body) (e 2) R₂)
        (crtClear_runs (body := body) (e 3) R₃)))
  apply crtRuns_mono h
  simp [R₃, R₂, R₁, he.eq_iff, h0, h1, h2, h3]
  omega

/-- Input slots 0–3 are unary modulus, multiplier, axis width, and total width.
Outputs 4–7 are the two binary words, unary padding, and outer address width;
slots 8–9 are returned scratch. -/
def crtControlParameters (rg : TblR 10 → Fin T) (e : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (crtControlUnaryWord rg (e 0) (e 8) (e 4))
    (.seq (crtControlUnaryWord rg (e 1) (e 8) (e 5))
      (.seq (crtControlPadding (e 2) (e 0) (e 6) (e 8) (e 9))
        (crtControlPrefixWidth (e 3) (e 2) (e 7) (e 8))))

def crtControlParametersRegs (e : Fin 10 → Fin T) (W S μ a L : ℕ) (R : Regs T A) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update R
    (e 4) (binSyms W S)) (e 5) (binSyms W μ))
      (e 6) (List.replicate (2 ^ a - S) tick)) (e 7) (List.replicate (L - a) tick)

def crtControlParametersSetupCost (W w S μ a L : ℕ) : ℕ :=
  crtControlUnaryWordCost W w S +
    (crtControlUnaryWordCost W w μ +
      ((4 * 2 ^ a + 9 * a + 4 * S + 9) + (4 * L + 4 * a + 8)))

theorem crtControlParameters_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (e : Fin 10 → Fin T) (he : Function.Injective e) (hrge : ∀ r j, rg r ≠ e j)
    {W w S μ a L : ℕ} (hW : 0 < W) (hS : S < 2 ^ W) (hμ : μ < 2 ^ W)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (R : Regs T A) (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hv : ∀ j, R (rg (.v j)) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (h0 : (R (e 0)).length = S) (h1 : (R (e 1)).length = μ)
    (h2 : (R (e 2)).length = a) (h3 : (R (e 3)).length = L)
    (hempty : ∀ j : Fin 10, 4 ≤ j.val → R (e j) = []) :
    crtRuns body (crtControlParameters rg e) R
      (crtControlParametersRegs e W S μ a L R) (crtControlParametersSetupCost W w S μ a L) := by
  let R₁ := Function.update R (e 4) (binSyms W S)
  let R₂ := Function.update R₁ (e 5) (binSyms W μ)
  let R₃ := Function.update R₂ (e 6) (List.replicate (2 ^ a - S) tick)
  have hword₁ := crtControlUnaryWord_runs (body := body) hrg (e 0) (e 8) (e 4)
    (by simp [List.nodup_cons, he.eq_iff]) (fun r => hrge r 0) (fun r => hrge r 8)
    (fun r => hrge r 4) hW hS wl nl hwl hnl hw R hwr hwn hv hz h0
    (hempty 8 (by decide)) (hempty 4 (by decide))
  have hword₂ := crtControlUnaryWord_runs (body := body) hrg (e 1) (e 8) (e 5)
    (by simp [List.nodup_cons, he.eq_iff]) (fun r => hrge r 1) (fun r => hrge r 8)
    (fun r => hrge r 5) hW hμ wl nl hwl hnl hw R₁
    (by simp [R₁, hrge, hwr]) (by simp [R₁, hrge, hwn])
    (by intro j; simp [R₁, hrge, hv]) (by intro j; simp [R₁, hrge, hz])
    (by simp [R₁, he.eq_iff, h1])
    (by simp [R₁, he.eq_iff, hempty 8 (by decide)])
    (by simp [R₁, he.eq_iff, hempty 5 (by decide)])
  have hpad := crtControlPadding_runs (body := body) (axis := e 2) (modulus := e 0)
    (padding := e 6) (tmp := e 8) (saved := e 9)
    (by simp [List.nodup_cons, he.eq_iff]) R₂
    (by simp [R₂, R₁, he.eq_iff, hempty 6 (by decide)])
    (by simp [R₂, R₁, he.eq_iff, hempty 8 (by decide)])
    (by simp [R₂, R₁, he.eq_iff, hempty 9 (by decide)])
  have ha : (R₂ (e 2)).length = a := by simp [R₂, R₁, he.eq_iff, h2]
  have hs : (R₂ (e 0)).length = S := by simp [R₂, R₁, he.eq_iff, h0]
  rw [ha, hs] at hpad
  have hwidth := crtControlPrefixWidth_runs (body := body) (total := e 3) (axis := e 2)
    (outer := e 7) (tmp := e 8) (by simp [List.nodup_cons, he.eq_iff]) R₃
    (by simp [R₃, R₂, R₁, he.eq_iff, hempty 7 (by decide)])
    (by simp [R₃, R₂, R₁, he.eq_iff, hempty 8 (by decide)])
  have ht : (R₃ (e 3)).length = L := by simp [R₃, R₂, R₁, he.eq_iff, h3]
  have ht' : (R₃ (e 2)).length = a := by simp [R₃, R₂, R₁, he.eq_iff, h2]
  rw [ht, ht'] at hwidth
  exact crtRuns_seq hword₁ (crtRuns_seq hword₂ (crtRuns_seq hpad hwidth))

end IntegerMultBounds.MathlibTM2.Fast
