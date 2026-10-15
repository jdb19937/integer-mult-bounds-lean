module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainSourceStages
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainPrimitiveEntry

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Schoenhage.Schedule (topN)
open Computability

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

attribute [local irreducible] mnT mnQ

noncomputable section

open Filter

def compactMainChain : CompactMnPr CompactMainProc (prime+mnKa) :=
  .seq (compactMainStage (mnDigits .rx)) <| .seq (srcDirectP compactSrcM (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer))) <|
  .seq (compactMainStage (mnMv (.src (.x .sb)) (.io .hx))) <|
  .seq (compactMainStage (mnDigits .ry)) <| .seq (srcDirectP compactSrcM (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer))) <|
  .seq (compactMainStage (mnMv (.io .hx) (.src (.v (.cm .xs))))) <| .seq (compactMainStage (mnMv (.src (.x .sb)) (.src (.v (.cm .ys))))) <|
  .seq (compactMainStage mnPoint) <| .seq (compactMainStage (uclear (mnCm .xs))) <| .seq (compactMainStage (uclear (mnCm .ys))) <|
  .seq (compactMainStage (mnMv (.src (.v (.cm .out))) (.src (.x .sb)))) <|
  .seq (oppDirectP compactSrcM (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer))) <|
  .seq (compactMainStage (mnMv (.src (.c .str)) (.rnd .src))) <|
  .seq (compactMainStage mnRound) (compactMainStage (mnMv (.rnd .dst) (.out .dat)))


theorem compactMainChain_eventually : ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (main : CompactMnPr CompactMainProc (prime+mnKa)) (_hA : 96 ≤ prime + mnKa) (hbig : Big n)
    (_hsmall : 2 * d n * p n ^ 2 ≤ Mult.Sizes.T n * logT n)
    (_hEs : 9 * (2 : ℝ) ^ Mult.Sizes.gamma n * Mult.Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {W : ℕ} (_hw : p n + Chirp.chirpGuard (d n) + 3 ≤ dsW n) (_hwW : dsW n < W)
    (_hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (_hWB : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (13 * p n + 8) < 2 ^ W)
    (_hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (_hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX 6) (prime + mnKa)} {σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + mnKa + 4))}
    {restA restB axsA axsB : List (Fin (prime + mnKa + 4))} (E : SrcF 6 (prime + mnKa))
    (_hE : SrcBase mnM E n (dsW n) W (srcHd0 hbig) V₀ σ₀
      (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA))
      (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) axsA axsB)
    (_hC : SrcCrtBase E.c E.cb n (dsW n)) (_hln : E.a .ln = []) (_hstr : E.c .str = [])
    (_hsb : E.x .sb = [])
    (g : MnR → List (Fin (prime + mnKa + 4))) (x y : ℕ) (_hsx : Nat.size x ≤ n)
    (_hsy : Nat.size y ≤ n)
    (_hrx : g (.io .rx) = (encodingNatBool.encode x).map bitSymbol)
    (_hry : g (.io .ry) = (encodingNatBool.encode y).map bitSymbol)
    (_hdbn : (g (.io .dbn)).length = b n) (_hdpn : (g (.io .dpn)).length = p n)
    (_hdwn : (g (.io .dwn)).length = (dsW n)) (_hdsn : (g (.io .dsn)).length = S n)
    (_htpl : g (.io .tpl) = []) (_htmp : g (.io .tmp) = []) (_hstmp : g (.io .stmp) = [])
    (_hacc : g (.io .acc) = []) (_hhx : g (.io .hx) = []) (_hsp : g (.io .sp) = [])
    (_hrsrc : g (.rnd .src) = []) (_hrdst : g (.rnd .dst) = [])
    (_hrwn : (g (.rnd .wn)).length = (dsW n)) (_hrmn : (g (.rnd .mn)).length = mnMw n (dsW n))
    (_hrnn : (g (.rnd .nn)).length = topN (mnMw n (dsW n)))
    (_hrsq : g (.rnd .sq) = binSyms (mnMw n (dsW n)) (S n * S n))
    (_hrbn : (g (.rnd .bn)).length = b n) (_hrpn : (g (.rnd .pn)).length = p n)
    (_hrwo : (g (.rnd .wo)).length = mnWo n) (_hrtm : g (.rnd .tm) = [])
    (_hru1 : g (.rnd .u1) = []) (_hrsg : g (.rnd .sg) = []) (_hrxa : g (.rnd .xa) = [])
    (_hrxc : g (.rnd .xc) = []) (_hrcy : g (.rnd .cy) = []) (_hracc : g (.rnd .acc) = [])
    (_hodat : g (.out .dat) = []),
    ∃ (F' : SrcF 6 (prime + mnKa)) (g' : MnR → List (Fin (prime + mnKa + 4))),
      SrcRuns (compactMainEntryTable main) compactMnRg compactSrcM.ι (compactMainStablePre n) compactMainChain (mnGlob E g) (mnGlob F' g')
        (mnChainCost n (dsW n)
          (srcDirectPCost compactSrcM n (dsW n) W (compactSynRetunedFwdCost n (compactBlCL n)) (compactSynRetunedOppCost n (compactBlCL' n)) (srcHd0 hbig) V₀ σ₀
              (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA))
              (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) +
            srcDirectPCost compactSrcM n (dsW n) W (compactSynRetunedFwdCost n (compactBlCL n)) (compactSynRetunedOppCost n (compactBlCL' n)) (srcHd0 hbig)
              (preCfgA V₀ crtHd n (dsW n) W (srcHd0 hbig)
                (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA)) (d n - 1))
              (preCfgB σ₀ crtHd n (dsW n) W (srcHd0 hbig)
                (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) (d n - 1))
              (preRecsA n W (srcHd0 hbig) 0 ++ restA) (preRecsB n W (srcHd0 hbig) 0 ++ restB) +
            oppDirectPCost compactSrcM n (dsW n) W (compactSynRetunedFwdCost n (compactBlCL n)) (compactSynRetunedOppCost n (compactBlCL' n)) (srcHd0 hbig)
              (preCfgA (preCfgA V₀ crtHd n (dsW n) W (srcHd0 hbig)
                (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA)) (d n - 1))
                crtHd n (dsW n) W (srcHd0 hbig) (preRecsA n W (srcHd0 hbig) 0 ++ restA) (d n - 1))
              (preCfgB (preCfgB σ₀ crtHd n (dsW n) W (srcHd0 hbig)
                (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) (d n - 1))
                crtHd n (dsW n) W (srcHd0 hbig) (preRecsB n W (srcHd0 hbig) 0 ++ restB) (d n - 1))
              restA restB) + 12) ∧
      g' (.out .dat) = mnWords mnKa n x y ∧ ∀ r, r ≠ .dat → g' (.out r) = g (.out r) := by
  filter_upwards [compactMainSrcFwd_eventually, compactMainSrcOpp_eventually] with n hF hO
  intro main hA hbig hsmall hEs W hw hwW hWA hWB hWs hWk V₀ σ₀ restA restB axsA axsB E hE hC hln hstr hsb g x y hsx hsy hrx hry hdbn hdpn hdwn hdsn htpl htmp hstmp hacc hhx hsp hrsrc hrdst hrwn hrmn hrnn hrsq hrbn hrpn hrwo hrtm hru1 hrsg hrxa hrxc hrcy hracc hodat
  set hd0 := srcHd0 hbig with hhd0
  have hP := compactMainStablePre_framed n
  have hb1 : 1 ≤ b n := one_le_b hbig.1
  have hpb : b n + 2 ≤ p n := by unfold p; omega
  have hpw : p n ≤ (dsW n) := by omega
  have hw1 : 1 ≤ (dsW n) := by omega
  have hA4 : 4 ≤ prime + mnKa := by omega
  have hS0 : NeZero (∏ i, s n i) := ⟨by
    have := hbig.T_lt_two_S; have := hbig.S_lt_T; unfold Sizes.S at *; omega⟩
  -- the operands
  set ux := mnU n x with hux
  set uy := mnU n y with huy
  have hux1 : ‖ux‖ ≤ 1 / 2 := mn_scaledDigits_norm (one_le_b hbig.1) _
  have huy1 : ‖uy‖ ≤ 1 / 2 := mn_scaledDigits_norm (one_le_b hbig.1) _
  have huxf : ∀ k, IsFixed (p n) (ux k) := mn_scaledDigits_fixed hpb _
  have huyf : ∀ k, IsFixed (p n) (uy k) := mn_scaledDigits_fixed hpb _
  have hFx := mn_srcMap_norm hbig hsmall hEs hux1
  have hFy := mn_srcMap_norm hbig hsmall hEs huy1
  set Y := mnY n x y with hY
  have hY1 : ‖Y‖ ≤ 1 / 2 := mn_rdV_norm _ hFx hFy
  have hYf : ∀ k, IsFixed (p n) (Y k) := fun k => isFixed_rhoC _ _
  have hOY := mn_oppMap_norm hbig hsmall hEs hY1
  set BX := cstream (prime + mnKa) (dsW n) (srcPad (p n) (s n) (t n) (srcMap n ux)) with hBX
  set BY := cstream (prime + mnKa) (dsW n) (srcPad (p n) (s n) (t n) (srcMap n uy)) with hBY
  set PR := cstream (prime + mnKa) (dsW n) (cstNumBox (p n) (t n)
    (rdV (p n) (mnPad (s n) (t n) (srcMap n ux) * mnPad (s n) (t n) (srcMap n uy)))) with hPR
  have hPR : PR = cstream (prime + mnKa) (dsW n) (srcPad (p n) (s n) (t n) Y) := by
    rw [hPR, mn_rdV_pad, ← mn_srcPad_eq]
  set CO := cstream (prime + mnKa) (dsW n) (srcCoef (p n) (∏ i, s n i) (oppMap n Y)) with hCO
  have hTw : BX.length = (∏ i, t n i) * (dsW n) := by rw [hBX, length_cstream, src_length_pad]
  have hTwY : BY.length = (∏ i, t n i) * (dsW n) := by rw [hBY, length_cstream, src_length_pad]
  have eS : S n = ∏ i, s n i := rfl
  -- 1. the digits of `x`
  have hxs : binaryValue (bitsMSB n x) = x := binaryValue_bitsMSB_of_size hsx
  have s1 := mn_digits_runs (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) .rx (Or.inl rfl) hb1 hpb hpw x
    (bitsMSB n x) hxs (mn_digits_len hbig x) E g hrx hdbn hdpn hdwn hdsn htpl htmp hstmp hacc
  rw [eS, mn_digitStream_eq hpb, hstr, List.append_nil] at s1
  obtain ⟨F₁, hF₁⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { E with
        c := Function.update E.c .str
          (cstream (prime + mnKa) (dsW n) (srcCoef (p n) (∏ i, s n i) ux)) } := ⟨_, rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g' : MnR → List (Fin (prime + mnKa + 4)), g' = Function.update g (.io .rx) [] :=
    ⟨_, rfl⟩
  rw [← hF₁, ← hg₁] at s1
  -- 2. the source transform of `x`
  have hE₁ : SrcBase mnM F₁ n (dsW n) W hd0 V₀ σ₀
      (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
      (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) axsA axsB := by
    subst hF₁; exact hE.of_eq (fun _ _ => rfl) rfl rfl rfl rfl (fun _ _ => rfl)
  have hC₁ : SrcCrtBase F₁.c F₁.cb n (dsW n) := by subst hF₁; exact hC.upd_str _
  have s2 := hF main hbig hsmall hEs hwW hWA hWB hWs hWk F₁
    hE₁ hC₁ (by subst hF₁; exact hln) ux hux1 huxf (by subst hF₁; simp) g₁ (by subst hg₁; simp [hdpn])
  obtain ⟨F₂, hF₂⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₁ with
        a := (rsaWith (preCfgA V₀ crtHd n (dsW n) W hd0
          (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1)) [] axsA []).get
        b := rsbWith (preCfgB σ₀ crtHd n (dsW n) W hd0
          (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1)) [] axsB []
        c := Function.update F₁.c .str []
        x := Function.update F₁.x .sb (BX ++ F₁.x .sb) } := ⟨_, rfl⟩
  replace s2 : SrcRuns (compactMainEntryTable main) compactMnRg compactSrcM.ι (compactMainStablePre n) (srcDirectP compactSrcM (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer))) (mnGlob F₁ g₁)
      (mnGlob F₂ g₁) (srcDirectPCost compactSrcM n (dsW n) W (compactSynRetunedFwdCost n (compactBlCL n)) (compactSynRetunedOppCost n (compactBlCL' n)) hd0 V₀ σ₀
        (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
        (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB))) := by subst hF₂; exact s2
  have hF₂sb : F₂.x .sb = BX := by subst hF₂ hF₁; simp [hsb]
  -- 3. park the first transform
  have s3 := mn_mv_sb_hx (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) F₂ g₁ (by subst hg₁; simp [hsp])
  obtain ⟨F₃, hF₃⟩ : ∃ F : SrcF 6 (prime + mnKa), F = { F₂ with x := Function.update F₂.x .sb [] } :=
    ⟨_, rfl⟩
  obtain ⟨g₃, hg₃⟩ : ∃ g' : MnR → List (Fin (prime + mnKa + 4)),
      g' = Function.update g₁ (.io .hx) BX := ⟨_, rfl⟩
  replace s3 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) (mnMv (.src (.x .sb)) (.io .hx))
      (mnGlob F₂ g₁) (mnGlob F₃ g₃) (4 * ((∏ i, t n i) * (dsW n)) + 4) := by
    rw [hF₂sb, hTw, show g₁ (.io .hx) = [] by subst hg₁; simp [hhx], List.append_nil] at s3
    rw [hF₃, hg₃]; exact s3
  -- 4. the digits of `y`
  have hys : binaryValue (bitsMSB n y) = y := binaryValue_bitsMSB_of_size hsy
  have s4 := mn_digits_runs (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) .ry (Or.inr rfl) hb1 hpb hpw y
    (bitsMSB n y) hys (mn_digits_len hbig y) F₃ g₃ (by subst hg₃ hg₁; simp [hry])
    (by subst hg₃ hg₁; simp [hdbn]) (by subst hg₃ hg₁; simp [hdpn]) (by subst hg₃ hg₁; simp [hdwn])
    (by subst hg₃ hg₁; simp [hdsn]) (by subst hg₃ hg₁; simp [htpl]) (by subst hg₃ hg₁; simp [htmp])
    (by subst hg₃ hg₁; simp [hstmp]) (by subst hg₃ hg₁; simp [hacc])
  have hF₃str : F₃.c .str = [] := by subst hF₃ hF₂; simp
  rw [eS, mn_digitStream_eq hpb, hF₃str, List.append_nil] at s4
  obtain ⟨F₄, hF₄⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₃ with
        c := Function.update F₃.c .str
          (cstream (prime + mnKa) (dsW n) (srcCoef (p n) (∏ i, s n i) uy)) } := ⟨_, rfl⟩
  obtain ⟨g₄, hg₄⟩ : ∃ g' : MnR → List (Fin (prime + mnKa + 4)),
      g' = Function.update g₃ (.io .ry) [] := ⟨_, rfl⟩
  replace s4 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) (mnDigits .ry) (mnGlob F₃ g₃) (mnGlob F₄ g₄)
      (digitCost (b n) (p n) (dsW n) (∏ i, s n i)) := by rw [hF₄, hg₄]; exact s4
  -- 5. the source transform of `y`
  have hE₄ : SrcBase mnM F₄ n (dsW n) W hd0
      (preCfgA V₀ crtHd n (dsW n) W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1))
      (preCfgB σ₀ crtHd n (dsW n) W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1))
      (preRecsA n W hd0 0 ++ restA) (preRecsB n W hd0 0 ++ restB) axsA axsB := by
    refine SrcBase.next (E := E) hE (fun r _ => by subst hF₄ hF₃ hF₂; rfl)
      (by subst hF₄ hF₃ hF₂; rfl) (by subst hF₄ hF₃ hF₂ hF₁; rfl) (by subst hF₄ hF₃ hF₂ hF₁; rfl)
      (by subst hF₄ hF₃ hF₂ hF₁; rfl) (fun j hj => ?_)
    subst hF₄ hF₃ hF₂ hF₁
    simp [Function.update_of_ne hj]
  have hC₄ : SrcCrtBase F₄.c F₄.cb n (dsW n) := by
    subst hF₄ hF₃ hF₂ hF₁; exact ((hC.upd_str _).upd_str _).upd_str _
  have s5 := hF main hbig hsmall hEs hwW hWA hWB hWs hWk F₄
    hE₄ hC₄ (by subst hF₄ hF₃ hF₂; rfl) uy huy1 huyf (by subst hF₄; simp) g₄ (by subst hg₄ hg₃ hg₁; simp [hdpn])
  obtain ⟨F₅, hF₅⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₄ with
        a := (rsaWith (preCfgA (preCfgA V₀ crtHd n (dsW n) W hd0
          (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1)) crtHd n (dsW n) W hd0
          (preRecsA n W hd0 0 ++ restA) (d n - 1)) [] axsA []).get
        b := rsbWith (preCfgB (preCfgB σ₀ crtHd n (dsW n) W hd0
          (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1)) crtHd n (dsW n) W hd0
          (preRecsB n W hd0 0 ++ restB) (d n - 1)) [] axsB []
        c := Function.update F₄.c .str []
        x := Function.update F₄.x .sb (BY ++ F₄.x .sb) } := ⟨_, rfl⟩
  replace s5 : SrcRuns (compactMainEntryTable main) compactMnRg compactSrcM.ι (compactMainStablePre n) (srcDirectP compactSrcM (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer))) (mnGlob F₄ g₄)
      (mnGlob F₅ g₄) (srcDirectPCost compactSrcM n (dsW n) W (compactSynRetunedFwdCost n (compactBlCL n)) (compactSynRetunedOppCost n (compactBlCL' n)) hd0
        (preCfgA V₀ crtHd n (dsW n) W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1))
        (preCfgB σ₀ crtHd n (dsW n) W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1))
        (preRecsA n W hd0 0 ++ restA) (preRecsB n W hd0 0 ++ restB)) := by subst hF₅; exact s5
  have hF₅sb : F₅.x .sb = BY := by subst hF₅ hF₄ hF₃; simp
  have hg₄hx : g₄ (.io .hx) = BX := by subst hg₄ hg₃; simp
  have hg₄sp : g₄ (.io .sp) = [] := by subst hg₄ hg₃ hg₁; simp [hsp]
  -- 6, 7. both transforms onto the product registers
  have s6 := mn_mv_hx_xs (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) F₅ g₄ hg₄sp
  have hF₅v : F₅.v = E.v := by subst hF₅ hF₄ hF₃ hF₂ hF₁; rfl
  rw [hg₄hx, hF₅v, hE.v.cmxs, List.append_nil, hTw] at s6
  obtain ⟨F₆, hF₆⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₅ with v := Function.update E.v (.cm .xs) BX } := ⟨_, rfl⟩
  obtain ⟨g₆, hg₆⟩ : ∃ g' : MnR → List (Fin (prime + mnKa + 4)),
      g' = Function.update g₄ (.io .hx) [] := ⟨_, rfl⟩
  replace s6 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) (mnMv (.io .hx) (.src (.v (.cm .xs))))
      (mnGlob F₅ g₄) (mnGlob F₆ g₆) (4 * ((∏ i, t n i) * (dsW n)) + 4) := by
    rw [hF₆, hg₆]; exact s6
  have hg₆sp : g₆ (.io .sp) = [] := by subst hg₆; simp [hg₄sp]
  have s7 := mn_mv_sb_ys (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) F₆ g₆ hg₆sp
  have hF₆sb : F₆.x .sb = BY := by subst hF₆; exact hF₅sb
  have hF₆ys : F₆.v (.cm .ys) = [] := by subst hF₆; simp [hE.v.cmys]
  rw [hF₆sb, hF₆ys, List.append_nil, hTwY] at s7
  obtain ⟨F₇, hF₇⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₆ with
        x := Function.update F₆.x .sb []
        v := Function.update F₆.v (.cm .ys) BY } := ⟨_, rfl⟩
  replace s7 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) (mnMv (.src (.x .sb)) (.src (.v (.cm .ys))))
      (mnGlob F₆ g₆) (mnGlob F₇ g₆) (4 * ((∏ i, t n i) * (dsW n)) + 4) := by rw [hF₇]; exact s7
  -- 8. the pointwise product
  have hF₇v : F₇.v = Function.update (Function.update E.v (.cm .xs) BX) (.cm .ys) BY := by
    subst hF₇ hF₆; rfl
  have hF₇sb : F₇.x .sb = [] := by subst hF₇; simp
  have s8 := mn_point_runs (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) hA hw1 hpw (t n)
    (mnPad (s n) (t n) (srcMap n ux)) (mnPad (s n) (t n) (srcMap n uy))
    (fun _ => mn_pad_fixed (mn_srcMap_fixed hd0 ux) _)
    (fun _ => mn_pad_fixed (mn_srcMap_fixed hd0 uy) _)
    (fun _ => mn_pad_fits (fun k => mn_fits ((norm_le_pi_norm _ k).trans hFx) (by omega)) _)
    (fun _ => mn_pad_fits (fun k => mn_fits ((norm_le_pi_norm _ k).trans hFy) (by omega)) _)
    (mnGlob F₇ g₆)
    (cst_ready_of_eq hE.v.ready fun c h1 h2 _ _ _ _ => by
      simp only [mnGlob_src, SrcF.get_v, hF₇v]
      rw [Function.update_of_ne (by simpa using h2), Function.update_of_ne (by simpa using h1)])
    (by simp only [mnGlob_src, SrcF.get_v, hF₇v]; simp [hBX, mn_srcPad_eq])
    (by simp only [mnGlob_src, SrcF.get_v, hF₇v]; simp [hBY, mn_srcPad_eq])
    (by simp [hF₇v, hE.v.cmxsv]) (by simp [hF₇v, hE.v.cmysv]) (by simp [hF₇v, hE.v.cmacc])
  have hF₇out : F₇.v (.cm .out) = [] := by simp [hF₇v, hE.v.cmout]
  simp only [mnGlob_src, SrcF.get_v, hF₇out, List.append_nil] at s8
  rw [mn_upd_v] at s8
  obtain ⟨F₈, hF₈⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₇ with v := Function.update F₇.v (.cm .out) PR } := ⟨_, rfl⟩
  replace s8 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) mnPoint (mnGlob F₇ g₆) (mnGlob F₈ g₆)
      ((∏ i, t n i) * (cmulCost mnT (dsW n) + 6 * (dsW n) + 2) + 8) := by rw [hF₈]; exact s8
  -- 9, 10. clear the operands
  have s9 := mn_clear_cm (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) .xs F₈ g₆
  have hF₈xs : F₈.v (.cm .xs) = BX := by subst hF₈; simp [hF₇v]
  rw [hF₈xs, hTw] at s9
  obtain ⟨F₉, hF₉⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₈ with v := Function.update F₈.v (.cm .xs) [] } := ⟨_, rfl⟩
  replace s9 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) (uclear (mnCm .xs)) (mnGlob F₈ g₆)
      (mnGlob F₉ g₆) (2 * ((∏ i, t n i) * (dsW n)) + 2) := by rw [hF₉]; exact s9
  have s10 := mn_clear_cm (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) .ys F₉ g₆
  have hF₉ys : F₉.v (.cm .ys) = BY := by subst hF₉ hF₈; simp [hF₇v]
  rw [hF₉ys, hTwY] at s10
  obtain ⟨F₁₀, hF₁₀⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₉ with v := Function.update F₉.v (.cm .ys) [] } := ⟨_, rfl⟩
  replace s10 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) (uclear (mnCm .ys)) (mnGlob F₉ g₆)
      (mnGlob F₁₀ g₆) (2 * ((∏ i, t n i) * (dsW n)) + 2) := by rw [hF₁₀]; exact s10
  -- 11. the product onto `x .sb`
  have s11 := mn_mv_out_sb (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) F₁₀ g₆ hg₆sp
  have hF₁₀out : F₁₀.v (.cm .out) = PR := by subst hF₁₀ hF₉ hF₈; simp
  have hF₁₀sb : F₁₀.x .sb = [] := by subst hF₁₀ hF₉ hF₈; exact hF₇sb
  have hPRl : PR.length = (∏ i, t n i) * (dsW n) := by rw [hPR, length_cstream, src_length_pad]
  rw [hF₁₀out, hF₁₀sb, List.append_nil, hPRl] at s11
  obtain ⟨F₁₁, hF₁₁⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₁₀ with
        v := Function.update F₁₀.v (.cm .out) []
        x := Function.update F₁₀.x .sb PR } := ⟨_, rfl⟩
  replace s11 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) (mnMv (.src (.v (.cm .out))) (.src (.x .sb)))
      (mnGlob F₁₀ g₆) (mnGlob F₁₁ g₆) (4 * ((∏ i, t n i) * (dsW n)) + 4) := by rw [hF₁₁]; exact s11
  -- 12. the opposite transform
  have hF₁₁v : F₁₁.v = E.v := by
    subst hF₁₁ hF₁₀ hF₉ hF₈
    rw [hF₇v]
    funext c
    by_cases h1 : c = .cm .out
    · subst h1; simp [hE.v.cmout]
    by_cases h2 : c = .cm .ys
    · subst h2; simp [hE.v.cmys]
    by_cases h3 : c = .cm .xs
    · subst h3; simp [hE.v.cmxs]
    simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  have hE₁₁ : SrcBase mnM F₁₁ n (dsW n) W hd0
      (preCfgA (preCfgA V₀ crtHd n (dsW n) W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
        (d n - 1)) crtHd n (dsW n) W hd0 (preRecsA n W hd0 0 ++ restA) (d n - 1))
      (preCfgB (preCfgB σ₀ crtHd n (dsW n) W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB))
        (d n - 1)) crtHd n (dsW n) W hd0 (preRecsB n W hd0 0 ++ restB) (d n - 1))
      restA restB axsA axsB := by
    refine SrcBase.next (E := F₄) hE₄ (fun r _ => by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl)
      (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl)
      (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl)
      (by rw [hF₁₁v]; subst hF₄ hF₃ hF₂ hF₁; rfl)
      (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl) (fun j hj => ?_)
    subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅
    simp [Function.update_of_ne hj]
  have hC₁₁ : SrcCrtBase F₁₁.c F₁₁.cb n (dsW n) := by
    subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; exact hC₄.upd_str _
  have s12 := hO main hbig hsmall hEs hwW hWA hWB hWs hWk
    F₁₁ hE₁₁ hC₁₁ (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl)
    (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; simp) Y hY1 hYf
    (by rw [← hPR]; subst hF₁₁; simp) g₆ (by subst hg₆ hg₄ hg₃ hg₁; simp [hdpn])
  obtain ⟨F₁₂, hF₁₂⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₁₁ with
        a := (rsaWith (preCfgA (preCfgA (preCfgA V₀ crtHd n (dsW n) W hd0
          (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1)) crtHd n (dsW n) W hd0
          (preRecsA n W hd0 0 ++ restA) (d n - 1)) crtHd n (dsW n) W hd0 restA (d n - 1)) [] axsA []).get
        b := rsbWith (preCfgB (preCfgB (preCfgB σ₀ crtHd n (dsW n) W hd0
          (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1)) crtHd n (dsW n) W hd0
          (preRecsB n W hd0 0 ++ restB) (d n - 1)) crtHd n (dsW n) W hd0 restB (d n - 1)) [] axsB []
        c := Function.update F₁₁.c .str CO
        x := Function.update F₁₁.x .sb [] } := ⟨_, rfl⟩
  replace s12 : SrcRuns (compactMainEntryTable main) compactMnRg compactSrcM.ι (compactMainStablePre n) (oppDirectP compactSrcM (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer))) (mnGlob F₁₁ g₆)
      (mnGlob F₁₂ g₆) (oppDirectPCost compactSrcM n (dsW n) W (compactSynRetunedFwdCost n (compactBlCL n)) (compactSynRetunedOppCost n (compactBlCL' n)) hd0
        (preCfgA (preCfgA V₀ crtHd n (dsW n) W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
          (d n - 1)) crtHd n (dsW n) W hd0 (preRecsA n W hd0 0 ++ restA) (d n - 1))
        (preCfgB (preCfgB σ₀ crtHd n (dsW n) W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB))
          (d n - 1)) crtHd n (dsW n) W hd0 (preRecsB n W hd0 0 ++ restB) (d n - 1))
        restA restB) := by subst hF₁₂; exact s12
  -- 13. the coefficient stream onto the rounding stage
  have s13 := mn_mv_str_rnd (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) F₁₂ g₆ hg₆sp
  have hF₁₂str : F₁₂.c .str = CO := by subst hF₁₂; simp
  have hg₆rsrc : g₆ (.rnd .src) = [] := by subst hg₆ hg₄ hg₃ hg₁; simp [hrsrc]
  have hCOl : CO.length = S n * (dsW n) := by rw [hCO, length_cstream, src_length_coef]; rfl
  rw [hF₁₂str, hg₆rsrc, List.append_nil, hCOl] at s13
  obtain ⟨F₁₃, hF₁₃⟩ : ∃ F : SrcF 6 (prime + mnKa), F =
      { F₁₂ with c := Function.update F₁₂.c .str [] } := ⟨_, rfl⟩
  obtain ⟨g₁₃, hg₁₃⟩ : ∃ g' : MnR → List (Fin (prime + mnKa + 4)),
      g' = Function.update g₆ (.rnd .src) CO := ⟨_, rfl⟩
  replace s13 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) (mnMv (.src (.c .str)) (.rnd .src))
      (mnGlob F₁₂ g₆) (mnGlob F₁₃ g₁₃) (4 * (S n * (dsW n)) + 4) := by rw [hF₁₃, hg₁₃]; exact s13
  -- 14. the rounding stage
  have hgr : ∀ r : RndReg, r ≠ .src → g₁₃ (.rnd r) = g (.rnd r) := by
    intro r hr; subst hg₁₃ hg₆ hg₄ hg₃ hg₁; simp [hr]
  have hSm : S n * S n < 2 ^ mnMw n (dsW n) := by
    have h1 := Nat.lt_size_self (S n)
    calc S n * S n < 2 ^ Nat.size (S n) * 2 ^ Nat.size (S n) := Nat.mul_lt_mul'' h1 h1
      _ = 2 ^ (2 * Nat.size (S n)) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ mnMw n (dsW n) := Nat.pow_le_pow_right (by norm_num) (by unfold mnMw; omega)
  have s14 := mn_round_runs (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) hA4 (m := mnMw n (dsW n)) (b' := b n)
    (p' := p n) (W := mnWo n) (S' := ∏ i, s n i) hw1 (by unfold mnMw; omega) hSm
    (fun i => numer (p n) (oppMap n Y ((i : ℕ) : ZMod (∏ i, s n i))))
    (fun i => (mn_fits ((norm_le_pi_norm _ _).trans hOY) (by omega)).1)
    (mnGlob F₁₃ g₁₃) (by simp only [mnGlob_rnd]; rw [hg₁₃, Function.update_self, hCO,
      mn_coef_stream])
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrwn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrmn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrnn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrsq)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrbn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrpn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrwo)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrtm)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hru1)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrsg)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrxa)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrxc)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrcy)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hracc)
  simp only [mnGlob_rnd] at s14
  rw [hgr _ (by decide), hrdst, List.append_nil, mn_upd_g _ _ (by intro x h; cases h),
    mn_upd_g _ _ (by intro x h; cases h)] at s14
  obtain ⟨g₁₄, hg₁₄⟩ : ∃ g' : MnR → List (Fin (prime + mnKa + 4)),
      g' = Function.update (Function.update g₁₃ (.rnd .src) []) (.rnd .dst) (mnWords mnKa n x y) :=
    ⟨_, rfl⟩
  replace s14 : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) mnRound (mnGlob F₁₃ g₁₃) (mnGlob F₁₃ g₁₄)
      (roundStageCost mnT (mnMw n (dsW n)) (dsW n) (b n) (p n) (mnWo n) (S n)) := by
    rw [hg₁₄]; exact s14
  -- 15. the words onto the output stage
  have hg₁₄sp : g₁₄ (.io .sp) = [] := by subst hg₁₄ hg₁₃; simp [hg₆sp]
  have s15 := mn_mv_dst_dat (body := mnBody mnLb (.act .done)) (Pre := fun _ => True) F₁₃ g₁₄ hg₁₄sp
  have hg₁₄dst : g₁₄ (.rnd .dst) = mnWords mnKa n x y := by subst hg₁₄; simp
  have hg₁₄dat : g₁₄ (.out .dat) = [] := by subst hg₁₄ hg₁₃ hg₆ hg₄ hg₃ hg₁; simp [hodat]
  have hWl : (mnWords mnKa n x y).length = S n * mnWo n := by
    rw [mnWords, mn_length_words, List.length_ofFn]; rfl
  rw [hg₁₄dst, hg₁₄dat, List.append_nil, hWl] at s15
  -- the chain
  have hd : ∀ r j, compactMnRg r ≠ compactSrcM.ι j := by
    intro r j h
    exact mnRg_ne_ι r j (compactMnLegacyReg_injective (by simpa only [compactMnLegacyReg_rg, compactSrcM_ι] using h))
  let lift := fun {p ρ ρ' c} (h : SrcRuns (mnBody mnLb (.act .done)) mnRg mnι (fun _ => True) p ρ ρ' c) hp =>
    compactMainEntry_srcRuns main (.act .done)
      (compactMainBody_srcRuns (mnBody mnLb (.act .done)) Cost.brDirs (Pre' := compactMainStablePre n) (fun _ _ => True.intro) h) hp
  have s1 := lift s1 (compactMainDigits_calls _)
  have s3 := lift s3 (compactMainMv_calls _ _)
  have s4 := lift s4 (compactMainDigits_calls _)
  have s6 := lift s6 (compactMainMv_calls _ _)
  have s7 := lift s7 (compactMainMv_calls _ _)
  have s8 := lift s8 (compactMainPoint_calls)
  have s9 := lift s9 (compactMainClearCm_calls _)
  have s10 := lift s10 (compactMainClearCm_calls _)
  have s11 := lift s11 (compactMainMv_calls _ _)
  have s13 := lift s13 (compactMainMv_calls _ _)
  have s14 := lift s14 (compactMainRound_calls)
  have s15 := lift s15 (compactMainMv_calls _ _)

  refine ⟨F₁₃, _, (s1.seq hd hP (s2.seq hd hP (s3.seq hd hP (s4.seq hd hP (s5.seq hd hP
    (s6.seq hd hP (s7.seq hd hP (s8.seq hd hP (s9.seq hd hP (s10.seq hd hP (s11.seq hd hP
    (s12.seq hd hP (s13.seq hd hP (s14.seq hd hP s15)))))))))))))).mono (le_of_eq ?_), ?_, ?_⟩
  · simp only [mnChainCost, mnGlue, eS]
    ring
  · simp
  · intro r hr
    subst hg₁₄ hg₁₃ hg₆ hg₄ hg₃ hg₁
    simp [hr]


end
end IntegerMultBounds.MathlibTM2.Fast.Main
