module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainChainR
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainChainEntry
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainOutput

/-! The rounded main chain from the distributed register file, and the coefficients and the
carry stage for any box convolution with the guarantee `BoxConvSpec`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Schoenhage.Schedule (topN)
open Computability
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM
open Filter
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.MathlibTM2.Fast.TableVM Filter
open IntegerMultBounds IntegerMultBounds.MathlibTM2 Filter Asymptotics
open IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack
open Computability
open IntegerMultBounds.Schoenhage.Schedule (topN)
attribute [local irreducible] mnT mnQ
noncomputable section


open Filter

theorem compactMainChainR_exec_eventually : ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (main : CompactMnPr CompactMainProc (prime+mnKa)) (_hA : 96 ≤ prime + mnKa) (hbig : Big n)
    (hg : CompactSynRetunedGeom n)
    (_hsmall : 2 * d n * p n ^ 2 ≤ Mult.Sizes.T n * logT n)
    (_hEs : 9 * (2 : ℝ) ^ Mult.Sizes.gamma n * Mult.Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {W : ℕ} (_hw : p n + Chirp.chirpGuard (d n) + 3 ≤ dsW n) (_hwW : dsW n < W)
    (_hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (_hWB : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (_hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (_hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX 6) (prime + mnKa)} {σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + mnKa + 4))}
    {restA restB axsA axsB : List (Fin (prime + mnKa + 4))} (E : SrcF 6 (prime + mnKa))
    (_hE : SrcBase mnM E n (dsW n) W (srcHd0 hbig) V₀ σ₀
      (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA))
      (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) axsA axsB)
    (_hC : SrcCrtBase E.c E.cb n (dsW n)) (_hln : E.a .ln = []) (_hstr : E.c .str = [])
    (_hsb : E.x .sb = []) (x y : ℕ) (_hsx : Nat.size x ≤ n) (_hsy : Nat.size y ≤ n)
    (v : HS compactMnT compactMnQ (prime + mnKa) Unit) (St : Stacks compactMnT (prime + mnKa))
    (_hstable : compactMainStablePre n St)
    (_hsrc : ∀ r, St.R (compactMnRg (.src r)) = E.get r) (_hM : MnMid (embStk compactMnLegacyReg St) x y n)
    (_hdwn : (St.R (compactMnRg (.io .dwn))).length = (dsW n)) (_hrwn : (St.R (compactMnRg (.rnd .wn))).length = (dsW n))
    (_hrmn : (St.R (compactMnRg (.rnd .mn))).length = mnMw n (dsW n))
    (_hrnn : (St.R (compactMnRg (.rnd .nn))).length = topN (mnMw n (dsW n)))
    (_hrsq : St.R (compactMnRg (.rnd .sq)) = binSyms (mnMw n (dsW n)) (S n * S n))
    (_hrwo : (St.R (compactMnRg (.rnd .wo))).length = mnWo n),
    ∃ (v' : HS compactMnT compactMnQ (prime + mnKa) Unit) (St' : Stacks compactMnT (prime + mnKa)) (m : ℕ),
      m ≤ mnChainCost n (dsW n) (compactMainRunsAt n (dsW n) W
        (compactSynRetunedFwdCostR n (compactBlCL n)) (compactSynRetunedOppCostR n (compactBlCL' n))
        (srcHd0 hbig) V₀ σ₀ restA restB) + 12 ∧
      Exec (compactMainEntryTableR main) compactMainChainR (mk v St) m (mk v' St') ∧
      St'.inp = St.inp ∧ St'.out = St.out ∧ St'.L = St.L ∧
      St'.R (compactMnRg (.out .dat)) = mnWordsG mnKa n (compactRetunedCb n hbig hg) x y ∧
      ∀ r, r ≠ .dat → St'.R (compactMnRg (.out r)) = St.R (compactMnRg (.out r)) := by
  filter_upwards [compactMainChainR_eventually] with n hchain
  intro main hA hbig hg hsmall hEs W hw hwW hWA hWB hWs hWk V₀ σ₀ restA restB axsA axsB E hE hC hln hstr hsb x y hsx hsy v St hstable hsrc hM hdwn hrwn hrmn hrnn hrsq hrwo
  have he : ∀ r : MnR, mnDistKeep r → r ∉ mnUsRegs → St.R (compactMnRg r) = [] := by
    intro r hr hu
    simpa only [embStk_R, compactMnLegacyReg_rg] using hM.rest r hr hu
  have hdbn := hM.dbn
  have hdpn := hM.dpn
  have hdsn := hM.dsn
  have hrbn := hM.rbn
  have hrpn := hM.rpn
  simp only [embStk_R, mnIo, mnRnd, compactMnLegacyReg_rg] at hdbn hdpn hdsn hrbn hrpn
  obtain ⟨F', g', hrun, hdat, hout⟩ := hchain main hA hbig hg hsmall hEs
    hw hwW hWA hWB hWs hWk E hE hC hln hstr hsb (fun r => St.R (compactMnRg r)) x y hsx hsy
    (by simpa only [embStk_R, compactMnLegacyReg_rg] using hM.rx)
    (by simpa only [embStk_R, compactMnLegacyReg_rg] using hM.ry)
    (by simp only [hdbn, List.length_replicate, mn_pmVals_b])
    (by simp only [hdpn, List.length_replicate, mn_pmVals_p])
    hdwn
    (by simp only [hdsn, List.length_replicate, mn_pmVals_S])
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    hrwn hrmn hrnn hrsq
    (by simp only [hrbn, List.length_replicate, mn_pmVals_b])
    (by simp only [hrpn, List.length_replicate, mn_pmVals_p])
    hrwo
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
  obtain ⟨v', St', m, -, hm, e, hS', hfr⟩ := hrun v St ⟨hstable.1, fun j => by simpa only [compactSrcM_ι, embStk_R] using hstable.2.2.2.1 j⟩ hstable
    (fun r => by cases r <;> first | rfl | exact hsrc _)
  refine ⟨v', St', m, hm, e, hfr.1, hfr.2.1, hfr.2.2.1, ?_, fun r hr => ?_⟩
  · rw [show St'.R (compactMnRg (.out .dat)) = g' (.out .dat) from hS' (.out .dat), hdat]
  · rw [show St'.R (compactMnRg (.out r)) = g' (.out r) from hS' (.out r), hout r hr]


/-- The cost of a rounded forward transform at the retuned sizes. -/
def compactRetunedCFR (n : ℕ) : ℕ := compactSynRetunedFwdCostR n (compactBlCL n)

/-- The cost of a rounded opposite transform at the retuned sizes. -/
def compactRetunedCOR (n : ℕ) : ℕ := compactSynRetunedOppCostR n (compactBlCL' n)


theorem compactRetunedChainR_entry_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ (main : CompactMnPr CompactMainProc (prime+mnKa)) (x y : ℕ)
    (_hsx : Nat.size x ≤ n) (_hsy : Nat.size y ≤ n)
    (v : HS compactMnT compactMnQ (prime+mnKa) Unit) (St : Stacks compactMnT (prime+mnKa)),
    compactMainStablePre n St →
    MnDistOut (embStk compactMnLegacyReg St).R n (dsW n) (compactRetunedDist.E n)
      (mnσ (blP₀ dsW n) (compactDsyV₀ n)) →
    MnMid (embStk compactMnLegacyReg St) x y n →
    ∃ (v' : HS compactMnT compactMnQ (prime+mnKa) Unit)
      (St' : Stacks compactMnT (prime+mnKa)) (m : ℕ),
      m ≤ mnChainCost n (dsW n)
        (compactMainRuns compactRetunedDist compactRetunedCFR compactRetunedCOR n) + 12 ∧
      Exec (compactMainEntryTableR main) compactMainChainR (mk v St) m (mk v' St') ∧
      St'.inp=St.inp ∧ St'.out=St.out ∧ St'.L=St.L ∧
      (∃ cb : BoxConvOf n, BoxConvSpec n cb ∧ St'.R (compactMnRg (.out .dat))=mnWordsG mnKa n cb x y) ∧
      ∀ r,r≠.dat → St'.R (compactMnRg (.out r))=St.R (compactMnRg (.out r)) := by
  filter_upwards [compactMainChainR_exec_eventually, compactSynRetunedGeometry_eventually, eventually_big, eventually_small,
    eventually_margins, compactRetunedDist.base, compactRetunedDist.crt,
    compactRetunedDist.ln, compactRetunedDist.str, compactRetunedDist.sb,
    compactRetunedDist.widths] with n hchain hg hbig hsmall hmarg hbase hcrt hln hstr hsb hwid
  intro main x y hsx hsy v St hstable hout hmid
  obtain ⟨hEs,-⟩ := hmarg
  obtain ⟨hw,hwW,hWA,hWB,hWs,hWk⟩ := hwid
  have h := hchain main mnKa_alpha hbig hg hsmall hEs hw hwW hWA hWB.2 hWs hWk
    (compactRetunedDist.E n) (hbase (srcHd0 hbig)) hcrt hln hstr hsb x y hsx hsy v St hstable
    (fun r => by simpa only [embStk_R, compactMnLegacyReg_rg] using hout.src r) hmid
    (by simpa only [embStk_R, mnIo, compactMnLegacyReg_rg] using hout.dwn)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rwn)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rmn)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rnn)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rsq)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rwo)
  obtain ⟨v',St',m,hm,he,h1,h2,h3,h4,h5⟩ := h
  refine ⟨v',St',m,?_,he,h1,h2,h3,⟨_,convBoxQ_spec hbig hsmall hEs (by norm_num) (by norm_num) _,h4⟩,h5⟩
  simpa only [compactMain_runs_eq compactRetunedDist compactRetunedCFR compactRetunedCOR
    (srcHd0 hbig), compactRetunedCFR, compactRetunedCOR] using hm


def compactMainCoeffsG (n : ℕ) (cb : BoxConvOf n) (x y : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (∏ i,s n i) => rndCoeff (b n) (∏ i,s n i) (p n)
    (numer (p n) (oppMapG n cb (mnYG n cb x y) ((i : ℕ) : ZMod (∏ i,s n i)))).re

lemma compactMainCoeffsG_words (n : ℕ) (cb : BoxConvOf n) (x y : ℕ) :
    mnWordsG mnKa n cb x y=(compactMainCoeffsG n cb x y).flatMap (binSyms (mnWo n)) := rfl

lemma compactMainCoeffsG_length (n : ℕ) (cb : BoxConvOf n) (x y : ℕ) :
    (compactMainCoeffsG n cb x y).length=S n := by
  rw [compactMainCoeffsG,List.length_ofFn]
  rfl

theorem compactMainCoeffsG_eventually : ∀ᶠ n : ℕ in atTop,
    1≤b n ∧ 1≤mnWo n ∧ ∀ cb : BoxConvOf n,BoxConvSpec n cb → ∀ x y : ℕ,Nat.size x≤n → Nat.size y≤n →
      (∀ z ∈ compactMainCoeffsG n cb x y,z<2^mnWo n) ∧
      evalBase (2^b n) (compactMainCoeffsG n cb x y)=x*y := by
  filter_upwards [eventually_big,eventually_small,eventually_margins,pipeline_correctG]
    with n hbig hsmall hmarg hpipe
  obtain ⟨hEs,-⟩ := hmarg
  have hb1 := one_le_b hbig.1
  refine ⟨hb1,by unfold mnWo; omega,?_⟩
  intro cb hcb x y hsx hsy
  have hY1 : ‖mnYG n cb x y‖≤1/2 := mn_rdV_norm _
    (mn_srcMapG_norm hbig hsmall hEs cb hcb (mn_scaledDigits_norm hb1 _))
    (mn_srcMapG_norm hbig hsmall hEs cb hcb (mn_scaledDigits_norm hb1 _))
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.1 hz
    exact mn_rndCoeff_lt ((norm_le_pi_norm _ _).trans (mn_oppMapG_norm hbig hsmall hEs cb hcb hY1))
  · rw [compactMainCoeffsG,← mn_pipelineCoeffsG_eq (srcHd0 hbig) cb x y]
    exact hpipe cb hcb x y hsx hsy

/-- The chain's output and preserved distribution fields suffice for the final carry stage. -/
theorem compactMainOutputG_exec_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ (body : CompactMainProc → CompactMnPr CompactMainProc (prime+mnKa)) (x y : ℕ),
    Nat.size x≤n → Nat.size y≤n →
    ∀ (B : Stacks compactMnT (prime+mnKa)),
    MnDistOut (embStk compactMnLegacyReg B).R n (dsW n) (compactRetunedDist.E n)
      (mnσ (blP₀ dsW n) (compactDsyV₀ n)) →
    MnMid (embStk compactMnLegacyReg B) x y n →
    ∀ (v : HS compactMnT compactMnQ (prime+mnKa) Unit) (St : Stacks compactMnT (prime+mnKa)),
    ∀ cb : BoxConvOf n,BoxConvSpec n cb → St.R (compactMnRg (.out .dat))=mnWordsG mnKa n cb x y →
    (∀ r,r≠.dat → St.R (compactMnRg (.out r))=B.R (compactMnRg (.out r))) →
    ∃ (v' : HS compactMnT compactMnQ (prime+mnKa) Unit) (St' : Stacks compactMnT (prime+mnKa)),
      Exec body compactMainOutput (mk v St) (carryOutCost (mnWo n) (b n) (S n)) (mk v' St') ∧
      St'.inp=St.inp ∧ St'.out=encodingNatBool.encode (x*y)++St.out ∧ St'.L=St.L := by
  filter_upwards [compactMainCoeffsG_eventually] with n hcoeff
  intro body x y hsx hsy B hdo hmid v St cb hcb hdat hfr
  obtain ⟨hb,hW,hcs⟩ := hcoeff
  obtain ⟨hcsb,hev⟩ := hcs cb hcb x y hsx hsy
  have hobr : St.R (compactMainOutR .br)=List.replicate (b n) tick := by
    rw [compactMainOutR,hfr .br (by simp)]
    have h := hmid.obr
    simpa only [embStk_R,mnOutR,compactMnLegacyReg_rg,mn_pmVals_b] using h
  have hoe : ∀ r : OReg,r≠.dat → mnDistKeep (.out r) → MnR.out r∉mnUsRegs →
      St.R (compactMainOutR r)=[] := by
    intro r hr hk hu
    rw [compactMainOutR,hfr r hr]
    have h := hmid.rest (.out r) hk hu
    simpa only [embStk_R,compactMnLegacyReg_rg] using h
  have hwr : (St.R (compactMainOutR .wr)).length=mnWo n := by
    rw [compactMainOutR,hfr .wr (by simp)]
    simpa only [embStk_R,mnOutR,compactMnLegacyReg_rg] using hdo.owr
  obtain ⟨v',hu,he⟩ := carryOut_exec (body := body) (oreg := compactMainOutR)
    (fun _ _ h => MnR.out.inj (compactMnRg_injective h)) hb hW hcsb
    (lw := St.R (compactMainOutR .wr)) (lb := St.R (compactMainOutR .br))
    hwr (by rw [hobr,List.length_replicate]) v St
    (by rw [compactMainOutR,hdat,compactMainCoeffsG_words]) rfl rfl
    (hoe .ct (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (hoe .cr (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (hoe .sm (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (hoe .acc (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
  rw [compactMainCoeffsG_length] at he
  exact ⟨v',_,he,rfl,by rw [hev],rfl⟩

end
end IntegerMultBounds.MathlibTM2.Fast.Main
