module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainChain
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsAt

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


attribute [local irreducible] mnT mnQ

noncomputable section

open Filter

theorem compactMainChain_exec_eventually : ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (main : CompactMnPr CompactMainProc (prime+mnKa)) (_hA : 96 ≤ prime + mnKa) (hbig : Big n)
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
        (compactSynRetunedFwdCost n (compactBlCL n)) (compactSynRetunedOppCost n (compactBlCL' n))
        (srcHd0 hbig) V₀ σ₀ restA restB) + 12 ∧
      Exec (compactMainEntryTable main) compactMainChain (mk v St) m (mk v' St') ∧
      St'.inp = St.inp ∧ St'.out = St.out ∧ St'.L = St.L ∧
      St'.R (compactMnRg (.out .dat)) = mnWords mnKa n x y ∧
      ∀ r, r ≠ .dat → St'.R (compactMnRg (.out r)) = St.R (compactMnRg (.out r)) := by
  filter_upwards [compactMainChain_eventually] with n hchain
  intro main hA hbig hsmall hEs W hw hwW hWA hWB hWs hWk V₀ σ₀ restA restB axsA axsB E hE hC hln hstr hsb x y hsx hsy v St hstable hsrc hM hdwn hrwn hrmn hrnn hrsq hrwo
  have he : ∀ r : MnR, mnDistKeep r → r ∉ mnUsRegs → St.R (compactMnRg r) = [] := by
    intro r hr hu
    simpa only [embStk_R, compactMnLegacyReg_rg] using hM.rest r hr hu
  have hdbn := hM.dbn
  have hdpn := hM.dpn
  have hdsn := hM.dsn
  have hrbn := hM.rbn
  have hrpn := hM.rpn
  simp only [embStk_R, mnIo, mnRnd, compactMnLegacyReg_rg] at hdbn hdpn hdsn hrbn hrpn
  obtain ⟨F', g', hrun, hdat, hout⟩ := hchain main hA hbig hsmall hEs
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


end
end IntegerMultBounds.MathlibTM2.Fast.Main
