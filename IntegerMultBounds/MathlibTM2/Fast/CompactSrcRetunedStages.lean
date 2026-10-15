module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSrcBase
public import IntegerMultBounds.MathlibTM2.Fast.CompactSrcRetunedFrame

/-! Concrete forward and opposite transforms with original layout programs and complete frame restoration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
open IntegerMultBounds.MathlibTM2.Fast.Src
open IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Pipeline
open Filter
open Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem compactSrcRetunedFwd_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ (main : CompactMnPr CompactMainProc (prime+mnKa)) (hbig : Big n)
    (_hsmall : 2 * d n * p n ^ 2 ≤ Mult.Sizes.T n * logT n)
    (_hEs : 9 * (2 : ℝ) ^ Mult.Sizes.gamma n * Mult.Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {W : ℕ}
    (_hwW : (dsW n) < W)
    (_hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (_hWB : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (13 * p n + 8) < 2 ^ W)
    (_hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (_hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX 6) (prime + mnKa)} {σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + mnKa + 4))}
    {restA restB axsA axsB : List (Fin (prime + mnKa + 4))} (E : SrcF 6 (prime + mnKa))
    (_hE : SrcBase mnM E n (dsW n) W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (_hC : SrcCrtBase E.c E.cb n (dsW n)) (_hln : E.a .ln = [])
    (u : ZMod (∏ i, s n i) → ℂ) (_hu : ‖u‖ ≤ 1 / 2) (_huf : ∀ k, IsFixed (p n) (u k))
    (_hstr : E.c .str = cstream (prime + mnKa) (dsW n) (srcCoef (p n) (∏ i, s n i) u)),
    SrcRuns (compactMainEntryTable main) compactSrcM.rg compactSrcM.ι (compactSynPre (Ka := mnKa) n (slyPk (blW dsW n) (blE n)) (compactDsyV₀ n)) (srcDirectP compactSrcM (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer))) E.get
      { E with a := (rsaWith (preCfgA V₀ compactSrcM.hd n (dsW n) W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (preCfgB σ₀ compactSrcM.hd n (dsW n) W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               c := Function.update E.c .str [],
               x := (Function.update E.x .sb
                 (cstream (prime + mnKa) (dsW n) (srcPad (p n) (s n) (t n) (srcMap n u)) ++ E.x .sb)) }.get
      (srcDirectPCost compactSrcM n (dsW n) W (compactSynRetunedFwdCost n (compactBlCL n)) (compactSynRetunedOppCost n (compactBlCL' n)) (srcHd0 hbig) V₀ σ₀ restA restB) := by
  filter_upwards [compactSynRetunedFwd_entry_eventually,compactSynRetunedOpp_entry_eventually] with n hF hO
  intro main hbig hsmall hEs W hwW hWA hWB hWs hWk V₀ σ₀ restA restB axsA axsB E hE hC hln u hu huf hstr
  have hw : p n+Chirp.chirpGuard (d n)+3≤dsW n := by unfold dsW; omega
  exact srcDirectP_runs (body := compactMainEntryTable main)
    compactSrcM mnKa_alpha hbig hsmall hEs (by simpa only [compactSrcM_rg] using hF main)
    (by simpa only [compactSrcM_rg] using hO main)
    (fun _ h => h) (fun _ h => h) (fun m _ => synPi_lt _ m) (compactSynPre_source_framed_of n _ _)
    hw hwW hWA hWB hWs hWk E (compactSrcBase_of_legacy hE) hC hln u hu huf hstr

theorem compactSrcRetunedOpp_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ (main : CompactMnPr CompactMainProc (prime+mnKa)) (hbig : Big n)
    (_hsmall : 2 * d n * p n ^ 2 ≤ Mult.Sizes.T n * logT n)
    (_hEs : 9 * (2 : ℝ) ^ Mult.Sizes.gamma n * Mult.Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {W : ℕ}
    (_hwW : (dsW n) < W)
    (_hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (_hWB : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (13 * p n + 8) < 2 ^ W)
    (_hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (_hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX 6) (prime + mnKa)} {σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + mnKa + 4))}
    {restA restB axsA axsB : List (Fin (prime + mnKa + 4))} (E : SrcF 6 (prime + mnKa))
    (_hE : SrcBase mnM E n (dsW n) W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (_hC : SrcCrtBase E.c E.cb n (dsW n)) (_hln : E.a .ln = []) (_hstr : E.c .str = [])
    (y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (_hy : ‖y‖ ≤ 1 / 2)
    (_hyf : ∀ k, IsFixed (p n) (y k))
    (_hsb : E.x .sb = cstream (prime + mnKa) (dsW n) (srcPad (p n) (s n) (t n) y)),
    SrcRuns (compactMainEntryTable main) compactSrcM.rg compactSrcM.ι (compactSynPre (Ka := mnKa) n (slyPk (blW dsW n) (blE n)) (compactDsyV₀ n)) (oppDirectP compactSrcM (compactSynFwd (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactSynOpp (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer))) E.get
      { E with a := (rsaWith (preCfgA V₀ compactSrcM.hd n (dsW n) W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (preCfgB σ₀ compactSrcM.hd n (dsW n) W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               c := (Function.update E.c .str
                 (cstream (prime + mnKa) (dsW n) (srcCoef (p n) (∏ i, s n i) (oppMap n y)))),
               x := Function.update E.x .sb [] }.get
      (oppDirectPCost compactSrcM n (dsW n) W (compactSynRetunedFwdCost n (compactBlCL n)) (compactSynRetunedOppCost n (compactBlCL' n)) (srcHd0 hbig) V₀ σ₀ restA restB) := by
  filter_upwards [compactSynRetunedFwd_entry_eventually,compactSynRetunedOpp_entry_eventually] with n hF hO
  intro main hbig hsmall hEs W hwW hWA hWB hWs hWk V₀ σ₀ restA restB axsA axsB E hE hC hln hstr y hy hyf hsb
  have hw : p n+Chirp.chirpGuard (d n)+3≤dsW n := by unfold dsW; omega
  exact srcDirectOpp_runs (body := compactMainEntryTable main)
    compactSrcM mnKa_alpha hbig hsmall hEs (by simpa only [compactSrcM_rg] using hF main)
    (by simpa only [compactSrcM_rg] using hO main)
    (fun _ h => h) (fun _ h => h) (fun m _ => synPi_lt _ m) (compactSynPre_source_framed_of n _ _)
    hw hwW hWA hWB hWs hWk E (compactSrcBase_of_legacy hE) hC hln hstr y hy hyf hsb

end
end IntegerMultBounds.MathlibTM2.Fast.Main
