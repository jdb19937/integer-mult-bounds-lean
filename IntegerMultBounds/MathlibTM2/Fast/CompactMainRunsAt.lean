module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsCost

/-! Three actual expanded source runs with explicit retuned transform costs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter IntegerMultBounds.MathlibTM2.Cost


attribute [local irreducible] mnT mnQ compactMnT compactMnQ

noncomputable section

def compactMainRunsAt {K : ℕ} (n w W cF cO : ℕ) (hd0 : 0 < d n) (V₀ : RsaV (RsaX 6) (prime + K))
    (σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4))) (restA restB : List (Fin (prime + K + 4))) :
    ℕ :=
  srcDirectPCost compactSrcM n w W cF cO hd0 V₀ σ₀
      (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
      (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) +
    srcDirectPCost compactSrcM n w W cF cO hd0
      (preCfgA V₀ crtHd n w W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1))
      (bandCfgB σ₀ crtHd n w W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1))
      (preRecsA n W hd0 0 ++ restA) (preRecsB n W hd0 0 ++ restB) +
    oppDirectPCost compactSrcM n w W cF cO hd0
      (preCfgA (preCfgA V₀ crtHd n w W hd0
        (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1))
        crtHd n w W hd0 (preRecsA n W hd0 0 ++ restA) (d n - 1))
      (bandCfgB (bandCfgB σ₀ crtHd n w W hd0
        (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1))
        crtHd n w W hd0 (preRecsB n W hd0 0 ++ restB) (d n - 1))
      restA restB

lemma compactMain_runs_eq {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ)
    (cF cO : ℕ → ℕ) {n : ℕ} (hd0 : 0 < d n) :
    compactMainRuns D cF cO n = compactMainRunsAt n (w n) (D.Wt n) (cF n) (cO n) hd0 (D.V₀ n) (D.σ₀ n) (D.restA n)
      (D.restB n) := by
  unfold compactMainRuns
  rw [dite_eq_left hd0]
  rfl

end
end IntegerMultBounds.MathlibTM2.Fast.Main
