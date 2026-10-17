module

import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapTransformFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineCompose
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapView
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! A fully charged transform boundary from real input sources and blank scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- The core transforms only the I/O stream; setup and exit are derived from real sources. -/
theorem compactMnTransformPipeline_from_sources (body : P → Pr P compactMnT Q A U)
    (core : Pr P compactMnT Q A U) (R : Fin compactMnT → List (Fin (A+4)))
    (p d : ℕ) (out : List (Fin (A+4))) (c : ℕ) (hp : 2≤p) (hd : 0<d)
    (hpSource : (R (compactMnRg (.io .dpn))).length=p)
    (hdSource : (R (compactMnSyn (.p .D))).length=d-1)
    (hs : ∀ i : Fin 32,R (compactMnSyn (.s i))=[])
    (hb : ∀ z : CompactBReg,R (compactMnLay (.bc (.inl z)))=[])
    (hcore : LayRuns body core (compactMnBootstrapFinal R p d)
      (Function.update (compactMnBootstrapFinal R p d) (compactMnRg (.src (.v .io))) out) c) :
    LayRuns body (compactMnTransformPipeline core) R
      (Function.update R (compactMnRg (.src (.v .io))) out)
      (compactMnOriginalBootstrapCost p d+(c+((2*d+2)+(2*(4*Nat.clog 2 p+6)+2)))) := by
  exact (compactMnOriginalBootstrap_from_sources body R p d hp hd hpSource hdSource hs hb).seq
    (hcore.seq (compactMnGlobalsExit_after_transform body R p d out hs hb))

end
end IntegerMultBounds.MathlibTM2.Fast.Main
