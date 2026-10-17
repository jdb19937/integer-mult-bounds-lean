module
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapView
import IntegerMultBounds.MathlibTM2.Fast.CompactSynScanFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundFrame
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd


/-! Forward layout followed by the concrete hybrid scan, with original transform semantics. -/
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
variable {Ka : ℕ}

/-- Entry uses original source lengths and a blank private bank. -/
def compactSynPre (M : ℕ) (Pk : List (Fin (prime+Ka+4)) → Prop)
    (v : SynW → List (Fin (prime+Ka+4))) (S : Stacks compactMnT (prime+Ka)) : Prop :=
  (∀ i,S.L i=[]) ∧
  (S.R (compactMnRg (.io .dpn))).length=Mult.Sizes.p M ∧
  (S.R (compactMnSyn (.p .D))).length=Mult.Sizes.d M-1 ∧
  (∀ z : CompactBReg,S.R (compactMnLay (.bc (.inl z)))=[]) ∧
  ∃ park,Pk park ∧ compactSynView S.R=
    synG (synIdle (S.R (compactMnRg (.src (.v .io)))) park) v

/-- Scratch blankness is a consequence of the synthetic invariant. -/
lemma compactSynView_scratch {M ℓ W l : ℕ} {es : List ℕ}
    {v : SynW → List (Fin (prime+Ka+4))}
    (hv : SynV v es ℓ (Mult.Sizes.K M) W l 0 (layPerm es ℓ (Mult.Sizes.K M)))
    {R : Fin compactMnT → List (Fin (prime+Ka+4))} {io park : List (Fin (prime+Ka+4))}
    (hR : compactSynView R=synG (synIdle io park) v) :
    ∀ i : Fin 32,R (compactMnSyn (.s i))=[] := by
  intro i
  rw [compactMnSyn_dispatch,compactSynView_wire hR]
  exact hv.hs i

end
end IntegerMultBounds.MathlibTM2.Fast.Main
