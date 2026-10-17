module
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainConstants
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
open Filter
open Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- Place source-machine registers in a larger host without changing source semantics. -/
def srcMachPlace {t₀ T Q T' Q' : ℕ} (M : SrcMach t₀ T Q)
    (e : Fin T → Fin T') (he : Function.Injective e) (hT : T≤T') (hQ : Q≤Q') :
    SrcMach t₀ T' Q' where
  rg := e ∘ M.rg
  ι := e ∘ M.ι
  hrg := he.comp M.hrg
  hι := he.comp M.hι
  hdisj r j h := M.hdisj r j (he h)
  hT := M.hT.trans hT
  hT91 := M.hT91.trans hT
  hQ := M.hQ.trans hQ
  hQrp := M.hQrp.trans hQ
  hd := M.hd
  pay := M.pay
  hi := M.hi
  hdpay := M.hdpay
  hQs := M.hQs.trans hQ
  hTs := M.hTs.trans hT
  hQc := M.hQc.trans hQ
  hTc := M.hTc.trans hT

lemma compactMnT_legacy : mnT≤compactMnT := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    compactMnLegacyReg compactMnLegacyReg_injective

/-- The original source layout on the expanded host and its enlarged state bank. -/
def compactSrcM : SrcMach 6 compactMnT compactMnQ :=
  srcMachPlace mnM compactMnLegacyReg compactMnLegacyReg_injective compactMnT_legacy compactMnQ_legacy

@[simp] lemma compactSrcM_rg (r : SrcR 6) : compactSrcM.rg r=compactMnRg (.src r) :=
  compactMnLegacyReg_rg _

@[simp] lemma compactSrcM_ι (j : Fin 64) : compactSrcM.ι j=compactMnLegacyReg (mnι j) := rfl

end
end IntegerMultBounds.MathlibTM2.Fast.Main
