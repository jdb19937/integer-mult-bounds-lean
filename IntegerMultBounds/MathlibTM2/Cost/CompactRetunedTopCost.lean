module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedTopGrowth
import IntegerMultBounds.MathlibTM2.Cost.CompactTopCompleteBound
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The complete actual compact top cost at the proposed stronger layer exponent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity
noncomputable section

/-- The actual recursive top program, kernels and controls obey the stronger
layer exponent. Premises describe the concrete encoded address geometry. -/
theorem compactRetuned_top_cost (ds : ComplexFramedExecution.Directions)
    (M : ℕ) (hM : 2≤M) (shape : CompactGadgetReservationShape.Shape)
    (packD d g K D oS R₂ W w shift n a R r ρ o q aT : ℕ)
    (hdActual : d=Mult.Sizes.d M) (hgActual : g=Mult.CompactSizes.guard M)
    (hKActual : K=Mult.CompactSizes.K M)
    (hD : D≤d)
    (hactive : compactReservationActive d g
      K D≠0)
    (hK : K=shape.chunk)
    (hguard : shape.guard=g)
    (hR : 1≤R) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<shape.chunk)
    (hn : o≤n) (hoS : o≤oS) (hbits : shape.bits≤n-o)
    (hpayload : shape.payload=2^o*(3*(r*w)))
    (hsw : shift+W≤w) (hN : n+a≤r*w) (hρo : ρ+oS≤n+a)
    (hDK : D*K≤n+a)
    (hker : aT+K*q≤n+a) (hqa : o≤aT) (hq : 1≤q)
    (hqactual : q=CompactGlobalRowPadding.rowAxes NW m d+
      frontChunks d g K)
    (hcap : 2^a*R≤R₂)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<CompactInterim.lam)
    (hpcs : ∀ pc∈compactTopPcs d g
      K D oS R₂,pc.Ok ds K n w R₂)
    (hbase : ∀ pc∈compactTopPcs d g
      K D oS R₂,o≤pc.a₀) :
    (compactTopCost W w shift n a R r K ρ q aT oS D R₂
      (compactTopPcs d g K D oS R₂)
      (compactTopCallCost ds shape packD (n+a) o r w ρ ⟨0,q,R,aT⟩)
      (compactTopCallCost ds shape packD n o r w ρ):ℝ)≤
      compactRetunedTopCoeff packD ds*((R₂*2^n*(r*w):ℕ):ℝ)*
        (Mult.Sizes.d M:ℝ)^CompactInterim.lam' := by
  have hG : 1≤shape.guard := by
    rw [hguard,hgActual]
    change 1≤4*Nat.clog 2 (Mult.Sizes.p M)+6
    omega
  have hd : 1≤d := by rw [hdActual]; exact Mult.Sizes.one_le_d hM
  have hk : 1≤K := by rw [hKActual]; exact Mult.CompactSizes.one_le_K hM
  have h := compactTopCost_complete (lam:=CompactInterim.lam) ds shape packD d g K D oS R₂ W w shift n a R r ρ o q aT
    hd hD hactive hK hk hR hr hw hρ hG hn hoS hbits hpayload hsw hN hρo hDK hker hqa hq hcap
    (by norm_num [CompactInterim.lam]) (by norm_num [Parameters.tau,CompactInterim.lam]) hal hpcs hbase
  rw [hguard,hqactual] at h
  have hdenv : D≤Mult.Sizes.d M := by simpa only [hdActual] using hD
  have henv := compactRetuned_top_envelope packD ds M hM D hdenv
  unfold compactRetunedTopEnvelope at henv
  simp only [←hdActual,←hgActual,←hKActual] at henv
  have hg := mul_le_mul_of_nonneg_left henv
    (Nat.cast_nonneg (α:=ℝ) (R₂*2^n*(r*w)))
  rw [hqactual]
  apply h.trans
  calc
    _ ≤ ((R₂*2^n*(r*w):ℕ):ℝ)*(compactRetunedTopCoeff packD ds*(d:ℝ)^CompactInterim.lam') := hg
    _ = compactRetunedTopCoeff packD ds*((R₂*2^n*(r*w):ℕ):ℝ)*
        (Mult.Sizes.d M:ℝ)^CompactInterim.lam' := by
      rw [hdActual]
      exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

end
end IntegerMultBounds.MathlibTM2.Cost
