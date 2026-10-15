module
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopAbsoluteBound
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopControlPower

/-! Complete actual top-transform cost, with back and kernel axes explicit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast
open CompactGadgetReservationCapacity
noncomputable section

/-- All top stages, actual recursive reserved calls, and the widened top kernel.
The packing degree is fixed separately from the number of transform axes. -/
theorem compactTopCost_complete (ds : ComplexFramedExecution.Directions)
    (shape : CompactGadgetReservationShape.Shape)
    (packD d g K D oS R₂ W w shift n a R r ρ o q aT : ℕ)
    {lam : ℝ} (hd : 1≤d) (hD : D≤d) (hactive : compactReservationActive d g K D≠0)
    (hK : K=shape.chunk) (hKpos : 1≤K)
    (hR : 1≤R) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<shape.chunk)
    (hG : 1≤shape.guard) (hn : o≤n) (hoS : o≤oS)
    (hbits : shape.bits≤n-o) (hpayload : shape.payload=2^o*(3*(r*w)))
    (hsw : shift+W≤w) (hN : n+a≤r*w) (hρo : ρ+oS≤n+a)
    (hDK : D*K≤n+a) (hker : aT+K*q≤n+a) (hqa : o≤aT) (hq : 1≤q)
    (hcap : 2^a*R≤R₂) (hl : 0<lam) (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hpcs : ∀ pc∈compactTopPcs d g K D oS R₂,pc.Ok ds K n w R₂)
    (hbase : ∀ pc∈compactTopPcs d g K D oS R₂,o≤pc.a₀) :
    (compactTopCost W w shift n a R r K ρ q aT oS D R₂
      (compactTopPcs d g K D oS R₂)
      (compactTopCallCost ds shape packD (n+a) o r w ρ ⟨0,q,R,aT⟩)
      (compactTopCallCost ds shape packD n o r w ρ):ℝ) ≤
    ((R₂*2^n*(r*w):ℕ):ℝ)*
      (16384*compactTopCountConst lam*(d:ℝ)^lam+
       512*(backChunks d g K:ℝ)+512*(q:ℝ)+
       compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) packD ds lam) m lam*
         (compactReservationActive d g K D:ℝ)^lam*(shape.guard:ℝ)^Parameters.tau) := by
  have hc := compactTopControlCost_power (ds:=ds) d g K D oS R₂ W w shift n a R r ρ q aT
    hd hD hl hR hr hw hKpos hsw hN hρo hDK hker hcap hpcs
  have hpcshape : ∀ pc∈compactTopPcs d g K D oS R₂,pc.Ok ds shape.chunk n w R₂ := by
    simpa only [hK] using hpcs
  have hs := compactTopCallCost_reserved_sum ds packD K 0
    (compactReservationActive d g K D) oS (oS+K*backChunks d g K) (backChunks d g K)
    (CompactGlobalRowPadding.depth m d) R₂ n o r w ρ shape hactive hK hr hw hρ hG hn
    (by omega) hbits hpayload (by omega) hl htl hal hpcshape hbase
  have hk := compactTopCallCost_kernel ds packD shape (n+a) o r w ρ q R aT
    hq hR hr hw hρ (by omega) hqa (by simpa only [hK] using hker) hN
  have hvol : R*2^(n+a)*(r*w)≤R₂*2^n*(r*w) := by
    calc
      R*2^(n+a)*(r*w) = (2^a*R)*(2^n*(r*w)) := by rw [pow_add]; ring
      _ ≤ R₂*(2^n*(r*w)) := Nat.mul_le_mul_right _ hcap
      _ = _ := by ring
  have hk' := hk.trans (Nat.mul_le_mul_left (512*q) hvol)
  have hkR : (compactTopCallCost ds shape packD (n+a) o r w ρ ⟨0,q,R,aT⟩:ℝ)≤
      512*(q:ℝ)*((R₂*2^n*(r*w):ℕ):ℝ) := by exact_mod_cast hk'
  have hv : R₂*(2^n*r*w)=R₂*2^n*(r*w) := by ring
  rw [hv] at hc
  change (((compactTopPcs d g K D oS R₂).map
    (compactTopCallCost ds shape packD n o r w ρ)).sum:ℝ)≤_ at hs
  rw [compactTopCost_split,Nat.cast_add,Nat.cast_add]
  nlinarith only [hc,hs,hkR]

end
end IntegerMultBounds.MathlibTM2.Cost
