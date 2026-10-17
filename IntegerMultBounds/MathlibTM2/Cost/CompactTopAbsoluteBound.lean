module
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopActualBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Canonical compact call costs in the absolute coordinates serialized by the top runner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast
noncomputable section

/-- The global reservation sum in the actual caller's absolute coordinates.
The stream volume has exponent n, and the low offset is counted only once. -/
theorem compactTopCallCost_reserved_sum (ds : ComplexFramedExecution.Directions)
    (D K X active oS activeOffset B J R n o r w ρ : ℕ)
    (s : CompactGadgetReservationShape.Shape) {lam : ℝ}
    (hactive : active≠0) (hK : K=s.chunk)
    (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hG : 1≤s.guard)
    (hn : o≤n) (hoffset : o≤activeOffset)
    (hbits : s.bits≤n-o) (hpayload : s.payload=2^o*(3*(r*w))) (hN : n≤r*w)
    (hl : 0<lam) (htl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (hok : ∀ pc∈(compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R),
      pc.Ok ds s.chunk n w R)
    (hbase : ∀ pc∈(compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R),
      o≤pc.a₀) :
    ((((compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R)).map
      (compactTopCallCost ds s D n o r w ρ)).sum:ℝ) ≤
      ((R*2^n*(r*w):ℕ):ℝ)*
        (512*(B:ℝ)+compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) D ds lam) m lam*
          (active:ℝ)^lam*(s.guard:ℝ)^Parameters.tau) := by
  let pcs := (compactReservedPcs K X oS B activeOffset J active).map (compactRebasePc R)
  have hmap : pcs.map (compactRelativePc o) =
      (compactReservedPcs K X (oS-o) B (activeOffset-o) J active).map (compactRebasePc R) := by
    calc
      _ = ((compactReservedPcs K X oS B activeOffset J active).map (compactRelativePc o)).map
          (compactRebasePc R) := by
        simp only [pcs,List.map_map]
        apply List.map_congr_left
        intro pc _
        exact compactRelativePc_rebase o R pc
      _ = _ := congrArg (List.map (compactRebasePc R))
        (compactRelativePc_reserved o K X oS B activeOffset J active hoffset)
  have hrel : ∀ pc∈(compactReservedPcs K X (oS-o) B (activeOffset-o) J active).map (compactRebasePc R),
      pc.Ok ds s.chunk (n-o) w R := by
    intro pc hp
    rw [←hmap] at hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact compactRelativePc_ok ds (hbase q hq) (hok q hq)
  have hs := compactReservedCost_sum ds D K X active (oS-o) (activeOffset-o) B J R (n-o) o r w ρ s
    hactive hK hr hw hρ hG hbits hpayload (by simpa only [Nat.add_sub_of_le hn] using hN)
    hl htl hal hrel
  have heq : (pcs.map (compactTopCallCost ds s D n o r w ρ)).sum =
      ((pcs.map (compactRelativePc o)).map (compactPieceCost ds D s (n-o) o r w ρ)).sum := by
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro pc _
    cases pc
    rfl
  change ((pcs.map (compactTopCallCost ds s D n o r w ρ)).sum:ℝ)≤_
  rw [heq,hmap]
  have hfun : compactPieceCost ds D s (n-o) o r w ρ =
      compactPieceCostWith (nT CompactBReg) ds D s (n-o) o r w ρ := by
    funext pc
    rfl
  simpa only [Nat.add_sub_of_le hn,hfun] using hs

/-- The actual top-kernel call, charged separately by its q axes. -/
theorem compactTopCallCost_kernel (ds : ComplexFramedExecution.Directions) (D : ℕ)
    (s : CompactGadgetReservationShape.Shape) (n o r w ρ q R a : ℕ)
    (hq : 1≤q) (hR : 1≤R) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk)
    (hn : o≤n) (ha : o≤a) (hfit : a+s.chunk*q≤n) (hN : n≤r*w) :
    compactTopCallCost ds s D n o r w ρ ⟨0,q,R,a⟩ ≤512*q*(R*2^n*(r*w)) := by
  have hf : a-o+s.chunk*q≤n-o := by omega
  have hs := compactPieceCost_leaf ds D s (n-o) o r w ρ q R (a-o)
    hq hR hr hw hρ hf (by simpa only [Nat.add_sub_of_le hn] using hN)
  simpa only [Nat.add_sub_of_le hn,compactTopCallCost,compactPieceCostWith] using hs

end
end IntegerMultBounds.MathlibTM2.Cost
