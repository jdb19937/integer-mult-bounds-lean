module

import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedTopCost
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
import IntegerMultBounds.MathlibTM2.Fast.CompactPieceGeometry
public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedTopGrowth
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The top envelope specialized to the actual caller records and address split. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity
noncomputable section

theorem compactRetuned_caller_guard {M : ℕ} (hM : 2≤M) :
    CompactReservationGrowth.guard M=Mult.CompactSizes.guard M := by
  unfold CompactReservationGrowth.guard Mult.CompactSizes.guard
  rw [compactCaller_runtime_guardLog hM]

private theorem first_le_total (a b c d e : ℕ) (h : a+b+c+d=e) : a≤e := by omega

private theorem addressGeometry (N K D o qrow ρ : ℕ)
    (hq : qrow≤D) (hD : 0<D) (hρ : ρ<K) (haddr : o+K*D≤N) :
    let n := o+K*(D-qrow)
    let a := N-n
    n+a=N ∧ qrow*K≤a ∧ o≤n ∧ ρ+o≤N ∧ D*K≤N := by
  have he : K*(D-qrow)+qrow*K=K*D := by
    rw [Nat.mul_comm qrow K,←Nat.mul_add,Nat.sub_add_cancel hq]
  have hKD : K≤K*D := Nat.le_mul_of_pos_right _ hD
  have hDK : D*K=K*D := Nat.mul_comm _ _
  dsimp only
  omega

/-- The actual shared-shape caller pays every premise of the top bound from
its original address, reserved capacity and positive kernel count. -/
theorem compactRetuned_caller_top_cost (ds : ComplexFramedExecution.Directions)
    (M N D o W r ρ : ℕ) (hM : 2≤M)
    (hD : D≤Mult.Sizes.d M)
    (hfit : CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.CompactSizes.K M) D)
    (haddr : o+Mult.CompactSizes.K M*D≤N)
    (hr : 1≤r) (hW : 1≤W) (hNW : N≤r*W)
    (hρ : ρ<Mult.CompactSizes.K M)
    (hactive : compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.CompactSizes.K M) D≠0)
    (hq : 1≤compactTopKernelCount (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.CompactSizes.K M))
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<Parameters.lam) :
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let K := Mult.CompactSizes.K M
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let a := N-n
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let R₂ := compactTopRows d 1 a
    let shift := (D+1)/2+q+(backChunks d g K+
      synE (gateCount (program ds)) (factorCount (program ds))
        (compactReservationActive d g K D) (compactReservationActive d g K D))
    let w := W+shift+D
    let shape := compactReservationShape d g K D (2^o*(3*(r*w)))
    let pcs := compactTopPcs d g K D o R₂
    (compactTopCost W w shift n a 1 r K ρ q aT o D R₂ pcs
      (compactTopCallCost ds shape 1 (n+a) o r w ρ ⟨0,q,1,aT⟩)
      (compactTopCallCost ds shape 1 n o r w ρ):ℝ)≤
      compactRetunedTopCoeff 1 ds*((R₂*2^n*(r*w):ℕ):ℝ)*
        (Mult.Sizes.d M:ℝ)^CompactInterim.lam' := by
  let d := Mult.Sizes.d M
  let g := CompactReservationGrowth.guard M
  let K := Mult.CompactSizes.K M
  let qrow := CompactGlobalRowPadding.rowAxes NW m d
  let n := o+K*(D-qrow)
  let a := N-n
  let q := compactTopKernelCount d g K
  let aT := compactTopKernelOffset d g K D o
  let R₂ := compactTopRows d 1 a
  let shift := (D+1)/2+q+(backChunks d g K+
    synE (gateCount (program ds)) (factorCount (program ds))
      (compactReservationActive d g K D) (compactReservationActive d g K D))
  let w := W+shift+D
  let shape := compactReservationShape d g K D (2^o*(3*(r*w)))
  have hK : 0<K := Mult.CompactSizes.one_le_K hM
  have hqD : qrow≤D := by
    have hh := compactReservation_axes hfit
    exact first_le_total _ _ _ _ _ hh
  have hactiveD : compactReservationActive d g K D≤D :=
    ((Nat.sub_le _ _).trans (Nat.sub_le _ _)).trans (Nat.sub_le _ _)
  have hDpos : 0<D := (Nat.pos_of_ne_zero hactive).trans_le hactiveD
  obtain ⟨htotal,ha,hon,hρN,hDK⟩ := addressGeometry N K D o qrow ρ hqD hDpos hρ haddr
  have hworking : W≤w := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have hw : 1≤w := hW.trans hworking
  have hN : n+a≤r*w := htotal.le.trans (hNW.trans (Nat.mul_le_mul_left r hworking))
  have hbits : shape.bits≤n-o := by
    rw [compactReservation_bits hK hfit]
    exact (Nat.add_sub_cancel_left o (K*(D-qrow))).symm.le
  have hsw : shift+W≤w := by dsimp only [w]; omega
  have hker := (compactTopKernel_geometry (o := o) hfit hρ ha).2
  have hqa : o≤aT := Nat.le_add_right _ _
  have hcap : 2^a*1≤R₂ := by
    simpa only [Nat.mul_one,Nat.one_mul] using (compactTopRows_bounds hK (by decide : 0<1) ha).1
  have hpcs := compactTop_working_pcs_ok ds hK (by decide : 0<1) hfit hD ha (w := W) (oS := o)
  exact compactRetuned_top_cost ds M hM shape 1 d g K D o R₂ W w shift n a 1 r ρ o q aT
    rfl (compactRetuned_caller_guard hM) rfl hD hactive rfl rfl (by decide) hr hw hρ hon (le_refl _) hbits rfl hsw hN
    (hρN.trans htotal.ge) (hDK.trans htotal.ge) hker hqa hq rfl hcap hal hpcs
    (fun _ hp => compactTopPcs_offset hp)

end
end IntegerMultBounds.MathlibTM2.Cost
