module

public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRetunedCapacity
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection

/-! Eventual strict capacity and division geometry for the actual full axis list. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open CompactGadgetReservationCapacity Filter
noncomputable section

private theorem slackGeometry (d K row front back : ℕ)
    (hd : 8≤d) (hK : 1≤K) (hs : 4*(row+front+back)≤d) :
    d-1-row-front-back≠0 ∧ ∀ o, row*K+3≤o+K*(d-1-row) := by
  have hrow : row+3≤d-1-row := by omega
  have hmul := Nat.mul_le_mul_left K hrow
  constructor
  · omega
  · intro o
    rw [Nat.mul_add] at hmul
    nlinarith

private theorem frontPositive (d g K f : ℕ) (hd : 1≤d) (hg : 1≤g)
    (hfront : 2*(d*g)≤f*K) : 1≤f := by nlinarith

/-- Every full-dimension actual retuned chunk has nonempty active axes, a
positive kernel count and the address room required by original-row division. -/
theorem compactRetuned_caller_eventually_slack : ∀ᶠ M : ℕ in atTop,
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let K := Mult.CompactSizes.K M
    let row := CompactGlobalRowPadding.rowAxes NW m d
    compactReservationActive d g K (d-1)≠0 ∧
      1≤compactTopKernelCount d g K ∧
      ∀ o,row*K+3≤o+K*(d-1-row) := by
  filter_upwards [eventually_ge_atTop 2,compactCaller_runtime_eventually_reservation 4,
    Mult.Sizes.tendsto_d.eventually (eventually_ge_atTop 8)] with M hM hres hd
  let d := Mult.Sizes.d M
  let g := CompactReservationGrowth.guard M
  let K := Mult.CompactSizes.K M
  let row := CompactGlobalRowPadding.rowAxes NW m d
  have hK := Mult.CompactSizes.one_le_K hM
  have hOldK : 0<Mult.Sizes.K M := Mult.Sizes.one_le_iroot Mult.Sizes.cExp_ne (Mult.Sizes.one_le_d hM)
  have hf := compactChunks_antitone (2*(d*g)) (Mult.Sizes.K M) K hOldK (Mult.CompactSizes.old_K_le_K M)
  have hb := compactChunks_antitone (d*g) (Mult.Sizes.K M) K hOldK (Mult.CompactSizes.old_K_le_K M)
  change frontChunks d g K≤frontChunks d g (Mult.Sizes.K M) at hf
  change backChunks d g K≤backChunks d g (Mult.Sizes.K M) at hb
  have hs : 4*(row+frontChunks d g K+backChunks d g K)≤d :=
    (Nat.mul_le_mul_left 4 (Nat.add_le_add (Nat.add_le_add_left hf row) hb)).trans hres
  obtain ⟨ha,hn⟩ := slackGeometry d K row (frontChunks d g K) (backChunks d g K) hd hK hs
  have hg : 1≤g := by dsimp only [g,CompactReservationGrowth.guard]; omega
  have hfront : 2*(d*g)≤frontChunks d g K*K := (Compact.Layout.ceiling_chunks _ K hK).1
  have hfp := frontPositive d g K (frontChunks d g K) (Mult.Sizes.one_le_d hM) hg hfront
  exact ⟨ha,hfp.trans (Nat.le_add_left _ _),hn⟩

end
end IntegerMultBounds.MathlibTM2.Cost
