module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeRunB
public import IntegerMultBounds.MathlibTM2.M8.Global.GaugedMoments

/-! Exact executed move moments of the gauged design-B node. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

variable {M : Type} [AddCommMonoid M]

/-- Complete body moves, plus the terminal alignment and whole exterior on side roles. -/
def wireMoment (φ : Nat → M) (w : Wire) : M :=
  chainMoment φ (gInit w :: fseq w allGates) +
    if w ∈ sideWires then
      stepMoment φ ((fseq w allGates).getLast?.getD (gInit w)) (sideTerminal w) +
        φ (1 - (sideTerminal w - gInit w)).rank else 0

/-- Every executed exchange is included in the wire ledger. -/
theorem edgeMoment_node (φ : Nat → M) : edgeMoment φ framedNode = ∑ w, wireMoment φ w := by
  rw [framedNode, sideExits]
  simpa only [wireMoment] using
    (moment_closeGauges φ allGates gInit sideTerminal gInit gatesOk_node chainOk_node
      sideWires sideWires_nodup)

/-- Both sides pay one exterior projector of rank `506 + rank σ`. -/
theorem exterior_rank (b : Bool) (k : V) (s : Slot) :
    (1 - (sideTerminal (wSide b k s) - gInit (wSide b k s))).rank =
      506 + (assignment.sigma s).rank := by
  cases b
  · exact gauged_exit1_rank (lineOf_idem k) (sigma_idem s) (rank_lineOf k)
  · exact gauged_exit2_rank (lineOf_idem k) (sigma_idem s) (rank_lineOf k)

theorem wireMoment_side (φ : Nat → M) (b : Bool) (k : V) (s : Slot) :
    wireMoment φ (wSide b k s) =
      chainMoment φ (gInit (wSide b k s) :: fseq (wSide b k s) allGates) +
      (stepMoment φ ((fseq (wSide b k s) allGates).getLast?.getD (gInit (wSide b k s)))
        (sideTerminal (wSide b k s)) + φ (506 + (assignment.sigma s).rank)) := by
  rw [wireMoment, ite_eq_left (mem_sideWires.mpr ⟨b, k, s, rfl⟩), exterior_rank]
/-- Side costs follow the complete padded chain, followed by the single exterior. -/
theorem wireMoment_side_path (φ : Nat → M) (b : Bool) (k : V) (s : Slot) :
    wireMoment φ (wSide b k s) =
      chainMoment φ (gInit (wSide b k s) :: fseq (wSide b k s) allGates ++
        [sideTerminal (wSide b k s)]) + φ (506 + (assignment.sigma s).rank) := by
  rw [wireMoment_side, chainMoment_append_last, add_assoc]


end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
