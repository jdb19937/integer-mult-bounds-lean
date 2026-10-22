module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeB
public import IntegerMultBounds.MathlibTM2.M8.Global.NodeScalar

/-! Scalar semantics of the actual gauged design-B node. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem firstStage_on : OnWires InR (gatesOf firstStage) := by
  intro g hg
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
  exact (stage_gate_good assignment v hv).1

theorem finalStage_on : OnWires InR (gatesOf finalStage) := by
  intro g hg
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
  exact (secondStage_gate_good assignment v hv).1

theorem firstStage_shear : LocalShear (gatesOf firstStage) := fun d hz =>
  ⟨fun _ ht => firstStage_target d hz ht, firstStage_other d hz⟩

theorem finalStage_shear : LocalShear (gatesOf finalStage) := fun d hz =>
  ⟨fun _ ht => finalStage_target d hz ht, finalStage_other d hz⟩

theorem allGates_program : (allGates.map FGate.gate) = nodeProgram (gatesOf firstStage) (gatesOf finalStage) := by
  have h1 : (allV.flatMap gates1).map FGate.gate =
      allV.flatMap fun T => (gatesOf firstStage).map (gateMap (place1 T)) := by
    rw [List.map_flatMap]
    apply congrArg allV.flatMap
    funext T
    exact gates_place (place1 T) (lift1 (lineOf T)) firstStage
  have h2 : (allV.flatMap gates2).map FGate.gate =
      allV.flatMap fun S => (gatesOf finalStage).map (gateMap (place2 S)) := by
    rw [List.map_flatMap]
    apply congrArg allV.flatMap
    funext S
    exact gates_place (place2 S) (lift2 (lineOf S)) finalStage
  rw [allGates_def, List.map_append, List.map_append, h1, h2, List.map_flatMap]
  rfl

/-- The actual global word swaps data pairs and restores every side role on zero temporaries. -/
theorem node_scalar (c : Wire → ZMod 2) (hz : ∀ t : Temp, c (.inr t) = 0) :
    (∀ S T, Circuit.run ((allGates.map FGate.gate)) c (wX S T) = c (wY S T)) ∧
    (∀ S T, Circuit.run ((allGates.map FGate.gate)) c (wY S T) = c (wX S T)) ∧
    (∀ b k s, Circuit.run ((allGates.map FGate.gate)) c (wSide b k s) = c (wSide b k s)) := by
  rw [allGates_program]
  exact nodeProgram_scalar _ _ firstStage_on finalStage_on firstStage_shear finalStage_shear c hz

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
