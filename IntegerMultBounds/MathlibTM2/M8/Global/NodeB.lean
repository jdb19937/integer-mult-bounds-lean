module

public import IntegerMultBounds.MathlibTM2.M8.Global.StageValidityB
public import IntegerMultBounds.MathlibTM2.M8.Global.GaugedSinks

/-! The gauged design-B node on the existing global roles and temporaries. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

def gates1 (T : V) : List (FGate Wire 529) :=
  firstStage.map (placeG (place1 T) (lift1 (lineOf T)))

def gates2 (S : V) : List (FGate Wire 529) :=
  finalStage.map (placeG (place2 S) (lift2 (lineOf S)))

@[irreducible] def allGates : List (FGate Wire 529) :=
  allV.flatMap gates1 ++ allV.flatMap gates2 ++ allPairs.flatMap fun p => corrGates p.1 p.2

attribute [local semireducible] allGates in
theorem allGates_def : allGates =
    allV.flatMap gates1 ++ allV.flatMap gates2 ++ allPairs.flatMap fun p => corrGates p.1 p.2 := rfl

/-- Side roles start in their readout gauges; all other roles retain the original entrance. -/
def gInit : Wire → Mat 529
  | .inl (.inr (.inr (false, T, s))) => lift1 (lineOf T) (assignment.sigma s)
  | .inl (.inr (.inr (true, S, _))) => lift2 (lineOf S) 0
  | w => Global.gInit w

/-- Terminal frames include the final endpoint of the reflected side chain. -/
def sideTerminal : Wire → Mat 529
  | .inl (.inr (.inr (false, T, _))) => lift1 (lineOf T) 1
  | .inl (.inr (.inr (true, S, s))) => lift2 (lineOf S) (1 - assignment.sigma s)
  | _ => 1

/-- Align every side role to its endpoint, then perform its single whole-projector exit. -/
def sideExits (fr : Wire → Mat 529) : List (FStep Wire 529) :=
  closeGauges sideTerminal gInit fr sideWires

def framedNode : List (FStep Wire 529) :=
  autoSteps gInit allGates ++ sideExits (finalFrames (autoSteps gInit allGates) gInit)

/-- Both placed stages and the correction use valid frame matrices and distinct XOR wires. -/
theorem gatesOk_node : GatesOk allGates := by
  intro v hv
  rw [allGates_def, List.mem_append, List.mem_append, List.mem_flatMap,
    List.mem_flatMap, List.mem_flatMap] at hv
  rcases hv with (⟨T, _, hv⟩ | ⟨S, _, hv⟩) | ⟨⟨S, T⟩, _, hv⟩
  · rw [gates1] at hv
    exact gatesOk_place (place1_injOn T) (lift1 (lineOf T)) firstStage
      (fun u hu => (stage_gate_good assignment u hu).1)
      (fun u hu => (stage_gate_good assignment u hu).2)
      (fun u hu => lframe_lift1 T (firstStage_frames u hu).1) v hv
  · rw [gates2] at hv
    exact gatesOk_place (place2_injOn S) (lift2 (lineOf S)) finalStage
      (fun u hu => (secondStage_gate_good assignment u hu).1)
      (fun u hu => (secondStage_gate_good assignment u hu).2)
      (fun u hu => lframe_lift2 S (finalStage_frames u hu).1) v hv
  · simp only [corrGates, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨isFrame_one, _, _, by simp [wCorr, wX], rfl⟩
    · exact ⟨isFrame_corr S T, _, _, by simp [wCorr, wY], rfl⟩

theorem isFrame_gInit (w : Wire) : IsFrame (gInit w) := by
  rcases w with ((⟨S, T⟩ | ⟨S, T⟩ | ⟨b, k, s⟩) | (⟨b, k, c⟩ | ⟨S, T⟩ | ⟨⟩))
  · exact Global.isFrame_gInit (wX S T)
  · exact Global.isFrame_gInit (wY S T)
  · cases b
    · exact lframe_lift1 k (sigma_lframe s)
    · exact lframe_lift2 k lframe_zero
  · cases b
    · exact Global.isFrame_gInit (wCentre false k c)
    · exact Global.isFrame_gInit (wCentre true k c)
  · exact Global.isFrame_gInit (wCorr S T)
  · exact Global.isFrame_gInit wJunk

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
