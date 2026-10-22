module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeFramesB
public import IntegerMultBounds.MathlibTM2.M8.Global.NodeScalarB

/-! Valid physical execution of the gauged design-B node, including side closure. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- The aligned body ends each wire at its last used frame. -/
theorem final_body : finalFrames (autoSteps gInit allGates) gInit =
    fun w => (fseq w allGates).getLast?.getD (gInit w) :=
  (valid_autoSteps allGates gInit tempZero gatesOk_node chainOk_node).2

theorem last_le {d : Nat} (fs : List (Mat d)) (A B : Mat d)
    (h : ∀ F ∈ fs, Le F B) (hA : Le A B) : Le (fs.getLast?.getD A) B := by
  cases he : fs.getLast? with
  | none => exact hA
  | some F => exact h F (List.mem_of_getLast? he)

/-- Both stages' actual terminal frames lie below their side-exit endpoints. -/
theorem body_side_le (b : Bool) (k : V) (s : Slot) :
    Le (finalFrames (autoSteps gInit allGates) gInit (wSide b k s))
      (sideTerminal (wSide b k s)) := by
  rw [final_body]
  dsimp only
  have hs : s.val < dagB.compile.next := by rw [compiler_slots_eq_plain]; exact s.2
  cases b
  · rw [fseq_side1]
    apply last_le
    · intro F hF
      obtain ⟨K, _, rfl⟩ := List.mem_map.mp hF
      exact le_lift1 (lineOf_idem k) (le_one K)
    · exact le_lift1 (lineOf_idem k) (le_one _)
  · rw [fseq_side2]
    apply last_le
    · intro F hF
      obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hF
      have he := (List.pairwise_append.mp ((finalStage_aux_chain s hs).imp le_of_nested)).2.2
      exact le_lift2 (lineOf_idem k) (he K hK _ (List.mem_singleton_self _))
    · exact le_lift2 (lineOf_idem k) (zero_le _)

/-- Every operation, including the terminal alignments and gauged exits, is valid. -/
theorem valid_node : Valid framedNode gInit tempZero := by
  rw [framedNode, valid_append]
  refine ⟨(valid_autoSteps allGates gInit tempZero gatesOk_node chainOk_node).1, ?_⟩
  apply closeGauges_valid sideTerminal gInit sideWires _ _ sideWires_nodup
  · intro w hw
    obtain ⟨b, k, s, rfl⟩ := mem_sideWires.mp hw
    cases b
    · exact lframe_lift1 k lframe_one
    · exact lframe_lift2 k (sigma_compl_lframe s)
  · intro w hw fr z hi
    obtain ⟨b, k, s, rfl⟩ := mem_sideWires.mp hw
    cases b
    · exact sideExit1_ok _ k s fr z hi
    · exact sideExit2_ok _ k s fr z hi
  · intro w hw
    obtain ⟨b, k, s, rfl⟩ := mem_sideWires.mp hw
    exact Or.inl (body_side_le b k s)

/-- Side frames close to complementary gauges; all other terminal frames are preserved. -/
theorem final_node : finalFrames framedNode gInit = fun w =>
    if w ∈ sideWires then 1 - gInit w else (fseq w allGates).getLast?.getD (gInit w) := by
  rw [framedNode, finalFrames_append, sideExits, finalFrames_closeGauges, final_body]
  funext w
  split_ifs <;> rfl

theorem final_wX (S T : V) : finalFrames framedNode gInit (wX S T) = 1 := by
  rw [final_node]
  dsimp only
  rw [ite_eq_right (fun h => by
    obtain ⟨b, k, s, h⟩ := mem_sideWires.mp h
    simp [wX, wSide] at h), fseq_wX]
  simp

theorem final_wY (S T : V) : finalFrames framedNode gInit (wY S T) = 1 - uFrame S T := by
  rw [final_node]
  dsimp only
  rw [ite_eq_right (fun h => by
    obtain ⟨b, k, s, h⟩ := mem_sideWires.mp h
    simp [wY, wSide] at h), fseq_wY]
  simp

theorem final_side (b : Bool) (k : V) (s : Slot) :
    finalFrames framedNode gInit (wSide b k s) = 1 - gInit (wSide b k s) := by
  rw [final_node]
  exact ite_eq_left (mem_sideWires.mpr ⟨b, k, s, rfl⟩)

/-- Side closure preserves the body's logical computation. -/
theorem logicRun_node {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (x : Wire → E) :
    logicRun framedNode x = FramedCircuit.moduleRun (allGates.map FGate.gate) x := by
  rw [framedNode, logicRun_append, sideExits, logicRun_closeGauges, logicRun_autoSteps]

/-- Arbitrary stored streams are routed and transposed by the actual design-B physical node. -/
theorem node_run {p : ℕ} (hp : p.Prime) (hpb : coefficientBound < p) (b : ℕ)
    (stored : Wire → Arrays 529 (p ^ b)) (hz : ∀ t, stored (.inr t) = 0) (i : World)
    (a : Address 529 (p ^ b)) :
    Step.run (edgeAction 529 (p ^ b)) (physOf framedNode) stored (.inl i) a =
      stored (.inl (route i)) (a.2, a.1) := by
  set ℓ0 : Wire → Arrays 529 (p ^ b) := fun w a => stored w (swapAt (p ^ b) (gInit w) a)
  have henc : Encoded (p ^ b) gInit stored ℓ0 := fun w a => by
    simp only [ℓ0]
    rw [swapAt_involutive hp hpb b (isFrame_gInit w)]
  have hzero : ∀ w, tempZero w → ℓ0 w = 0 := by
    rintro w ⟨t, rfl⟩
    funext a
    simp only [ℓ0, hz t, Pi.zero_apply]
  have hrun := run_phys hp hpb b (by norm_num) (by norm_num) framedNode gInit tempZero isFrame_gInit
    valid_node stored ℓ0 henc hzero
  have hlogic : logicRun framedNode ℓ0 = FramedCircuit.moduleRun (allGates.map FGate.gate) ℓ0 := by
    exact logicRun_node ℓ0
  have hpt : ∀ w (a' : Address 529 (p ^ b)), logicRun framedNode ℓ0 w a' =
      Circuit.run (allGates.map FGate.gate) (fun w' => ℓ0 w' a') w := fun w a' => by
    rw [hlogic, FramedCircuit.moduleRun_pointwise]
  have hz' : ∀ (a' : Address 529 (p ^ b)) (t : Temp), (fun w' => ℓ0 w' a') (.inr t) = 0 := by
    intro a' t
    simp only [ℓ0, hz t, Pi.zero_apply]
  rw [hrun (.inl i) a, hpt]
  rcases i with ⟨S, T⟩ | ⟨S, T⟩ | ⟨b', T, s⟩
  · rw [show (.inl (.inl (S, T)) : Wire) = wX S T from rfl, final_wX,
      (node_scalar _ (hz' _)).1 S T]
    simp only [ℓ0, wY, route]
    rw [show gInit (.inl (.inr (.inl (S, T)))) = 0 from rfl, swapAt_zero b, swapAt_one b]
  · rw [show (.inl (.inr (.inl (S, T))) : Wire) = wY S T from rfl, final_wY,
      (node_scalar _ (hz' _)).2.1 S T]
    simp only [ℓ0, wX, route]
    rw [show gInit (.inl (.inl (S, T))) = uFrame S T from rfl, swapAt_gauge hp hpb b,
      swapAt_one b]
  · rw [show (.inl (.inr (.inr (b', T, s))) : Wire) = wSide b' T s from rfl, final_side,
      (node_scalar _ (hz' _)).2.2 b' T s]
    simp only [ℓ0, wSide, route]
    rw [swapAt_complement hp hpb b (isFrame_gInit _), swapAt_one b]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
