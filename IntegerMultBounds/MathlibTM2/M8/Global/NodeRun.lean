module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeFrames

/-!
# The PR97 node runs as the routed transpose

The framed node is valid from its starting frames (`valid_node`); every data wire `X S T` ends in
frame `1`, every `Y S T` in frame `1 − P_S ⊗ Q_T` and every side slot in frame `1`
(`final_wX`, `final_wY`, `final_side`). By the framed run (`run_phys`) and the node on scalars
(`node_scalar`), on arbitrary stored streams with zero temporaries, every contract role ends
with the stream of its route, its two address fields exchanged (`node_run`): `X S T` and
`Y S T` exchange their streams, and side slots keep theirs. For `Y S T` the gauge closes:
`D_{P ⊗ Q} D_{1 − P ⊗ Q} = D_1`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open IntegerMultBounds.Swap.Modular (reduce)
open Classical

/-- The temporaries start at zero. -/
def tempZero (k : Wire) : Prop := ∃ t : Temp, k = .inr t

theorem sideWires_nodup : sideWires.Nodup := by
  rw [sideWires_def]
  refine List.nodup_flatMap.mpr ⟨fun b _ => List.nodup_flatMap.mpr ⟨fun k _ =>
    (List.nodup_finRange _).map fun s s' h => by simpa [wSide] using h,
      allV_nodup.imp fun {k k'} hk => List.disjoint_left.mpr fun x hx hx' => ?_⟩, ?_⟩
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨s', -, h⟩ := List.mem_map.mp hx'
    simp only [wSide, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
    exact hk h.2.1.symm
  · refine List.pairwise_pair.mpr (List.disjoint_left.mpr fun x hx hx' => ?_)
    obtain ⟨k, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k', -, hx'⟩ := List.mem_flatMap.mp hx'
    obtain ⟨s', -, h⟩ := List.mem_map.mp hx'
    simp [wSide] at h

theorem mem_sideWires {k : Wire} : k ∈ sideWires ↔ ∃ b T s, k = wSide b T s := by
  simp only [sideWires_def, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map]
  constructor
  · rintro ⟨b, -, T, -, s, -, rfl⟩; exact ⟨b, T, s, rfl⟩
  · rintro ⟨b, T, s, rfl⟩
    exact ⟨b, by cases b <;> simp, T, mem_allV T, s, List.mem_finRange s, rfl⟩

/-- **The framed node is valid.** -/
theorem valid_node : Valid framedNode gInit tempZero := by
  obtain ⟨h1, h2⟩ := valid_autoSteps allGates gInit tempZero gatesOk_node chainOk_node
  rw [framedNode, valid_append, sinks]
  refine ⟨h1, ?_⟩
  exact (alignMoves_valid 1 isFrame_one sideWires _ _ sideWires_nodup fun w _ =>
    Or.inl (le_one _)).1

theorem final_node : finalFrames framedNode gInit =
    setF (fun w => (fseq w allGates).getLast?.getD (gInit w)) sideWires 1 := by
  obtain ⟨-, h2⟩ := valid_autoSteps allGates gInit tempZero gatesOk_node chainOk_node
  rw [framedNode, finalFrames_append, sinks, h2]
  exact (alignMoves_valid 1 isFrame_one sideWires _ tempZero sideWires_nodup fun w _ =>
    Or.inl (le_one _)).2.1

theorem final_wX (S T : V) : finalFrames framedNode gInit (wX S T) = 1 := by
  rw [final_node, setF, ite_eq_right (fun h => by
    obtain ⟨b, T', s, h⟩ := mem_sideWires.mp h; simp [wX, wSide] at h), fseq_wX]
  simp

theorem final_wY (S T : V) : finalFrames framedNode gInit (wY S T) = 1 - uFrame S T := by
  rw [final_node, setF, ite_eq_right (fun h => by
    obtain ⟨b, T', s, h⟩ := mem_sideWires.mp h; simp [wY, wSide] at h), fseq_wY]
  simp

theorem final_side (b : Bool) (T : V) (s : Slot) :
    finalFrames framedNode gInit (wSide b T s) = 1 := by
  rw [final_node, setF, ite_eq_left (mem_sideWires.mpr ⟨b, T, s, rfl⟩)]

/-! ### The partial swaps at the ends -/

section Swaps
variable {p : ℕ} (hp : p.Prime) (hpb : coefficientBound < p) (b : ℕ)
include hp hpb

omit hp hpb in
theorem swapAt_zero (a : Address 529 (p ^ b)) : swapAt (p ^ b) 0 a = a := by
  rw [swapAt, show reduce (p ^ b) (0 : Mat 529) = 0 by ext i j; simp [reduce, Swap.Modular.ratMod_zero]]
  exact exchange_zero a

omit hp hpb in
theorem swapAt_one (a : Address 529 (p ^ b)) : swapAt (p ^ b) 1 a = (a.2, a.1) := by
  rw [swapAt, Swap.Modular.reduce_one]
  simp [Exchange.exchange]

theorem swapAt_gauge (S T : V) (a : Address 529 (p ^ b)) :
    swapAt (p ^ b) (uFrame S T) (swapAt (p ^ b) (1 - uFrame S T) a) = swapAt (p ^ b) 1 a := by
  have hU : IsFrame (uFrame S T) := lframe_lift1 T (lframe_lineOf S)
  have ha := frame_admissible hp hpb b hU
  have h1 := frame_admissible hp hpb b (isFrame_one (d := 529))
  have hid := reduce_idem hp hpb b hU
  simp only [swapAt]
  rw [exchange_exchange, reduce_sub _ h1 ha, Swap.Modular.reduce_one, Matrix.mul_sub,
    Matrix.mul_one, hid, sub_self, smul_zero, sub_zero, add_sub_cancel]

end Swaps

/-! ### The routed transpose -/

/-- The route: `X S T` and `Y S T` exchange, side slots stay. -/
def route : World → World
  | .inl (S, T) => .inr (.inl (S, T))
  | .inr (.inl (S, T)) => .inl (S, T)
  | .inr (.inr x) => .inr (.inr x)

theorem route_involutive : Function.Involutive route := by
  rintro ((⟨S, T⟩) | (⟨S, T⟩ | x)) <;> rfl

/-- **The node theorem.** On arbitrary stored streams of the contract roles and zero
temporaries, every contract role ends with the stream of its route, address fields exchanged. -/
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
    rw [framedNode, logicRun_append, sinks, logicRun_alignMoves, logicRun_autoSteps]
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
    rw [show gInit (.inl (.inr (.inr (b', T, s)))) = 0 from rfl, swapAt_zero b,
      swapAt_one b]

end

end IntegerMultBounds.MathlibTM2.M8.Global
