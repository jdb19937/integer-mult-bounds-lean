module

public import IntegerMultBounds.MathlibTM2.M8.Rev.FramedRing
public import IntegerMultBounds.MathlibTM2.M8.Global.NodeRunB

/-! The gauged design-B node is the routed interchange under any frame interpretation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Rev
open IntegerMultBounds.MathlibTM2.M8.Frames
open Classical
variable {R : Type} [CommRing R]

theorem node_run_ring (I : Interp 529 R) (stored : Wire → Streams 529 R)
    (hz : ∀ t, stored (.inr t) = 0) (i : World) (a : Addr 529 R) :
    frun I framedNode stored (.inl i) a = stored (.inl (route i)) (a.2, a.1) := by
  set ℓ0 : Wire → Streams 529 R := fun w a => stored w (I.swap (gInit w) a)
  have henc : REncoded I gInit stored ℓ0 := fun w a => by
    simp only [ℓ0]
    rw [I.swap_involutive (isFrame_gInit w)]
  have hzero : ∀ w, tempZero w → ℓ0 w = 0 := by
    rintro w ⟨t, rfl⟩
    funext a
    simp only [ℓ0, hz t, Pi.zero_apply]
  have hrun := frun_encoded I framedNode gInit tempZero isFrame_gInit valid_node stored ℓ0 henc hzero
  have hlogic : logicRun framedNode ℓ0 = FramedCircuit.moduleRun (allGates.map FGate.gate) ℓ0 :=
    logicRun_node ℓ0
  have hpt : ∀ w (a' : Addr 529 R), logicRun framedNode ℓ0 w a' =
      Circuit.run (allGates.map FGate.gate) (fun w' => ℓ0 w' a') w := fun w a' => by
    rw [hlogic, FramedCircuit.moduleRun_pointwise]
  have hz' : ∀ (a' : Addr 529 R) (t : Temp), (fun w' => ℓ0 w' a') (.inr t) = 0 := by
    intro a' t
    simp only [ℓ0, hz t, Pi.zero_apply]
  rw [hrun (.inl i) a, hpt]
  rcases i with ⟨S, T⟩ | ⟨S, T⟩ | ⟨b', T, s⟩
  · rw [show (.inl (.inl (S, T)) : Wire) = wX S T from rfl, final_wX,
      (node_scalar _ (hz' _)).1 S T]
    simp only [ℓ0, wY, route]
    rw [show gInit (.inl (.inr (.inl (S, T)))) = 0 from rfl, I.swap_zero, I.swap_one]
  · rw [show (.inl (.inr (.inl (S, T))) : Wire) = wY S T from rfl, final_wY,
      (node_scalar _ (hz' _)).2.1 S T]
    simp only [ℓ0, wX, route]
    rw [show gInit (.inl (.inl (S, T))) = uFrame S T from rfl, Rev.swap_gauge, I.swap_one]
  · rw [show (.inl (.inr (.inr (b', T, s))) : Wire) = wSide b' T s from rfl, final_side,
      (node_scalar _ (hz' _)).2.2 b' T s]
    simp only [ℓ0, wSide, route]
    rw [I.swap_up (isFrame_gInit _) isFrame_one (Matrix.mul_one _), I.swap_one]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
