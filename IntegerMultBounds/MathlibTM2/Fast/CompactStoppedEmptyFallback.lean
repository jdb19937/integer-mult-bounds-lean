module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedSynLayerPrepare
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynDispatch

/-! Empty selected sets cannot enter the capacity-certified compact branch.
The existing dispatcher therefore uses its unchanged direct fallback. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open CompactGadgetReservationCapacity

theorem compactStopped_empty_no_chunk (d g K ℓ h : ℕ)
    (hd : 0<d) (hg : 0<g) (hK : 0<K)
    (hcap : synChunk ℓ K h → CompactReservationFits d g K 0) :
    ¬synChunk ℓ K h := by
  intro hc
  have hfit := hcap hc
  unfold CompactReservationFits at hfit
  have hb : backChunks d g K=0 := by omega
  have hbits := (capacities d g K hK).2
  change d*g≤backChunks d g K*K at hbits
  simp only [hb,zero_mul] at hbits
  exact (Nat.not_lt_of_ge hbits) (Nat.mul_pos hd hg)

theorem compactStopped_empty_dispatch_cost (d g K ℓ h chunkCost directCost : ℕ)
    (hd : 0<d) (hg : 0<g) (hK : 0<K)
    (hcap : synChunk ℓ K h → CompactReservationFits d g K 0) :
    Main.compactSynDispatchCost ℓ K h+(if synChunk ℓ K h then chunkCost else directCost) =
      Main.compactSynDispatchCost ℓ K h+directCost := by
  rw [if_neg (compactStopped_empty_no_chunk d g K ℓ h hd hg hK hcap)]

end IntegerMultBounds.MathlibTM2.Fast
