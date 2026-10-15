module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedReservedPieces
public import IntegerMultBounds.Machine.CompactGadgetReservationCapacity

/-! The active digits satisfy the selected stopping budget; the separate back
leaf has the actual reservation size ceil(d*g/K). Its budget is an independent
condition, not a consequence of stopping the active digits. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node CompactGadgetReservationCapacity

/-- Exact ceiling bounds for the actual unchanged back-reservation leaf. -/
theorem compactStoppedBack_reservation (d g K : ℕ) (hK : 0<K) :
    d*g ≤ backChunks d g K*K ∧ backChunks d g K*K < d*g+K := by
  exact Compact.Layout.ceiling_chunks (d*g) K hK

/-- Above the cutoff threshold, a uniform selected-beta leaf claim for the
whole list is equivalent to the remaining back-leaf budget. -/
theorem compactStoppedReservedPcs_leaf_bound_iff (K a oS B activeOffset J D globalD : ℕ)
    (hglobalD : 0<globalD) (hlarge : selectedStopDen ≤ Nat.log m globalD) :
    (∀ pc ∈ compactStoppedReservedPcs K a oS B activeOffset J D globalD,
      pc.u^selectedStopDen ≤ globalD) ↔ (B ≠ 0 → B^selectedStopDen ≤ globalD) := by
  constructor
  · intro h hB
    exact h ⟨0,B,rowsAt (2^a) J,oS⟩ (by simp [compactStoppedReservedPcs,hB])
  · intro h pc hp
    unfold compactStoppedReservedPcs at hp
    rcases List.mem_append.mp hp with hb | ha
    · by_cases hB : B=0
      · simp [hB] at hb
      · simp only [ite_eq_right hB, List.mem_singleton] at hb
        subst pc
        exact h hB
    · exact compactStoppedGlobalPipeline_leaf_bound K a activeOffset J D globalD D
        hglobalD hlarge pc ha

end IntegerMultBounds.MathlibTM2.Fast
