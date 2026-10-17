module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedGeometry

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRows
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynCoverage

/-! Exact selected coordinates for the reserved top-level configuration.
The actual padded-row metadata leaves both records and selected coordinates
unchanged. Back/active pieces plus the high kernel cover each original bit once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open CompactGadgetReservationCapacity
noncomputable section

noncomputable def compactStoppedTopPcs (d g K D oS R₂ : ℕ) : List TopPc :=
  (compactStoppedReservedPcs K 0 oS (backChunks d g K) (oS+K*backChunks d g K)
    (CompactGlobalRowPadding.depth m d) (compactReservationActive d g K D) D).map (compactRebasePc R₂)

theorem compactStoppedTopSelection_vals (ds : ComplexFramedExecution.Directions)
    {d g K D oS n a w R₂ ρ : ℕ} (h : CompactReservationFits d g K D) (hρ : ρ<K)
    (hpcs : ∀ pc∈compactStoppedTopPcs d g K D oS R₂,pc.Ok ds K n w R₂)
    (hfitT : ∀ i<compactTopKernelCount d g K, compactTopKernelOffset d g K D oS+ρ+K*i<n+a) :
    ((topSel a ((topPieces hρ (compactStoppedTopPcs d g K D oS R₂) hpcs).flatMap Piece.bitsList)
      (topTop (compactTopKernelOffset d g K D oS) ρ K (compactTopKernelCount d g K) (n+a) hfitT)).map Fin.val).Perm
      ((List.range D).map fun i => ρ+oS+K*i) := by
  rw [topSel,List.map_append,List.map_map]
  have hh : (Fin.val ∘ Fin.castAdd a) = (Fin.val : Fin n → ℕ) := rfl
  rw [hh,topPieces_vals,topTop,map_val_actMap]
  unfold compactStoppedTopPcs
  rw [compactStoppedReservedPcs_vals,compactRebasePc_vals]
  have he : (List.range (compactTopKernelCount d g K)).map
      (fun i => compactTopKernelOffset d g K D oS+ρ+K*i) =
      (List.range (compactTopKernelCount d g K)).map
      (fun i => ρ+oS+K*(backChunks d g K+compactReservationActive d g K D+i)) := by
    apply List.map_congr_left
    intro i _
    unfold compactTopKernelOffset
    ring
  rw [he]
  exact compactReservation_full_coverage h 0 oS (CompactGlobalRowPadding.depth m d) ρ

end
end IntegerMultBounds.MathlibTM2.Fast
