module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopReady
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcR

/-! Selection and shift obligations of the rounded compact top: the pieces as rounded pieces
(`TopPc.OkR`), and the sum of their scales `Piece.expR`, which is the runtime exponent sum
`synE` with no factor term. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open CompactGadgetReservationCapacity
noncomputable section

/-- A piece of the exact top is a rounded piece. -/
lemma _root_.IntegerMultBounds.MathlibTM2.LayerMachine.TopPc.Ok.okR {ds : ComplexFramedExecution.Directions} {K n w R₂ : ℕ} {pc : TopPc}
    (h : pc.Ok ds K n w R₂) : pc.OkR K n R₂ := ⟨h.hu, h.hR₀, h.hR, h.hfit⟩

/-- The rounded pieces of exact pieces are the same pieces. -/
lemma topPiecesR_eq {ds : ComplexFramedExecution.Directions} {ρ K n w R₂ : ℕ} (hρ : ρ < K) :
    ∀ (pcs : List TopPc) (h : ∀ pc ∈ pcs, pc.Ok ds K n w R₂),
      topPiecesR hρ pcs (fun pc hpc => (h pc hpc).okR) = topPieces hρ pcs h
  | [], _ => rfl
  | pc :: pcs, h => by
      rw [topPiecesR, topPieces, topPiecesR_eq hρ pcs]
      rfl

theorem synPcs_expR_sum (ds : ComplexFramedExecution.Directions) (K a D oS J : ℕ) : ∀ t,
    ((synPcs K a D oS J t).map fun pc => scaleR pc.u ds pc.j).sum =
      synE (gateCount (program ds)) 0 D t
  | 0 => by simp [synPcs, synE]
  | t + 1 => by
      rw [synPcs_succ, synE_succ, List.map_append, List.sum_append, synPcs_expR_sum ds K a D oS J t]
      by_cases h0 : synDg D t = 0
      · simp [h0]
      · simp [h0, synPc, scaleR_eq_expSeq, Nat.add_comm]

theorem compactReservedPcs_expR_sum (ds : ComplexFramedExecution.Directions)
    (K a oS B activeOffset J D : ℕ) :
    ((compactReservedPcs K a oS B activeOffset J D).map fun pc => scaleR pc.u ds pc.j).sum =
      B + synE (gateCount (program ds)) 0 D D := by
  unfold compactReservedPcs
  rw [List.map_append, List.sum_append, synPcs_expR_sum]
  by_cases hB : B=0 <;> simp [hB, scaleR]

private theorem rebase_scaleR (ds : ComplexFramedExecution.Directions)
    (pcs : List TopPc) (base : TopPc → ℕ) :
    (pcs.map (fun pc => {pc with R₀:=base pc})).map (fun pc => scaleR pc.u ds pc.j) =
      pcs.map (fun pc => scaleR pc.u ds pc.j) := by
  rw [List.map_map]
  rfl

theorem compactTopPcs_expR (ds : ComplexFramedExecution.Directions) (d g K D oS R₂ : ℕ) :
    ((compactTopPcs d g K D oS R₂).map (fun pc => scaleR pc.u ds pc.j)).sum =
      backChunks d g K+synE (gateCount (program ds)) 0
        (compactReservationActive d g K D) (compactReservationActive d g K D) := by
  unfold compactTopPcs
  have hh := rebase_scaleR ds
    (compactReservedPcs K 0 oS (backChunks d g K) (oS+K*backChunks d g K)
      (CompactGlobalRowPadding.depth m d) (compactReservationActive d g K D))
    (fun pc => R₂ / NW^pc.j)
  exact (congrArg List.sum hh).trans (compactReservedPcs_expR_sum ds _ _ _ _ _ _ _)

theorem topPiecesR_expR {ds : ComplexFramedExecution.Directions} {ρ K n R₂ : ℕ} (hρ : ρ < K) :
    ∀ (pcs : List TopPc) (h : ∀ pc ∈ pcs, pc.OkR K n R₂),
      (topPiecesR hρ pcs h).map (Piece.expR ds) = pcs.map fun pc => scaleR pc.u ds pc.j
  | [], _ => rfl
  | pc :: pcs, h => by
      rw [topPiecesR, List.map_cons, List.map_cons, topPiecesR_expR hρ pcs]
      rfl

/-- The rounded shift without the guard is the shift required by `topRS`. -/
theorem compactTop_shiftR (ds : ComplexFramedExecution.Directions)
    {d g K D oS n a w R₂ ρ : ℕ} (h : CompactReservationFits d g K D) (hρ : ρ<K)
    (hpcs : ∀ pc∈compactTopPcs d g K D oS R₂,pc.Ok ds K n w R₂)
    (hfitT : ∀ i<compactTopKernelCount d g K,
      compactTopKernelOffset d g K D oS+ρ+K*i<n+a) :
    (D+1)/2+compactTopKernelCount d g K+
        (backChunks d g K+synE (gateCount (program ds)) 0
          (compactReservationActive d g K D) (compactReservationActive d g K D)) =
      (((topPieces hρ (compactTopPcs d g K D oS R₂) hpcs).flatMap Piece.bitsList).length+
        compactTopKernelCount d g K+1)/2+compactTopKernelCount d g K+
      ((topPiecesR hρ (compactTopPcs d g K D oS R₂) (fun pc hpc => (hpcs pc hpc).okR)).map
        (Piece.expR ds)).sum := by
  have hlen := compactSelection_length (compactTopSelection_vals ds h hρ hpcs hfitT)
  simp only [topSel,List.length_append,List.length_map,topTop,List.length_finRange] at hlen
  rw [hlen,topPiecesR_expR,compactTopPcs_expR]

end
end IntegerMultBounds.MathlibTM2.Fast
