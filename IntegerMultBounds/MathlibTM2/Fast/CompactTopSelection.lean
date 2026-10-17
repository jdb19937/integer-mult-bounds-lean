module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRows
import IntegerMultBounds.MathlibTM2.Fast.CompactSynCoverage
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
import IntegerMultBounds.MathlibTM2.Fast.CompactSynSel
public import IntegerMultBounds.MathlibTM2.Fast.SynSel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

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

noncomputable def compactTopPcs (d g K D oS R₂ : ℕ) : List TopPc :=
  (compactReservedPcs K 0 oS (backChunks d g K) (oS+K*backChunks d g K)
    (CompactGlobalRowPadding.depth m d) (compactReservationActive d g K D)).map (compactRebasePc R₂)

noncomputable def compactTopKernelCount (d g K : ℕ) :=
  CompactGlobalRowPadding.rowAxes NW m d+frontChunks d g K

noncomputable def compactTopKernelOffset (d g K D oS : ℕ) :=
  oS+K*(backChunks d g K+compactReservationActive d g K D)

private theorem rebaseMetadata_vals (ρ K : ℕ) (pcs : List TopPc) (base : TopPc → ℕ) :
    (pcs.map (fun pc => {pc with R₀:=base pc})).flatMap (synPcVals ρ K) =
      pcs.flatMap (synPcVals ρ K) := by
  simp only [List.flatMap_map]
  rfl

theorem compactRebasePc_vals (ρ K R : ℕ) (pcs : List TopPc) :
    (pcs.map (compactRebasePc R)).flatMap (synPcVals ρ K) =
      pcs.flatMap (synPcVals ρ K) :=
  rebaseMetadata_vals ρ K pcs (fun pc => R / NW^pc.j)

theorem compactTopKernel_end {d g K D : ℕ} (h : CompactReservationFits d g K D) (oS : ℕ) :
    compactTopKernelOffset d g K D oS+K*compactTopKernelCount d g K=oS+K*D := by
  have he := compactReservation_axes h
  have hsum : (backChunks d g K+compactReservationActive d g K D)+
      (CompactGlobalRowPadding.rowAxes NW m d+frontChunks d g K)=D := by omega
  unfold compactTopKernelOffset compactTopKernelCount
  rw [Nat.add_assoc,←Nat.mul_add,hsum]

theorem compactTopKernel_fits {d g K D oS ρ N : ℕ} (h : CompactReservationFits d g K D)
    (hρ : ρ<K) (hfit : oS+K*D≤N) :
    ∀ i<compactTopKernelCount d g K, compactTopKernelOffset d g K D oS+ρ+K*i<N :=
  topFit hρ (by rw [compactTopKernel_end h]; exact hfit)

/-- These are the actual `topSel` indices used by the top-level host contract. -/
theorem compactTopSelection_vals (ds : ComplexFramedExecution.Directions)
    {d g K D oS n a w R₂ ρ : ℕ} (h : CompactReservationFits d g K D) (hρ : ρ<K)
    (hpcs : ∀ pc∈compactTopPcs d g K D oS R₂,pc.Ok ds K n w R₂)
    (hfitT : ∀ i<compactTopKernelCount d g K, compactTopKernelOffset d g K D oS+ρ+K*i<n+a) :
    ((topSel a ((topPieces hρ (compactTopPcs d g K D oS R₂) hpcs).flatMap Piece.bitsList)
      (topTop (compactTopKernelOffset d g K D oS) ρ K (compactTopKernelCount d g K) (n+a) hfitT)).map Fin.val).Perm
      ((List.range D).map fun i => ρ+oS+K*i) := by
  rw [topSel,List.map_append,List.map_map]
  have hh : (Fin.val ∘ Fin.castAdd a) = (Fin.val : Fin n → ℕ) := rfl
  rw [hh,topPieces_vals,topTop,map_val_actMap]
  unfold compactTopPcs
  rw [compactRebasePc_vals]
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

/-- Exact coordinate coverage implies no repeated selected bit. -/
theorem compactSelection_nodup {N K D ρ oS : ℕ} {sel : List (Fin N)} (hK : 0<K)
    (h : (sel.map Fin.val).Perm ((List.range D).map fun i => ρ+oS+K*i)) : sel.Nodup := by
  have hn : ((List.range D).map fun i => ρ+oS+K*i).Nodup := by
    refine List.nodup_range.map fun i j hij => ?_
    exact Nat.eq_of_mul_eq_mul_left hK (Nat.add_left_cancel hij)
  exact List.Nodup.of_map _ (h.nodup_iff.2 hn)

/-- The actual padded pieces fit below the row prefix, including the low offset. -/
theorem compactTopPcs_ok (ds : ComplexFramedExecution.Directions)
    {d g K D oS R a w : ℕ} (hK : 0<K) (hR : 0<R)
    (h : CompactReservationFits d g K D) (hD : D≤d)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a)
    (hw : synE (gateCount (program ds)) (factorCount (program ds))
      (compactReservationActive d g K D) (compactReservationActive d g K D)+
        compactReservationActive d g K D≤w) :
    ∀ pc∈compactTopPcs d g K D oS (compactTopRows d R a),
      pc.Ok ds K (oS+K*(D-CompactGlobalRowPadding.rowAxes NW m d)) w (compactTopRows d R a) := by
  have he := compactReservation_axes h
  have hab : backChunks d g K+compactReservationActive d g K D ≤
      D-CompactGlobalRowPadding.rowAxes NW m d := by omega
  have hb : backChunks d g K≤D-CompactGlobalRowPadding.rowAxes NW m d := by omega
  have hactive : compactReservationActive d g K D≤d := by omega
  apply compactTopRows_pcs_ok ds hK hR ha hactive
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left K hb) oS
  · have hm := Nat.mul_le_mul_left K hab
    simpa only [Nat.mul_add,Nat.add_assoc] using Nat.add_le_add_left hm oS
  · exact hw

private theorem rebaseMetadata_exps (ds : ComplexFramedExecution.Directions)
    (pcs : List TopPc) (base : TopPc → ℕ) :
    (pcs.map (fun pc => {pc with R₀:=base pc})).map (fun pc => expZ pc.u ds pc.j) =
      pcs.map (fun pc => expZ pc.u ds pc.j) := by
  rw [List.map_map]
  rfl

/-- The actual rebased records retain exactly the exponent used in the runtime shift. -/
theorem compactTopPcs_exp (ds : ComplexFramedExecution.Directions) (d g K D oS R₂ : ℕ) :
    ((compactTopPcs d g K D oS R₂).map (fun pc => expZ pc.u ds pc.j)).sum =
      backChunks d g K+synE (gateCount (program ds)) (factorCount (program ds))
        (compactReservationActive d g K D) (compactReservationActive d g K D) := by
  unfold compactTopPcs
  have hh := rebaseMetadata_exps ds
    (compactReservedPcs K 0 oS (backChunks d g K) (oS+K*backChunks d g K)
      (CompactGlobalRowPadding.depth m d) (compactReservationActive d g K D))
    (fun pc => R₂ / NW^pc.j)
  exact (congrArg List.sum hh).trans (compactReservedPcs_exp_sum ds _ _ _ _ _ _ _)

end
end IntegerMultBounds.MathlibTM2.Fast
