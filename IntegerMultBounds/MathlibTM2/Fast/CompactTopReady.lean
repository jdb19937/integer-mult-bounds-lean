module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Selection and precision obligations for the computed compact top configuration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open CompactGadgetReservationCapacity
noncomputable section

/-- Exact coordinate coverage supplies the mask predicate used by the top program. -/
theorem compactSelection_mem {N K D ρ oS : ℕ} {sel : List (Fin N)}
    (h : (sel.map Fin.val).Perm ((List.range D).map fun i => ρ+oS+K*i))
    (t : Fin N) : t ∈ sel ↔ ∃ i<D, t.val=ρ+oS+K*i := by
  constructor
  · intro ht
    have hh := h.mem_iff.1 (List.mem_map_of_mem (f := Fin.val) ht)
    obtain ⟨i,hi,he⟩ := List.mem_map.1 hh
    exact ⟨i,List.mem_range.1 hi,he.symm⟩
  · rintro ⟨i,hi,he⟩
    have hh : t.val ∈ sel.map Fin.val := h.mem_iff.2
      (List.mem_map.2 ⟨i,List.mem_range.2 hi,he.symm⟩)
    obtain ⟨t',ht',he'⟩ := List.mem_map.1 hh
    rwa [Fin.ext he'] at ht'

theorem compactSelection_length {N K D ρ oS : ℕ} {sel : List (Fin N)}
    (h : (sel.map Fin.val).Perm ((List.range D).map fun i => ρ+oS+K*i)) :
    sel.length=D := by simpa using h.length_eq

/-- The serialized shift is exactly the shift required by `topZ_correct`. -/
theorem compactTop_shift (ds : ComplexFramedExecution.Directions)
    {d g K D oS n a w R₂ ρ : ℕ} (h : CompactReservationFits d g K D) (hρ : ρ<K)
    (hpcs : ∀ pc∈compactTopPcs d g K D oS R₂,pc.Ok ds K n w R₂)
    (hfitT : ∀ i<compactTopKernelCount d g K,
      compactTopKernelOffset d g K D oS+ρ+K*i<n+a) :
    (D+1)/2+compactTopKernelCount d g K+
        (backChunks d g K+synE (gateCount (program ds)) (factorCount (program ds))
          (compactReservationActive d g K D) (compactReservationActive d g K D)) =
      (((topPieces hρ (compactTopPcs d g K D oS R₂) hpcs).flatMap Piece.bitsList).length+
        compactTopKernelCount d g K+1)/2+compactTopKernelCount d g K+
      ((topPieces hρ (compactTopPcs d g K D oS R₂) hpcs).map (Piece.exp ds)).sum := by
  have hlen := compactSelection_length (compactTopSelection_vals ds h hρ hpcs hfitT)
  simp only [topSel,List.length_append,List.length_map,topTop,List.length_finRange] at hlen
  rw [hlen,topPieces_exp,compactTopPcs_exp]

/-- The actual working width pays every piece's exponent and active bits. -/
theorem compactTop_working_pcs_ok (ds : ComplexFramedExecution.Directions)
    {d g K D oS R a w : ℕ} (hK : 0<K) (hR : 0<R)
    (h : CompactReservationFits d g K D) (hD : D≤d)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a) :
    ∀ pc∈compactTopPcs d g K D oS (compactTopRows d R a),
      pc.Ok ds K (oS+K*(D-CompactGlobalRowPadding.rowAxes NW m d))
        (w+((D+1)/2+compactTopKernelCount d g K+
          (backChunks d g K+synE (gateCount (program ds)) (factorCount (program ds))
            (compactReservationActive d g K D) (compactReservationActive d g K D)))+D)
        (compactTopRows d R a) := by
  apply compactTopPcs_ok ds hK hR h hD ha
  have := compactReservation_axes h
  omega

/-- Piece embeddings are injective for every positive physical chunk width. -/
theorem compactTopPieces_injective (ds : ComplexFramedExecution.Directions)
    {ρ K n w R₂ : ℕ} (hρ : ρ<K) (pcs : List TopPc)
    (hpcs : ∀ pc∈pcs, pc.Ok ds K n w R₂) :
    ∀ P∈topPieces hρ pcs hpcs, Function.Injective P.e := by
  induction pcs with
  | nil => simp [topPieces]
  | cons pc pcs ih =>
    intro P hP
    rw [topPieces,List.mem_cons] at hP
    rcases hP with rfl | hP
    · simp only [TopPc.piece]
      exact actMap_injective (by omega) _
    · exact ih _ P hP

/-- The reserved decomposition with its computed shift has the exact desired
transform semantics. Actual compact layer execution is a separate obligation. -/
theorem compactTopZ_correct (ds : ComplexFramedExecution.Directions)
    (hd : ComplexPhaseBudget.Realizes ds)
    {d g K D oS n a w R R₂ r ρ : ℕ} (h : CompactReservationFits d g K D) (hρ : ρ<K)
    (hR₂ : R*2^a≤R₂)
    (hpcs : ∀ pc∈compactTopPcs d g K D oS R₂,pc.Ok ds K n w R₂)
    (hfitT : ∀ i<compactTopKernelCount d g K,
      compactTopKernelOffset d g K D oS+ρ+K*i<n+a)
    (Z : ZArr (Fin R × Fin r) (n+a))
    (p : (Fin R × Fin r) × (Fin (n+a) → ZMod 2)) :
    let Ps := topPieces hρ (compactTopPcs d g K D oS R₂) hpcs
    let low := Ps.flatMap Piece.bitsList
    let top := topTop (compactTopKernelOffset d g K D oS) ρ K
      (compactTopKernelCount d g K) (n+a) hfitT
    let shift := (D+1)/2+compactTopKernelCount d g K+
      (backChunks d g K+synE (gateCount (program ds)) (factorCount (program ds))
        (compactReservationActive d g K D) (compactReservationActive d g K D))
    topZ ds a low top hR₂ Ps shift Z p =
      ⟨truncR (Hl _ (topSel a low top) (toC Z) p).re,
        truncR (Hl _ (topSel a low top) (toC Z) p).im⟩ := by
  dsimp only
  apply topZ_correct ds hd
  · exact compactTopPieces_injective ds hρ _ hpcs
  · exact List.Perm.refl _
  · exact compactSelection_nodup (by omega) (compactTopSelection_vals ds h hρ hpcs hfitT)
  · simpa [topTop] using compactTop_shift ds h hρ hpcs hfitT

end
end IntegerMultBounds.MathlibTM2.Fast
