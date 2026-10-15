module

public import IntegerMultBounds.Networks.Certificates.T16.TableauSource
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Certificate
public import Mathlib.LinearAlgebra.Pi

/-! Explicit column-retention API for supplying the source's invertible basis
extension. No unverified matrix is inserted into the native catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

/-- An invertible address matrix whose initial columns retain the literal frame. -/
structure FrameExtension (f : Frame) where
  rank_le : f.rank ≤ 9
  matrix : Address ≃ₗ[F] Address
  columns : ∀ i : Fin f.rank,
    matrix (Pi.single (Fin.castLE rank_le i) 1) = f.vectors i

theorem cut_single (r : ℕ) (i : Fin 9) :
    cut r (Pi.single i 1) = if i.val < r then Pi.single i 1 else 0 := by
  ext j
  by_cases hji : j = i
  · subst j
    by_cases hi : i.val < r <;> simp [cut, hi]
  · by_cases hi : i.val < r <;> simp [cut, hi, hji]

theorem FrameExtension.space {f : Frame} (e : FrameExtension f) :
    frameSpace e.matrix f.rank = f.space := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    change e.matrix (cut f.rank a) ∈ f.space
    rw [← (Pi.basisFun F (Fin 9)).sum_repr a]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    rw [Pi.basisFun_apply, cut_single]
    split_ifs with hi
    · have hc := e.columns ⟨i.val,hi⟩
      have he : Fin.castLE e.rank_le ⟨i.val,hi⟩ = i := Fin.ext rfl
      rw [he] at hc
      rw [hc]
      exact Submodule.subset_span ⟨⟨i.val,hi⟩, rfl⟩
    · simp
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine ⟨Pi.single (Fin.castLE e.rank_le i) 1, ?_⟩
    change e.matrix (cut f.rank (Pi.single (Fin.castLE e.rank_le i) 1)) = _
    simpa [cut_single, i.isLt] using e.columns i

/-- For actual extension matrices, native edge widths are actual relative B-block ranks. -/
theorem native_edge_rank {old next rank : ℕ}
    (e : FrameExtension (catalog old).data) (f : FrameExtension (catalog next).data)
    (h : EdgeGood catalog old next rank) :
    Module.finrank F (LinearMap.range
      (bBlock (sourceCanonical e.matrix (catalog old).data.rank)
        (sourceCanonical f.matrix (catalog next).data.rank))) = rank := by
  have hs : frameSpace e.matrix (catalog old).data.rank ≤
      frameSpace f.matrix (catalog next).data.rank := by
    rw [e.space, f.space]
    exact h.1
  rw [sourceCanonical_relative_rank _ _ _ _ hs, e.space, f.space]
  exact h.2.1

theorem forward_climb_rank {phase register old next rank : ℕ}
    (e : FrameExtension (catalog old).data) (f : FrameExtension (catalog next).data)
    (h : Trace.Event.climb phase register old next rank ∈ Trace.forwardEvents) :
    Module.finrank F (LinearMap.range
      (bBlock (sourceCanonical e.matrix (catalog old).data.rank)
        (sourceCanonical f.matrix (catalog next).data.rank))) = rank :=
  native_edge_rank e f (forward_climb h)

theorem backward_climb_rank {phase register old next rank : ℕ}
    (e : FrameExtension (catalog old).data) (f : FrameExtension (catalog next).data)
    (h : Trace.Event.climb phase register old next rank ∈ Trace.backwardEvents) :
    Module.finrank F (LinearMap.range
      (bBlock (sourceCanonical e.matrix (catalog old).data.rank)
        (sourceCanonical f.matrix (catalog next).data.rank))) = rank :=
  native_edge_rank e f (backward_climb h)

theorem bBlock_rank_symm (A B : PhaseAddress ≃ₗ[F] PhaseAddress) :
    Module.finrank F (LinearMap.range (bBlock A B)) =
      Module.finrank F (LinearMap.range (bBlock B A)) := by
  rw [bBlock_rank, bBlock_rank, inf_comm]

theorem forward_center_rank {index old next rank : ℕ}
    (e : FrameExtension (catalog old).data) (f : FrameExtension (catalog next).data)
    (h : Trace.Event.center index old next rank ∈ Trace.forwardEvents) :
    Module.finrank F (LinearMap.range
      (bBlock (sourceCanonical e.matrix (catalog old).data.rank)
        (sourceCanonical f.matrix (catalog next).data.rank))) = rank := by
  rw [bBlock_rank_symm]
  exact native_edge_rank f e (forward_center h)

theorem backward_center_rank {index old next rank : ℕ}
    (e : FrameExtension (catalog old).data) (f : FrameExtension (catalog next).data)
    (h : Trace.Event.center index old next rank ∈ Trace.backwardEvents) :
    Module.finrank F (LinearMap.range
      (bBlock (sourceCanonical e.matrix (catalog old).data.rank)
        (sourceCanonical f.matrix (catalog next).data.rank))) = rank :=
  native_edge_rank e f (backward_center h)

end IntegerMultBounds.Networks.Certificates.T16.Tableau
