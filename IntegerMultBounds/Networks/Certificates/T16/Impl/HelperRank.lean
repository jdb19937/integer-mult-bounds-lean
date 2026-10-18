module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheck
public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesCatalog

/-! The X-block ranks of the helper transitions. Every helper starts at the empty label or ends
at the full label, except two pairs whose inclusion is witnessed explicitly; nested labels
have relative rank equal to their difference in dimension. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open Geometry Tableau Pauli

theorem catalog_space_bot (a : ℕ) (ha : (catalog a).data.rank = 0) : (catalog a).space = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [catalog_dimension, ha]

theorem catalog_space_top (b : ℕ) (hb : (catalog b).data.rank = 9) : (catalog b).space = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [catalog_dimension, hb]
  simp

theorem edgeGood_of_le {a b : ℕ} (hle : (catalog a).space ≤ (catalog b).space)
    (hlt : (catalog a).data.rank < (catalog b).data.rank) :
    EdgeGood catalog a b ((catalog b).data.rank - (catalog a).data.rank) :=
  ⟨hle, by rw [catalog_dimension, catalog_dimension], by omega⟩

/-- The relative rank of nested native labels. -/
theorem edge_rank_of_le {a b : ℕ} (hle : (catalog a).space ≤ (catalog b).space)
    (hlt : (catalog a).data.rank < (catalog b).data.rank) :
    Module.finrank F (xRange (edgeRealization a b).binary) =
      (catalog b).data.rank - (catalog a).data.rank := by
  rw [edgeRealization_width]
  exact native_edge_rank (catalogExtension a) (catalogExtension b) (edgeGood_of_le hle hlt)

/-- The label pairs of the helpers. -/
def helperPairOK (a b : ℕ) : Bool :=
  ((catalog a).data.rank < (catalog b).data.rank) &&
    (((catalog a).data.rank == 0) || ((catalog b).data.rank == 9) ||
      (a == 2 && b == 999) || (a == 3 && b == 998))

def witness_2_999 : Fin frame2.rank → ℕ := ![112]

def witness_3_998 : Fin frame3.rank → ℕ := ![152]

theorem inclusion_2_999 : (catalog 2).space ≤ (catalog 999).space :=
  frame2.inclusion frame999 witness_2_999 (by decide)

theorem inclusion_3_998 : (catalog 3).space ≤ (catalog 998).space :=
  frame3.inclusion frame998 witness_3_998 (by decide)

/-- **Helper ranks.** -/
theorem helper_rank {a b : ℕ} (h : helperPairOK a b = true) :
    Module.finrank F (xRange (edgeRealization a b).binary) =
      (catalog b).data.rank - (catalog a).data.rank := by
  simp only [helperPairOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hlt, ((h0 | h9) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩⟩ := h
  · exact edge_rank_of_le (by rw [catalog_space_bot a h0]; exact bot_le) hlt
  · exact edge_rank_of_le (by rw [catalog_space_top b h9]; exact le_top) hlt
  · exact edge_rank_of_le inclusion_2_999 hlt
  · exact edge_rank_of_le inclusion_3_998 hlt

end IntegerMultBounds.Networks.Certificates.T16.Impl
