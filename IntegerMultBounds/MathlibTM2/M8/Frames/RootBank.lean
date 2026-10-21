module

public import IntegerMultBounds.MathlibTM2.M8.Frames.RootBankCheck
public import IntegerMultBounds.MathlibTM2.M8.Frames.RootFrame

/-! Soundness of the computed frame bank and its chain checks. All statements
are generic in the bank, so concrete frame data are never reduced here. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames.RootBank

open Matrix

noncomputable section

/-- The projector complement represented by an entry. -/
def Record.frame (entry : Record) : Matrix (Fin 23) (Fin 23) ℚ := rootFrame entry.basis

theorem Record.check_spec {entry : Record} (h : entry.check = true) :
    (∀ b ∈ entry.basis, RootCheck.validCode b = true) ∧
      IsUnit ((rootMat entry.basis)ᵀ * formG * rootMat entry.basis).det ∧
      ∀ g ∈ entry.generators, rvec g ∈ rspan entry.basis := by
  obtain ⟨hm, hg⟩ := Bool.and_eq_true_iff.mp h
  simp only [Record.matrixCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hm
  obtain ⟨⟨hb, hd⟩, hmul⟩ := hm
  have hvalid := all_valid hb
  refine ⟨hvalid, gram_unit hvalid hd hmul, ?_⟩
  intro g hgen
  simp only [Record.generatorCheck] at hg
  obtain ⟨hgv, hmem⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hg g hgen)
  rcases Bool.or_eq_true_iff.mp hmem with hcontains | hspan
  · exact Submodule.subset_span (List.mem_map_of_mem (List.contains_iff_mem.mp hcontains))
  · exact memOk_mem hd hvalid hgv hspan

theorem Record.idem (entry : Record) (h : entry.check = true) :
    entry.frame * entry.frame = entry.frame := by
  have hp := proj_idem (Record.check_spec h).2.1
  simp only [Record.frame, rootFrame, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, hp]
  abel

theorem Record.rank (entry : Record) (h : entry.check = true) :
    entry.frame.rank = 23 - entry.basis.length := by
  have hu := (Record.check_spec h).2.1
  have hp := proj_idem hu
  have hr := Exchange.rank_sub_add _ 1 hp (Matrix.one_mul 1) (Matrix.mul_one _) (Matrix.one_mul _)
  rw [rank_one, Fintype.card_fin, proj_rank hu, Fintype.card_fin] at hr
  rw [Record.frame, rootFrame]
  omega

theorem Record.bounded (entry : Record) (h : entry.check = true) :
    Height.Bounded entry.frame (2 * 10 ^ 200) := by
  have hu := (Record.check_spec h).2.1
  rw [← rootMatZ_cast] at hu
  rw [Record.frame, rootFrame, ← rootMatZ_cast]
  exact frame_compl_bounded8 (rootMatZ_le entry.basis) hu

theorem Record.nested {a b : Record} (ha : a.check = true)
    (hab : a.nestedCheck b = true) : Nested a.frame b.frame := by
  apply nested_one_sub
  apply proj_le_root (Record.check_spec ha).2.1
  intro j
  have hmem := List.all_eq_true.mp hab _ (List.get_mem b.basis j)
  exact (Record.check_spec ha).2.2 _ (List.contains_iff_mem.mp hmem)

theorem chainCheck_bounds (bank : ℕ → Record) (size : ℕ) :
    ∀ ids, chainCheck bank size ids = true → ∀ i ∈ ids, i < size
  | [], _, _, hi => by simp at hi
  | i :: ids, h, j, hj => by
    have hi : i < size := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp h).1
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · cases ids with
      | nil => simp at hj
      | cons k ids =>
        exact chainCheck_bounds bank size (k :: ids)
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2 j hj

/-- Every checked chain is an increasing chain of actual rational frames. -/
theorem chainCheck_pairwise (bank : ℕ → Record) (size : ℕ)
    (hbank : ∀ i < size, (bank i).check = true) :
    ∀ ids, chainCheck bank size ids = true →
      (ids.map fun i => (bank i).frame).Pairwise Nested
  | [], _ => List.Pairwise.nil
  | i :: [], _ => by simp
  | i :: j :: ids, h => by
    have hi : i < size := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp h).1
    have hedge := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
    have htail := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
    have hp := chainCheck_pairwise bank size hbank (j :: ids) htail
    have hij := Record.nested (hbank i hi) hedge
    apply List.pairwise_cons.mpr
    refine ⟨?_, hp⟩
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hij
    · exact hij.trans ((List.pairwise_cons.mp hp).1 F hF)

/-- Turn the shared bank and schedule checks into semantic chain facts. -/
theorem chainsCheck_pairwise (bank : ℕ → Record) (size : ℕ)
    (hbank : ∀ i < size, (bank i).check = true) (chains : List (List ℕ))
    (h : chainsCheck bank size chains = true) (ids : List ℕ) (hi : ids ∈ chains) :
    (ids.map fun i => (bank i).frame).Pairwise Nested :=
  chainCheck_pairwise bank size hbank ids (List.all_eq_true.mp h ids hi)

end

end IntegerMultBounds.MathlibTM2.M8.Frames.RootBank
