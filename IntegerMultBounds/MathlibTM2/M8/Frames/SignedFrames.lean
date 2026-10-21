module

public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedCheck
public import IntegerMultBounds.MathlibTM2.M8.Frames.RootBank

/-! Signed frame descriptions interpret both the plain and computed pieces of
a design-B wire chain using the same certified bank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames.Signed

open Matrix
noncomputable section

def Frame.eval (bank : Nat → RootBank.Record) : Frame → Matrix (Fin 23) (Fin 23) ℚ
  | .zero => 0
  | .one => 1
  | .positive i => proj formG (rootMat (bank i).basis)
  | .negative i => (bank i).frame

theorem Frame.idem (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) (frame : Frame)
    (h : frame.validCheck size = true) : frame.eval bank * frame.eval bank = frame.eval bank := by
  cases frame with
  | zero | one => simp [Frame.eval]
  | positive i => exact proj_idem (RootBank.Record.check_spec (hbank i (Nat.blt_eq.mp h))).2.1
  | negative i => exact RootBank.Record.idem (bank i) (hbank i (Nat.blt_eq.mp h))

theorem Frame.rank_eval (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) (frame : Frame)
    (h : frame.validCheck size = true) : (frame.eval bank).rank = frame.rankValue bank := by
  cases frame with
  | zero => simp [Frame.eval, Frame.rankValue]
  | one => simp [Frame.eval, Frame.rankValue, rank_one]
  | positive i =>
    simpa only [Frame.eval, Frame.rankValue, Fintype.card_fin] using
      proj_rank (RootBank.Record.check_spec (hbank i (Nat.blt_eq.mp h))).2.1
  | negative i => exact RootBank.Record.rank (bank i) (hbank i (Nat.blt_eq.mp h))

theorem generatorCheck_mem {a : RootBank.Record} (ha : a.check = true) {generators : List Nat}
    (h : a.generatorCheck generators = true) : ∀ g ∈ generators, rvec g ∈ rspan a.basis := by
  have hm := (Bool.and_eq_true_iff.mp ha).1
  simp only [RootBank.Record.matrixCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hm
  have hvalid := (RootBank.Record.check_spec ha).1
  simp only [RootBank.Record.generatorCheck] at h
  intro g hg
  obtain ⟨hgv, hmem⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h g hg)
  rcases Bool.or_eq_true_iff.mp hmem with hcontains | hresidual
  · exact Submodule.subset_span (List.mem_map_of_mem (List.contains_iff_mem.mp hcontains))
  · exact memOk_mem hm.1.2 hvalid hgv hresidual

theorem spanCheck_mem {a b : RootBank.Record} (ha : a.check = true)
    (h : spanCheck a b = true) : ∀ g ∈ b.basis, rvec g ∈ rspan a.basis := by
  rcases Bool.or_eq_true_iff.mp h with hfast | hresidual
  · intro g hg
    have hm := List.all_eq_true.mp hfast g hg
    exact (RootBank.Record.check_spec ha).2.2 g (List.contains_iff_mem.mp hm)
  · exact generatorCheck_mem ha hresidual

theorem orthogonalCheck_gram {a b : RootBank.Record} (ha : a.check = true) (hb : b.check = true)
    (h : orthogonalCheck a b = true) : (rootMat a.basis)ᵀ * formG * rootMat b.basis = 0 := by
  ext i j
  rw [gram_apply, Matrix.zero_apply]
  have hrow := List.all_eq_true.mp (List.all_eq_true.mp h _ (List.get_mem a.basis i)) _
    (List.get_mem b.basis j)
  have hz : RootCheck.g9 (a.basis.get i) (b.basis.get j) = 0 := by
    simpa only [beq_iff_eq] using hrow
  have hzq : (RootCheck.g9 (a.basis.get i) (b.basis.get j) : ℚ) = 0 := by exact_mod_cast hz
  rw [g9_eq ((RootBank.Record.check_spec ha).1 _ (List.get_mem a.basis i))
    ((RootBank.Record.check_spec hb).1 _ (List.get_mem b.basis j))] at hzq
  change gform (rvec (a.basis.get i)) (rvec (b.basis.get j)) = 0
  exact (mul_eq_zero.mp hzq).resolve_left (by norm_num)

/-- Orthogonal spans lie in each other's projector complements. -/
theorem positive_negative {a b : RootBank.Record} (ha : a.check = true) (hb : b.check = true)
    (h : orthogonalCheck a b = true) :
    Nested (proj formG (rootMat a.basis)) b.frame := by
  have hz := orthogonalCheck_gram ha hb h
  have hz' := cross_symm hz
  have product_zero {X : Matrix (Fin 23) (Fin a.basis.length) ℚ}
      {Y : Matrix (Fin 23) (Fin b.basis.length) ℚ}
      (hxy : Xᵀ * formG * Y = 0) : proj formG X * proj formG Y = 0 := by
    simp only [proj]
    rw [show X * (Xᵀ * formG * X)⁻¹ * Xᵀ * formG *
        (Y * (Yᵀ * formG * Y)⁻¹ * Yᵀ * formG) =
        X * (Xᵀ * formG * X)⁻¹ * (Xᵀ * formG * Y) *
          ((Yᵀ * formG * Y)⁻¹ * Yᵀ * formG) by simp only [Matrix.mul_assoc],
      hxy, Matrix.mul_zero, Matrix.zero_mul]
  have h1 := product_zero hz
  have h2 : proj formG (rootMat b.basis) * proj formG (rootMat a.basis) = 0 := by
    simp only [proj]
    rw [show rootMat b.basis * ((rootMat b.basis)ᵀ * formG * rootMat b.basis)⁻¹ *
        (rootMat b.basis)ᵀ * formG *
        (rootMat a.basis * ((rootMat a.basis)ᵀ * formG * rootMat a.basis)⁻¹ *
          (rootMat a.basis)ᵀ * formG) =
        rootMat b.basis * ((rootMat b.basis)ᵀ * formG * rootMat b.basis)⁻¹ *
          ((rootMat b.basis)ᵀ * formG * rootMat a.basis) *
          (((rootMat a.basis)ᵀ * formG * rootMat a.basis)⁻¹ * (rootMat a.basis)ᵀ * formG) by
        simp only [Matrix.mul_assoc], hz', Matrix.mul_zero, Matrix.zero_mul]
  exact nested_of_orth nested_one h2 h1

theorem Frame.nested (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) {a b : Frame}
    (ha : a.validCheck size = true) (hb : b.validCheck size = true)
    (h : a.nestedCheck bank b = true) : Nested (a.eval bank) (b.eval bank) := by
  cases a with
  | zero => exact ⟨by simp [Frame.eval], by simp [Frame.eval]⟩
  | one =>
    cases b with
    | one => exact nested_one
    | zero | positive | negative => simp [Frame.nestedCheck] at h
  | positive i =>
    cases b with
    | zero => simp [Frame.nestedCheck] at h
    | one => exact nested_one
    | positive j =>
      apply proj_le_root (RootBank.Record.check_spec (hbank j (Nat.blt_eq.mp hb))).2.1
      intro k
      exact spanCheck_mem (hbank j (Nat.blt_eq.mp hb)) h _ (List.get_mem (bank i).basis k)
    | negative j =>
      exact positive_negative (hbank i (Nat.blt_eq.mp ha)) (hbank j (Nat.blt_eq.mp hb)) h
  | negative i =>
    cases b with
    | zero | positive => simp [Frame.nestedCheck] at h
    | one => exact nested_one
    | negative j =>
      apply nested_one_sub
      apply proj_le_root (RootBank.Record.check_spec (hbank i (Nat.blt_eq.mp ha))).2.1
      intro k
      exact spanCheck_mem (hbank i (Nat.blt_eq.mp ha)) h _ (List.get_mem (bank j).basis k)

theorem chainCheck_valid (bank : Nat → RootBank.Record) (size : Nat) :
    ∀ frames, chainCheck bank size frames = true → ∀ frame ∈ frames, frame.validCheck size = true
  | [], _, _, hmem => by simp at hmem
  | frame :: frames, h, next, hmem => by
    obtain ⟨hv, ht⟩ := Bool.and_eq_true_iff.mp h
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hv
    · cases frames with
      | nil => simp at hmem
      | cons f frames =>
        exact chainCheck_valid bank size (f :: frames) (Bool.and_eq_true_iff.mp ht).2 next hmem

theorem chainCheck_pairwise (bank : Nat → RootBank.Record) (size : Nat)
    (hbank : ∀ i < size, (bank i).check = true) :
    ∀ frames, chainCheck bank size frames = true →
      (frames.map (Frame.eval bank)).Pairwise Nested
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | a :: b :: frames, h => by
    have ha := chainCheck_valid bank size (a :: b :: frames) h a (by simp)
    have hb := chainCheck_valid bank size (a :: b :: frames) h b (by simp)
    have hedge := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
    have htail := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
    have hab := Frame.nested bank size hbank ha hb hedge
    have hp := chainCheck_pairwise bank size hbank (b :: frames) htail
    apply List.pairwise_cons.mpr
    refine ⟨?_, hp⟩
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hab
    · exact hab.trans ((List.pairwise_cons.mp hp).1 F hF)

end
end IntegerMultBounds.MathlibTM2.M8.Frames.Signed
