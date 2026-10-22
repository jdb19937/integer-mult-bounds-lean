module

public import IntegerMultBounds.MathlibTM2.M8.Global.ChainMoments
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.List.Sort

/-! Repeated and skipped frames do not increase the cost of a nested checked chain. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical

variable {d : Nat}

theorem stepMoment_nonneg (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r) (A B : Mat d) :
    0 ≤ stepMoment φ A B := by
  unfold stepMoment
  split_ifs
  · exact le_refl 0
  · exact hφ _

theorem chainMoment_nonneg (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r) :
    ∀ fs : List (Mat d), 0 ≤ chainMoment φ fs
  | [] => le_refl 0
  | [_] => le_refl 0
  | A :: B :: fs => add_nonneg (stepMoment_nonneg φ hφ A B) (chainMoment_nonneg φ hφ (B :: fs))

theorem chainMoment_tail_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r) (A : Mat d) (fs : List (Mat d)) :
    chainMoment φ fs ≤ chainMoment φ (A :: fs) := by
  cases fs with
  | nil => exact le_refl 0
  | cons B fs => exact le_add_of_nonneg_left (stepMoment_nonneg φ hφ A B)

/-- Inserting an intermediate first frame only splits a nested move. -/
theorem chainMoment_head_insert (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) (A B : Mat d) (fs : List (Mat d))
    (hp : (A :: B :: fs).Pairwise Le) (hi : ∀ F ∈ A :: B :: fs, F * F = F) :
    chainMoment φ (A :: fs) ≤ chainMoment φ (A :: B :: fs) := by
  cases fs with
  | nil => simpa only [chainMoment, add_zero] using stepMoment_nonneg φ hφ A B
  | cons C fs =>
    have hab := (List.pairwise_cons.mp hp).1 B (List.mem_cons_self)
    have hbc := (List.pairwise_cons.mp hp.of_cons).1 C (List.mem_cons_self)
    have h := stepMoment_split φ hsub (hi A (by simp)) (hi C (by simp)) (hi B (by simp)) hab hbc
    change stepMoment φ A C + chainMoment φ (C :: fs) ≤
      stepMoment φ A B + (stepMoment φ B C + chainMoment φ (C :: fs))
    linarith

/-- A subsequence with a fixed entrance costs no more than the full nested path. -/
theorem chainMoment_sublist_from (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) {xs ys : List (Mat d)} (h : xs.Sublist ys) :
    ∀ A, (A :: ys).Pairwise Le → (∀ F ∈ A :: ys, F * F = F) →
      chainMoment φ (A :: xs) ≤ chainMoment φ (A :: ys) := by
  induction h with
  | slnil => intro A _ _; exact le_refl 0
  | @cons xs ys B h ih =>
    intro A hp hi
    have hp' : (A :: ys).Pairwise Le := hp.sublist (List.Sublist.cons_cons A (List.sublist_cons_self B ys))
    have hi' : ∀ F ∈ A :: ys, F * F = F := fun F hF => hi F (by
      rcases List.mem_cons.mp hF with rfl | hF
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))
    exact (ih A hp' hi').trans (chainMoment_head_insert φ hφ hsub A B ys hp hi)
  | @cons_cons xs ys B h ih =>
    intro A hp hi
    have ht := ih B hp.of_cons (fun F hF => hi F (List.mem_cons_of_mem _ hF))
    simp only [chainMoment_cons_cons]
    linarith

/-- Deleting frames, including endpoints, cannot increase a nested chain's moment. -/
theorem chainMoment_sublist (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) {xs ys : List (Mat d)} (h : xs.Sublist ys)
    (hp : ys.Pairwise Le) (hi : ∀ F ∈ ys, F * F = F) :
    chainMoment φ xs ≤ chainMoment φ ys := by
  induction h with
  | slnil => exact le_refl 0
  | @cons xs ys B h ih =>
    exact (ih hp.of_cons (fun F hF => hi F (List.mem_cons_of_mem _ hF))).trans
      (chainMoment_tail_le φ hφ B ys)
  | @cons_cons xs ys B h ih =>
    exact chainMoment_sublist_from φ hφ hsub h B hp hi

/-- Refining a junction through its two bounding endpoints only splits nested moves. -/
theorem chainMoment_splice_le (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) (A B C E : Mat d) (xs ys : List (Mat d))
    (hx : ((A :: xs) ++ [B]).Pairwise Le) (hy : ((C :: ys) ++ [E]).Pairwise Le)
    (hbc : Le B C)
    (hix : ∀ F ∈ (A :: xs) ++ [B], F * F = F)
    (hiy : ∀ F ∈ (C :: ys) ++ [E], F * F = F) :
    chainMoment φ ((A :: xs) ++ ys ++ [E]) ≤
      chainMoment φ ((A :: xs) ++ [B]) + stepMoment φ B C +
        chainMoment φ ((C :: ys) ++ [E]) := by
  have hall : (((A :: xs) ++ [B]) ++ ((C :: ys) ++ [E])).Pairwise Le := by
    apply pw_app hx hy
    intro F hF K hK
    have hFB : Le F B := by
      rcases List.mem_append.mp hF with hF | hF
      · exact (List.pairwise_append.mp hx).2.2 F hF B (List.mem_singleton_self B)
      · rw [List.mem_singleton.mp hF]
        exact le_refl_of_idem (hix B (List.mem_append_right _ (List.mem_singleton_self B)))
    have hCK : Le C K := by
      change (C :: (ys ++ [E])).Pairwise Le at hy
      change K ∈ C :: (ys ++ [E]) at hK
      rcases List.mem_cons.mp hK with rfl | hK
      · exact le_refl_of_idem (hiy _ (List.mem_append_left _ (List.mem_cons_self)))
      · exact (List.pairwise_cons.mp hy).1 K hK
    exact le_trans' (le_trans' hFB hbc) hCK
  have hid : ∀ F ∈ ((A :: xs) ++ [B]) ++ ((C :: ys) ++ [E]), F * F = F := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact hix F hF
    · exact hiy F hF
  have hs : ((A :: xs) ++ (ys ++ [E])).Sublist
      (((A :: xs) ++ [B]) ++ ((C :: ys) ++ [E])) := by
    have h := (List.Sublist.refl (A :: xs)).append
      (List.Sublist.cons B (List.Sublist.cons C (List.Sublist.refl (ys ++ [E]))))
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h
  have h := chainMoment_sublist φ hφ hsub hs hall hid
  have hcost : chainMoment φ (((A :: xs) ++ [B]) ++ ((C :: ys) ++ [E])) =
      chainMoment φ ((A :: xs) ++ [B]) + stepMoment φ B C +
        chainMoment φ ((C :: ys) ++ [E]) := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
      chainMoment_append φ (A :: xs) B C (ys ++ [E])
  rw [hcost] at h
  simpa only [List.append_assoc] using h

/-- Removing adjacent repetitions changes no move cost. -/
theorem chainMoment_destutter {M : Type} [AddCommMonoid M] (φ : Nat → M) (fs : List (Mat d)) :
    chainMoment φ (fs.destutter (· ≠ ·)) = chainMoment φ fs := by
  have aux : ∀ (xs : List (Mat d)) (A : Mat d), ∃ ys,
      xs.destutter' (· ≠ ·) A = A :: ys ∧
      chainMoment φ (A :: ys) = chainMoment φ (A :: xs) := by
    intro xs
    induction xs with
    | nil => intro A; exact ⟨[], rfl, rfl⟩
    | cons B xs ih =>
      intro A
      by_cases he : A = B
      · subst B
        obtain ⟨ys, hy, hm⟩ := ih A
        refine ⟨ys, ?_, ?_⟩
        · simpa only [List.destutter'_cons, ne_eq, not_true_eq_false, ite_false] using hy
        · rw [chainMoment_cons_cons, stepMoment, ite_eq_left rfl, zero_add]
          exact hm
      · obtain ⟨ys, hy, hm⟩ := ih B
        refine ⟨B :: ys, ?_, ?_⟩
        · rw [List.destutter'_cons, ite_eq_left he, hy]
        · exact congrArg (stepMoment φ A B + ·) hm
  cases fs with
  | nil => rfl
  | cons A xs =>
    obtain ⟨ys, hy, hm⟩ := aux xs A
    rw [List.destutter_cons', hy]
    exact hm

/-- A constant path has no physical moves, regardless of its number of repetitions. -/
theorem chainMoment_of_constant {M : Type} [AddCommMonoid M] (φ : Nat → M) (A : Mat d) :
    ∀ fs : List (Mat d), (∀ F ∈ fs, F = A) → chainMoment φ fs = 0
  | [], _ => rfl
  | [_], _ => rfl
  | F :: G :: fs, h => by
    have he : F = G := (h F (by simp)).trans (h G (by simp)).symm
    rw [chainMoment_cons_cons, he, stepMoment, ite_eq_left rfl, zero_add]
    exact chainMoment_of_constant φ A (G :: fs) (fun K hK => h K (List.mem_cons_of_mem _ hK))

/-- Nested projectors of equal rank are the same frame. -/
theorem eq_of_le_rank_eq {A B : Mat d} (hA : A * A = A) (hB : B * B = B)
    (hab : Le A B) (hr : A.rank = B.rank) : A = B := by
  have hd := rank_sub_of_le hA hB hab
  rw [hr] at hd
  have hz : (B - A).rank = 0 := by omega
  exact (sub_eq_zero.mp (eq_zero_of_rank_eq_zero hz)).symm

/-- Padding a path with repetitions of its final endpoint adds no new frame values. -/
theorem padded_path_subset {α : Type} (A B : α) (xs extra : List α)
    (he : ∀ x ∈ extra, x = B) : ∀ x ∈ (A :: xs) ++ extra ++ [B], x ∈ (A :: xs) ++ [B] := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · rw [he x hx]
      exact List.mem_append_right _ (List.mem_singleton_self B)
  · exact List.mem_append_right _ hx

/-- Constant entrance and exit blocks introduce no values beyond the padded path. -/
theorem padded_path_both_subset {α : Type} (A B : α) (p xs q : List α)
    (hp : ∀ x ∈ p, x = A) (hq : ∀ x ∈ q, x = B) :
    ∀ x ∈ (A :: (p ++ xs ++ q)) ++ [B], x ∈ (A :: xs) ++ [B] := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_append_left _ (List.mem_cons_self)
    · rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · rw [hp x hx]
          exact List.mem_append_left _ (List.mem_cons_self)
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ hx)
      · rw [hq x hx]
        exact List.mem_append_right _ (List.mem_singleton_self B)
  · exact List.mem_append_right _ hx

/-- Coverage suffices: repetitions disappear and the remaining sorted path is a subsequence. -/
theorem chainMoment_le_of_subset (φ : Nat → ℝ) (hφ : ∀ r, 0 ≤ φ r)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) {xs ys : List (Mat d)}
    (hx : xs.Pairwise Le) (hy : ys.Pairwise Le) (hm : ∀ F ∈ xs, F ∈ ys)
    (hi : ∀ F ∈ ys, F * F = F) : chainMoment φ xs ≤ chainMoment φ ys := by
  let : Std.Antisymm (Le (d := d)) := ⟨fun _ _ h h' => le_antisymm' h h'⟩
  have he := hx.destutter_eq_dedup
  have hn := List.nodup_dedup xs
  have hs : xs.dedup.Sublist ys := List.sublist_of_subperm_of_pairwise
    (List.subperm_of_subset hn (fun F hF => hm F (List.mem_dedup.mp hF)))
    (hx.sublist (List.dedup_sublist xs)) hy
  rw [← chainMoment_destutter φ xs, he]
  exact chainMoment_sublist φ hφ hsub hs hy hi

end
end IntegerMultBounds.MathlibTM2.M8.Global
