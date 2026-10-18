module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.List.Count
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Rectangle plans for the disjoint-subset relation. A plan on a ground list
lists pairs of set families; every pair of an `a`-subset and a `b`-subset of the
ground set that are disjoint lies in exactly one listed rectangle, and every
rectangle's sources and targets have disjoint unions. The plan splits the
ground list in half and multiplies the plans of the two halves. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Rectangles

variable {α : Type*} [DecidableEq α]

/-- A rectangle: a family of sources and a family of targets. -/
abbrev Rect (α : Type*) := Finset (Finset α) × Finset (Finset α)

/-- Pairwise unions of two families. -/
def join (A B : Finset (Finset α)) : Finset (Finset α) :=
  (A ×ˢ B).image fun p => p.1 ∪ p.2

/-- The product rectangle on two disjoint ground sets. -/
def rectJoin (R₁ R₂ : Rect α) : Rect α := (join R₁.1 R₂.1, join R₁.2 R₂.2)

/-- The index pairs `(i, j)` with `i ≤ a` and `j ≤ b`. -/
def splits (a b : ℕ) : List (ℕ × ℕ) :=
  (List.range (a + 1)).flatMap fun i => (List.range (b + 1)).map fun j => (i, j)

/-- All products of a rectangle of one list with a rectangle of another. -/
def rectProducts (xs ys : List (Rect α)) : List (Rect α) :=
  xs.flatMap fun R₁ => ys.map (rectJoin R₁)

/-- The rectangle plan of the disjoint `a`/`b`-subset relation on `P`. -/
def plan (P : List α) (a b : ℕ) : List (Rect α) :=
  if _hab : P.length < a + b then []
  else if _ha : a = 0 then [({∅}, P.toFinset.powersetCard b)]
  else if _hb : b = 0 then [(P.toFinset.powersetCard a, {∅})]
  else
    (splits a b).flatMap fun ij =>
      rectProducts (plan (P.take (P.length / 2)) ij.1 ij.2)
        (plan (P.drop (P.length / 2)) (a - ij.1) (b - ij.2))
termination_by P.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

/-! ### Counting rectangle incidences -/

/-- The number of listed rectangles containing a given source and target. -/
def hits (L : List (Rect α)) (S T : Finset α) : ℕ :=
  (L.map fun R => if S ∈ R.1 ∧ T ∈ R.2 then 1 else 0).sum

@[simp] theorem hits_nil (S T : Finset α) : hits ([] : List (Rect α)) S T = 0 := rfl

theorem hits_cons (R : Rect α) (L : List (Rect α)) (S T : Finset α) :
    hits (R :: L) S T = (if S ∈ R.1 ∧ T ∈ R.2 then 1 else 0) + hits L S T := by
  simp [hits]

theorem hits_flatMap {β : Type*} (l : List β) (f : β → List (Rect α)) (S T : Finset α) :
    hits (l.flatMap f) S T = (l.map fun x => hits (f x) S T).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    simp [hits]

theorem mem_join {A B : Finset (Finset α)} {S : Finset α} :
    S ∈ join A B ↔ ∃ X ∈ A, ∃ Y ∈ B, X ∪ Y = S := by
  simp [join, and_assoc]

/-- A member of a join on disjoint grounds is determined by its two traces. -/
theorem mem_join_iff {A B : Finset (Finset α)} {G₁ G₂ S : Finset α} (hd : Disjoint G₁ G₂)
    (hA : ∀ X ∈ A, X ⊆ G₁) (hB : ∀ Y ∈ B, Y ⊆ G₂) :
    S ∈ join A B ↔ S ⊆ G₁ ∪ G₂ ∧ S ∩ G₁ ∈ A ∧ S ∩ G₂ ∈ B := by
  rw [mem_join]
  constructor
  · rintro ⟨X, hX, Y, hY, rfl⟩
    have hXY : Disjoint X G₂ := Finset.disjoint_of_subset_left (hA X hX) hd
    have hYX : Disjoint Y G₁ := Finset.disjoint_of_subset_left (hB Y hY) hd.symm
    refine ⟨Finset.union_subset_union (hA X hX) (hB Y hY), ?_, ?_⟩
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr (hA X hX),
        Finset.disjoint_iff_inter_eq_empty.mp hYX, Finset.union_empty]
      exact hX
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr (hB Y hY),
        Finset.disjoint_iff_inter_eq_empty.mp hXY, Finset.empty_union]
      exact hY
  · rintro ⟨hS, h₁, h₂⟩
    refine ⟨_, h₁, _, h₂, ?_⟩
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS]

/-- Products on disjoint grounds multiply incidence counts. -/
theorem hits_rectProducts {G₁ G₂ : Finset α} (hd : Disjoint G₁ G₂) (xs ys : List (Rect α))
    (hx : ∀ R ∈ xs, (∀ X ∈ R.1, X ⊆ G₁) ∧ ∀ X ∈ R.2, X ⊆ G₁)
    (hy : ∀ R ∈ ys, (∀ Y ∈ R.1, Y ⊆ G₂) ∧ ∀ Y ∈ R.2, Y ⊆ G₂) (S T : Finset α) :
    hits (rectProducts xs ys) S T =
      if S ⊆ G₁ ∪ G₂ ∧ T ⊆ G₁ ∪ G₂ then
        hits xs (S ∩ G₁) (T ∩ G₁) * hits ys (S ∩ G₂) (T ∩ G₂) else 0 := by
  rw [rectProducts, hits_flatMap]
  have hrow : ∀ R₁ ∈ xs, hits (ys.map (rectJoin R₁)) S T =
      if S ⊆ G₁ ∪ G₂ ∧ T ⊆ G₁ ∪ G₂ then
        (if S ∩ G₁ ∈ R₁.1 ∧ T ∩ G₁ ∈ R₁.2 then 1 else 0) * hits ys (S ∩ G₂) (T ∩ G₂)
      else 0 := by
    intro R₁ hR₁
    have hcell : ∀ R₂ ∈ ys, (if S ∈ (rectJoin R₁ R₂).1 ∧ T ∈ (rectJoin R₁ R₂).2 then 1 else 0) =
        if S ⊆ G₁ ∪ G₂ ∧ T ⊆ G₁ ∪ G₂ then
          (if S ∩ G₁ ∈ R₁.1 ∧ T ∩ G₁ ∈ R₁.2 then 1 else 0) *
            (if S ∩ G₂ ∈ R₂.1 ∧ T ∩ G₂ ∈ R₂.2 then 1 else 0)
        else 0 := by
      intro R₂ hR₂
      simp only [rectJoin, mem_join_iff hd (hx R₁ hR₁).1 (hy R₂ hR₂).1,
        mem_join_iff hd (hx R₁ hR₁).2 (hy R₂ hR₂).2]
      by_cases hS : S ⊆ G₁ ∪ G₂ <;> by_cases hT : T ⊆ G₁ ∪ G₂ <;> simp only [hS, hT] <;>
        split_ifs <;> simp_all
    unfold hits
    rw [List.map_map]
    simp only [Function.comp_def]
    rw [List.map_congr_left (fun R₂ hR₂ => hcell R₂ hR₂)]
    by_cases h : S ⊆ G₁ ∪ G₂ ∧ T ⊆ G₁ ∪ G₂
    · simp only [if_pos h]
      exact List.sum_map_mul_left (R := ℕ) _ _ _
    · simp [if_neg h]
  rw [List.map_congr_left (fun R₁ hR₁ => hrow R₁ hR₁)]
  by_cases h : S ⊆ G₁ ∪ G₂ ∧ T ⊆ G₁ ∪ G₂
  · simp only [if_pos h]
    unfold hits
    exact List.sum_map_mul_right (R := ℕ) _ _ _
  · simp [if_neg h]

/-! ### Exact cover -/

/-- The relation covered by `plan P a b`. -/
def Rel (P : List α) (a b : ℕ) (S T : Finset α) : Prop :=
  S ⊆ P.toFinset ∧ S.card = a ∧ T ⊆ P.toFinset ∧ T.card = b ∧ Disjoint S T

instance (P : List α) (a b : ℕ) (S T : Finset α) : Decidable (Rel P a b S T) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem mem_splits {a b i j : ℕ} : (i, j) ∈ splits a b ↔ i ≤ a ∧ j ≤ b := by
  simp [splits, Nat.lt_succ_iff]

theorem splits_nodup (a b : ℕ) : (splits a b).Nodup := by
  unfold splits
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => (List.nodup_range).map (fun j j' h => by simpa using h), ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun i _ i' _ hii' => ?_
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro _ ⟨j, -, rfl⟩ ⟨j', -, h⟩
  exact hii' (congrArg Prod.fst h).symm

/-- The two halves of a duplicate-free ground list are disjoint. -/
theorem halves_disjoint {P : List α} (hP : P.Nodup) (k : ℕ) :
    Disjoint (P.take k).toFinset (P.drop k).toFinset :=
  List.disjoint_toFinset_iff_disjoint.mpr (List.disjoint_take_drop hP le_rfl)

theorem halves_union (P : List α) (k : ℕ) :
    (P.take k).toFinset ∪ (P.drop k).toFinset = P.toFinset := by
  rw [← List.toFinset_append, List.take_append_drop]

/-- Every member of a plan lies in the ground set with the stated size. -/
theorem plan_sound (P : List α) (a b : ℕ) : P.Nodup → ∀ R ∈ plan P a b,
    (∀ S ∈ R.1, S ⊆ P.toFinset ∧ S.card = a) ∧ (∀ T ∈ R.2, T ⊆ P.toFinset ∧ T.card = b) := by
  induction P, a, b using plan.induct with
  | case1 P a b hab =>
    intro _ R hR
    rw [plan, dif_pos hab] at hR
    simp at hR
  | case2 P b hab =>
    intro _ R hR
    rw [plan, dif_neg hab, dif_pos rfl] at hR
    simp only [List.mem_singleton] at hR
    subst hR
    refine ⟨fun S hS => ?_, fun T hT => Finset.mem_powersetCard.mp hT⟩
    simp only [Finset.mem_singleton] at hS
    simp [hS]
  | case3 P a ha hab =>
    intro _ R hR
    rw [plan, dif_neg hab, dif_neg ha, dif_pos rfl] at hR
    simp only [List.mem_singleton] at hR
    subst hR
    refine ⟨fun S hS => Finset.mem_powersetCard.mp hS, fun T hT => ?_⟩
    simp only [Finset.mem_singleton] at hT
    simp [hT]
  | case4 P a b hab ha hb ih₁ ih₂ =>
    intro hP R hR
    rw [plan, dif_neg hab, dif_neg ha, dif_neg hb] at hR
    obtain ⟨⟨i, j⟩, hij, hR⟩ := List.mem_flatMap.mp hR
    obtain ⟨hi, hj⟩ := mem_splits.mp hij
    obtain ⟨R₁, hR₁, hR⟩ := List.mem_flatMap.mp hR
    obtain ⟨R₂, hR₂, rfl⟩ := List.mem_map.mp hR
    have s₁ := ih₁ (i, j) (hP.sublist (List.take_sublist _ _)) R₁ hR₁
    have s₂ := ih₂ (i, j) (hP.sublist (List.drop_sublist _ _)) R₂ hR₂
    have hd := halves_disjoint hP (P.length / 2)
    have hu := halves_union P (P.length / 2)
    have hpiece : ∀ (A B : Finset (Finset α)) (u v : ℕ),
        (∀ X ∈ A, X ⊆ (P.take (P.length / 2)).toFinset ∧ X.card = u) →
        (∀ Y ∈ B, Y ⊆ (P.drop (P.length / 2)).toFinset ∧ Y.card = v) →
        ∀ S ∈ join A B, S ⊆ P.toFinset ∧ S.card = u + v := by
      intro A B u v hA hB S hS
      obtain ⟨X, hX, Y, hY, rfl⟩ := mem_join.mp hS
      refine ⟨hu ▸ Finset.union_subset_union (hA X hX).1 (hB Y hY).1, ?_⟩
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_left (hA X hX).1 (Finset.disjoint_of_subset_right (hB Y hY).1 hd)),
        (hA X hX).2, (hB Y hY).2]
    refine ⟨fun S hS => ?_, fun T hT => ?_⟩
    · have := hpiece _ _ _ _ s₁.1 s₂.1 S hS
      exact ⟨this.1, by rw [this.2]; omega⟩
    · have := hpiece _ _ _ _ s₁.2 s₂.2 T hT
      exact ⟨this.1, by rw [this.2]; omega⟩

/-- Splitting a subset of two disjoint grounds into its two traces. -/
theorem card_traces {G₁ G₂ S : Finset α} (hd : Disjoint G₁ G₂) (hS : S ⊆ G₁ ∪ G₂) :
    (S ∩ G₁).card + (S ∩ G₂).card = S.card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hd)),
    ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS]

theorem disjoint_of_traces {G₁ G₂ S T : Finset α} (hd : Disjoint G₁ G₂)
    (hS : S ⊆ G₁ ∪ G₂) (hT : T ⊆ G₁ ∪ G₂)
    (h₁ : Disjoint (S ∩ G₁) (T ∩ G₁)) (h₂ : Disjoint (S ∩ G₂) (T ∩ G₂)) : Disjoint S T := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  rcases Finset.mem_union.mp (hS hxS) with hx | hx
  · exact Finset.disjoint_left.mp h₁ (Finset.mem_inter.mpr ⟨hxS, hx⟩) (Finset.mem_inter.mpr ⟨hxT, hx⟩)
  · exact Finset.disjoint_left.mp h₂ (Finset.mem_inter.mpr ⟨hxS, hx⟩) (Finset.mem_inter.mpr ⟨hxT, hx⟩)

/-- A pair splits into covered halves exactly at its own trace sizes. -/
theorem rel_halves_iff {P : List α} (hP : P.Nodup) (k : ℕ) {a b i j : ℕ} (hi : i ≤ a) (hj : j ≤ b)
    (S T : Finset α) :
    ((S ⊆ (P.take k).toFinset ∪ (P.drop k).toFinset ∧ T ⊆ (P.take k).toFinset ∪ (P.drop k).toFinset) ∧
      Rel (P.take k) i j (S ∩ (P.take k).toFinset) (T ∩ (P.take k).toFinset) ∧
      Rel (P.drop k) (a - i) (b - j) (S ∩ (P.drop k).toFinset) (T ∩ (P.drop k).toFinset)) ↔
    ((i, j) = ((S ∩ (P.take k).toFinset).card, (T ∩ (P.take k).toFinset).card) ∧ Rel P a b S T) := by
  have hd := halves_disjoint hP k
  have hu := halves_union P k
  set G₁ := (P.take k).toFinset
  set G₂ := (P.drop k).toFinset
  constructor
  · rintro ⟨⟨hS, hT⟩, ⟨-, hS₁, -, hT₁, hST₁⟩, ⟨-, hS₂, -, hT₂, hST₂⟩⟩
    have cS := card_traces hd hS
    have cT := card_traces hd hT
    refine ⟨by rw [hS₁, hT₁], hu ▸ hS, by omega, hu ▸ hT, by omega,
      disjoint_of_traces hd hS hT hST₁ hST₂⟩
  · rintro ⟨hij, hS, hSa, hT, hTb, hST⟩
    simp only [Prod.mk.injEq] at hij
    obtain ⟨rfl, rfl⟩ := hij
    rw [← hu] at hS hT
    have cS := card_traces hd hS
    have cT := card_traces hd hT
    refine ⟨⟨hS, hT⟩, ⟨Finset.inter_subset_right, rfl, Finset.inter_subset_right, rfl,
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hST)⟩,
      ⟨Finset.inter_subset_right, by omega, Finset.inter_subset_right, by omega,
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hST)⟩⟩

/-- Summing an indicator over a duplicate-free list hits a member once. -/
theorem sum_indicator {β : Type*} [DecidableEq β] (l : List β) (hl : l.Nodup) (x : β)
    (Q : Prop) [Decidable Q] (hx : Q → x ∈ l) :
    (l.map fun y => if y = x ∧ Q then 1 else 0).sum = if Q then 1 else 0 := by
  by_cases hQ : Q
  · simp only [hQ, and_true, if_true]
    induction l with
    | nil => exact absurd (hx hQ) (List.not_mem_nil)
    | cons y l ih =>
      rw [List.map_cons, List.sum_cons]
      obtain ⟨hy, hl'⟩ := List.nodup_cons.mp hl
      by_cases hyx : y = x
      · subst hyx
        rw [if_pos rfl, List.map_congr_left (g := fun _ => 0)]
        · simp
        · intro z hz
          rw [if_neg]
          rintro rfl
          exact hy hz
      · rw [if_neg hyx, ih hl' (fun _ => (List.mem_cons.mp (hx hQ)).resolve_left (Ne.symm hyx)),
          zero_add]
  · simp [hQ]

/-- Each disjoint pair of the right sizes lies in exactly one rectangle of the plan. -/
theorem plan_hits (P : List α) (a b : ℕ) : P.Nodup → ∀ S T : Finset α,
    hits (plan P a b) S T = if Rel P a b S T then 1 else 0 := by
  induction P, a, b using plan.induct with
  | case1 P a b hab =>
    intro _ S T
    rw [plan, dif_pos hab, hits_nil, if_neg]
    rintro ⟨hS, hSa, hT, hTb, hST⟩
    have h := Finset.card_le_card (Finset.union_subset hS hT)
    rw [Finset.card_union_of_disjoint hST, hSa, hTb] at h
    have := List.toFinset_card_le P
    omega
  | case2 P b hab =>
    intro _ S T
    rw [plan, dif_neg hab, dif_pos rfl, hits_cons, hits_nil, add_zero]
    by_cases hS : S = ∅
    · subst hS
      simp [Rel, Finset.mem_powersetCard]
    · simp [Rel, hS]
  | case3 P a ha hab =>
    intro _ S T
    rw [plan, dif_neg hab, dif_neg ha, dif_pos rfl, hits_cons, hits_nil, add_zero]
    by_cases hT : T = ∅
    · subst hT
      simp [Rel, Finset.mem_powersetCard]
    · simp [Rel, hT]
  | case4 P a b hab ha hb ih₁ ih₂ =>
    intro hP S T
    rw [plan, dif_neg hab, dif_neg ha, dif_neg hb, hits_flatMap]
    have hP₁ : (P.take (P.length / 2)).Nodup := hP.sublist (List.take_sublist _ _)
    have hP₂ : (P.drop (P.length / 2)).Nodup := hP.sublist (List.drop_sublist _ _)
    have hd := halves_disjoint hP (P.length / 2)
    have hterm : ∀ ij ∈ splits a b,
        hits (rectProducts (plan (P.take (P.length / 2)) ij.1 ij.2)
          (plan (P.drop (P.length / 2)) (a - ij.1) (b - ij.2))) S T =
        if ij = ((S ∩ (P.take (P.length / 2)).toFinset).card,
            (T ∩ (P.take (P.length / 2)).toFinset).card) ∧ Rel P a b S T then 1 else 0 := by
      rintro ⟨i, j⟩ hij
      obtain ⟨hi, hj⟩ := mem_splits.mp hij
      rw [hits_rectProducts hd _ _
        (fun R hR => ⟨fun X hX => ((plan_sound _ _ _ hP₁ R hR).1 X hX).1,
          fun X hX => ((plan_sound _ _ _ hP₁ R hR).2 X hX).1⟩)
        (fun R hR => ⟨fun Y hY => ((plan_sound _ _ _ hP₂ R hR).1 Y hY).1,
          fun Y hY => ((plan_sound _ _ _ hP₂ R hR).2 Y hY).1⟩),
        ih₁ (i, j) hP₁, ih₂ (i, j) hP₂]
      rw [← if_congr (rel_halves_iff hP (P.length / 2) hi hj S T) rfl rfl]
      by_cases h₀ : S ⊆ (P.take (P.length / 2)).toFinset ∪ (P.drop (P.length / 2)).toFinset ∧
          T ⊆ (P.take (P.length / 2)).toFinset ∪ (P.drop (P.length / 2)).toFinset
      · simp only [h₀, true_and, if_true]
        split_ifs <;> simp_all
      · simp [h₀]
    rw [List.map_congr_left hterm]
    apply sum_indicator _ (splits_nodup a b)
    rintro ⟨hS, hSa, hT, hTb, -⟩
    apply mem_splits.mpr
    constructor
    · rw [← hSa]; exact Finset.card_le_card Finset.inter_subset_left
    · rw [← hTb]; exact Finset.card_le_card Finset.inter_subset_left

/-- Sources and targets of a plan's rectangles are disjoint. -/
theorem hits_pos {L : List (Rect α)} {R : Rect α} (hR : R ∈ L) {S T : Finset α}
    (hS : S ∈ R.1) (hT : T ∈ R.2) : 0 < hits L S T := by
  induction L with
  | nil => simp at hR
  | cons R' L ih =>
    rw [hits_cons]
    rcases List.mem_cons.mp hR with rfl | hR
    · simp [hS, hT]
    · have := ih hR
      omega

theorem plan_disjoint {P : List α} (hP : P.Nodup) {a b : ℕ} {R : Rect α} (hR : R ∈ plan P a b)
    {S T : Finset α} (hS : S ∈ R.1) (hT : T ∈ R.2) : Disjoint S T := by
  have hpos := hits_pos hR hS hT
  rw [plan_hits P a b hP S T] at hpos
  split_ifs at hpos with h
  · exact h.2.2.2.2
  · exact absurd hpos (lt_irrefl 0)

/-! ### Membership counts -/

theorem union_inter_left {G₁ G₂ X Y : Finset α} (hd : Disjoint G₁ G₂) (hX : X ⊆ G₁)
    (hY : Y ⊆ G₂) : (X ∪ Y) ∩ G₁ = X := by
  rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hX,
    Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left hY hd.symm),
    Finset.union_empty]

theorem union_inter_right {G₁ G₂ X Y : Finset α} (hd : Disjoint G₁ G₂) (hX : X ⊆ G₁)
    (hY : Y ⊆ G₂) : (X ∪ Y) ∩ G₂ = Y := by
  rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hY,
    Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left hX hd),
    Finset.empty_union]

/-- Joins of families on disjoint grounds have product size. -/
theorem card_join {A B : Finset (Finset α)} {G₁ G₂ : Finset α} (hd : Disjoint G₁ G₂)
    (hA : ∀ X ∈ A, X ⊆ G₁) (hB : ∀ Y ∈ B, Y ⊆ G₂) : (join A B).card = A.card * B.card := by
  rw [join, Finset.card_image_of_injOn, Finset.card_product]
  rintro ⟨X, Y⟩ hXY ⟨X', Y'⟩ hXY' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hXY hXY'
  simp only at h
  have e₁ := union_inter_left hd (hA X hXY.1) (hB Y hXY.2)
  have e₂ := union_inter_right hd (hA X hXY.1) (hB Y hXY.2)
  rw [h, union_inter_left hd (hA X' hXY'.1) (hB Y' hXY'.2)] at e₁
  rw [h, union_inter_right hd (hA X' hXY'.1) (hB Y' hXY'.2)] at e₂
  rw [e₁, e₂]

theorem sum_flatMap {β : Type*} (l : List β) (f : β → List ℕ) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_rectProducts {G₁ G₂ : Finset α} (hd : Disjoint G₁ G₂) (xs ys : List (Rect α))
    (hx : ∀ R ∈ xs, (∀ X ∈ R.1, X ⊆ G₁) ∧ ∀ X ∈ R.2, X ⊆ G₁)
    (hy : ∀ R ∈ ys, (∀ Y ∈ R.1, Y ⊆ G₂) ∧ ∀ Y ∈ R.2, Y ⊆ G₂) :
    ((rectProducts xs ys).map fun R => R.1.card).sum =
        (xs.map fun R => R.1.card).sum * (ys.map fun R => R.1.card).sum ∧
      ((rectProducts xs ys).map fun R => R.2.card).sum =
        (xs.map fun R => R.2.card).sum * (ys.map fun R => R.2.card).sum := by
  unfold rectProducts
  simp only [List.map_flatMap, sum_flatMap, List.map_map, Function.comp_def, rectJoin]
  constructor
  · rw [← List.sum_map_mul_right (R := ℕ)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro R₁ hR₁
    rw [← List.sum_map_mul_left (R := ℕ)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro R₂ hR₂
    exact card_join hd (hx R₁ hR₁).1 (hy R₂ hR₂).1
  · rw [← List.sum_map_mul_right (R := ℕ)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro R₁ hR₁
    rw [← List.sum_map_mul_left (R := ℕ)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro R₂ hR₂
    exact card_join hd (hx R₁ hR₁).2 (hy R₂ hR₂).2

/-- Total source memberships of `plan` on a ground of size `n`, with recursion fuel `f`. -/
def srcCount : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | f + 1, n, a, b =>
    if n < a + b then 0 else if a = 0 then 1 else if b = 0 then n.choose a else
      ((splits a b).map fun ij =>
        srcCount f (n / 2) ij.1 ij.2 * srcCount f (n - n / 2) (a - ij.1) (b - ij.2)).sum

/-- Total target memberships of `plan` on a ground of size `n`, with recursion fuel `f`. -/
def tgtCount : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | f + 1, n, a, b =>
    if n < a + b then 0 else if a = 0 then n.choose b else if b = 0 then 1 else
      ((splits a b).map fun ij =>
        tgtCount f (n / 2) ij.1 ij.2 * tgtCount f (n - n / 2) (a - ij.1) (b - ij.2)).sum

/-- The membership totals of a plan are given by the count recursions. -/
theorem plan_counts (P : List α) (a b : ℕ) : P.Nodup → ∀ f, P.length < f →
    ((plan P a b).map fun R => R.1.card).sum = srcCount f P.length a b ∧
      ((plan P a b).map fun R => R.2.card).sum = tgtCount f P.length a b := by
  induction P, a, b using plan.induct with
  | case1 P a b hab =>
    intro _ f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [plan, dif_pos hab]
    simp [srcCount, tgtCount, hab]
  | case2 P b hab =>
    intro hP f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [plan, dif_neg hab, dif_pos rfl]
    simp only [zero_add] at hab
    simp [srcCount, tgtCount, Finset.card_powersetCard, List.toFinset_card_of_nodup hP]
    omega
  | case3 P a ha hab =>
    intro hP f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [plan, dif_neg hab, dif_neg ha, dif_pos rfl]
    simp only [add_zero] at hab
    simp [srcCount, tgtCount, ha, Finset.card_powersetCard, List.toFinset_card_of_nodup hP]
    omega
  | case4 P a b hab ha hb ih₁ ih₂ =>
    intro hP f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hP₁ : (P.take (P.length / 2)).Nodup := hP.sublist (List.take_sublist _ _)
    have hP₂ : (P.drop (P.length / 2)).Nodup := hP.sublist (List.drop_sublist _ _)
    have hd := halves_disjoint hP (P.length / 2)
    have l₁ : (P.take (P.length / 2)).length = P.length / 2 := by
      rw [List.length_take]; omega
    have l₂ : (P.drop (P.length / 2)).length = P.length - P.length / 2 := List.length_drop
    have hpart : ∀ ij : ℕ × ℕ,
        ((rectProducts (plan (P.take (P.length / 2)) ij.1 ij.2)
          (plan (P.drop (P.length / 2)) (a - ij.1) (b - ij.2))).map fun R => R.1.card).sum =
          srcCount f (P.length / 2) ij.1 ij.2 *
            srcCount f (P.length - P.length / 2) (a - ij.1) (b - ij.2) ∧
        ((rectProducts (plan (P.take (P.length / 2)) ij.1 ij.2)
          (plan (P.drop (P.length / 2)) (a - ij.1) (b - ij.2))).map fun R => R.2.card).sum =
          tgtCount f (P.length / 2) ij.1 ij.2 *
            tgtCount f (P.length - P.length / 2) (a - ij.1) (b - ij.2) := by
      intro ij
      have c₁ := ih₁ ij hP₁ f (by omega)
      have c₂ := ih₂ ij hP₂ f (by omega)
      rw [l₁] at c₁
      rw [l₂] at c₂
      have hs := sum_rectProducts hd (plan (P.take (P.length / 2)) ij.1 ij.2)
        (plan (P.drop (P.length / 2)) (a - ij.1) (b - ij.2))
        (fun R hR => ⟨fun X hX => ((plan_sound _ _ _ hP₁ R hR).1 X hX).1,
          fun X hX => ((plan_sound _ _ _ hP₁ R hR).2 X hX).1⟩)
        (fun R hR => ⟨fun Y hY => ((plan_sound _ _ _ hP₂ R hR).1 Y hY).1,
          fun Y hY => ((plan_sound _ _ _ hP₂ R hR).2 Y hY).1⟩)
      rw [hs.1, hs.2, c₁.1, c₁.2, c₂.1, c₂.2]
      exact ⟨rfl, rfl⟩
    rw [plan, dif_neg hab, dif_neg ha, dif_neg hb]
    simp only [List.map_flatMap, sum_flatMap]
    simp only [srcCount, tgtCount, if_neg hab, if_neg ha, if_neg hb]
    exact ⟨congrArg List.sum (List.map_congr_left fun ij _ => (hpart ij).1),
      congrArg List.sum (List.map_congr_left fun ij _ => (hpart ij).2)⟩

/-! ### The plan of disjoint triple pairs on 25 points -/

/-- The rectangle plan of ordered disjoint pairs of three-point subsets of `Fin 25`. -/
def plan25 : List (Rect (Fin 25)) := plan (List.finRange 25) 3 3

/-- Every ordered pair of disjoint triples lies in exactly one rectangle. -/
theorem plan25_hits (S T : Finset (Fin 25)) :
    hits plan25 S T = if S.card = 3 ∧ T.card = 3 ∧ Disjoint S T then 1 else 0 := by
  rw [plan25, plan_hits _ _ _ (List.nodup_finRange 25)]
  simp [Rel]

/-- Rectangle sources and targets are triples. -/
theorem plan25_sound {R : Rect (Fin 25)} (hR : R ∈ plan25) :
    (∀ S ∈ R.1, S.card = 3) ∧ ∀ T ∈ R.2, T.card = 3 :=
  ⟨fun S hS => ((plan_sound _ _ _ (List.nodup_finRange 25) R hR).1 S hS).2,
    fun T hT => ((plan_sound _ _ _ (List.nodup_finRange 25) R hR).2 T hT).2⟩

theorem plan25_disjoint {R : Rect (Fin 25)} (hR : R ∈ plan25) {S T : Finset (Fin 25)}
    (hS : S ∈ R.1) (hT : T ∈ R.2) : Disjoint S T :=
  plan_disjoint (List.nodup_finRange 25) hR hS hT

/-- The plan has `224802` source memberships and `224802` target memberships. -/
theorem plan25_counts :
    (plan25.map fun R => R.1.card).sum = 224802 ∧ (plan25.map fun R => R.2.card).sum = 224802 := by
  have h := plan_counts (List.finRange 25) 3 3 (List.nodup_finRange 25) 26 (by simp)
  rw [List.length_finRange] at h
  rw [plan25, h.1, h.2]
  constructor <;> decide

end IntegerMultBounds.Networks.Mixer.Rectangles
