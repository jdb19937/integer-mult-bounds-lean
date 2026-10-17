module

public import IntegerMultBounds.Networks.PairedPresence
public import IntegerMultBounds.Networks.PairedStripCorrect

/-! Structural tools for counting one paired recursion level: every stage
extends its DAG, loops may be charged under an invariant, the consecutive
grouping of an odd range is explicit, and strip lookups return the strip
built for their vertex. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedLevelTools

open DisjointCircuit DisjointBuilder PairedCircuit DAGAllocator

variable {ι X Y : Type*} [DecidableEq ι]

theorem smartAdd_extends (nodes : List (Node ι)) (l r : Ref) :
    Extends nodes (smartAdd nodes l r).1 := by
  cases l <;> cases r
  all_goals first | exact extends_refl _ | skip
  simp only [smartAdd]
  unfold intern
  split
  · exact extends_refl _
  · exact ⟨[_], rfl⟩

theorem total_extends (nodes : List (Node ι)) (refs : List Ref) :
    Extends nodes (DisjointBalanced.total nodes refs).1 := by
  induction refs using (measure (fun rs : List Ref => rs.length)).wf.induction generalizing nodes with
  | h refs ih =>
    cases refs with
    | nil => simp only [DisjointBalanced.total]; exact extends_refl _
    | cons r tail =>
      cases tail with
      | nil => simp only [DisjointBalanced.total]; exact extends_refl _
      | cons s rs =>
        let values := r :: s :: rs
        let left := values.take (values.length / 2)
        let right := values.drop (values.length / 2)
        have hlen : 2 ≤ values.length := by simp [values]
        have hl : left.length < values.length := by simp only [left, List.length_take]; omega
        have hr : right.length < values.length := by simp only [right, List.length_drop]; omega
        rw [DisjointBalanced.total]
        exact extends_trans (ih left hl nodes) (extends_trans (ih right hr _) (smartAdd_extends _ _ _))

omit [DecidableEq ι] in
theorem mapBuild_extends (f : List (Node ι) → X → List (Node ι) × Y)
    (h : ∀ ns x, Extends ns (f ns x).1) (nodes : List (Node ι)) (xs : List X) :
    Extends nodes (mapBuild f nodes xs).1 := by
  induction xs generalizing nodes with
  | nil => exact extends_refl _
  | cons x xs ih => exact extends_trans (h nodes x) (ih _)

theorem prefixBuild_extends (nodes : List (Node ι)) (acc : Ref) (refs : List Ref) :
    Extends nodes (prefixBuild nodes acc refs).1 := by
  induction refs generalizing nodes acc with
  | nil => exact extends_refl _
  | cons r rs ih => exact extends_trans (smartAdd_extends nodes acc r) (ih _ _)

theorem suffixBuild_extends (nodes : List (Node ι)) (refs : List Ref) :
    Extends nodes (suffixBuild nodes refs).1 := by
  induction refs with
  | nil => exact extends_refl _
  | cons r rs ih => exact extends_trans ih (smartAdd_extends _ _ _)

theorem vectorTail_extends (nodes : List (Node ι)) (refs : List Ref) :
    Extends nodes (vectorTail nodes refs).nodes := by
  cases refs with
  | nil => exact extends_refl _
  | cons c vs =>
    exact extends_trans (prefixBuild_extends _ _ _) (extends_trans (suffixBuild_extends _ _)
      (mapBuild_extends _ (fun ns (p : Ref × Ref) => smartAdd_extends ns p.1 p.2) _ _))

theorem buildStrip_extends (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) :
    Extends nodes (buildStrip nodes groups edges weights ia).1 :=
  extends_trans (total_extends _ _) (extends_trans
    (mapBuild_extends _ (fun ns _ => total_extends ns _) _ _) (vectorTail_extends _ _))

omit [DecidableEq ι] in
/-- Charge a loop body under an invariant preserved by every iteration. -/
theorem mapBuild_additions_le_inv (f : List (Node ι) → X → List (Node ι) × Y)
    (budget : X → ℕ) (inv : List (Node ι) → Prop) (xs : List X)
    (hinv : ∀ ns, ∀ x ∈ xs, inv ns → inv (f ns x).1)
    (h : ∀ ns, ∀ x ∈ xs, inv ns → additionCount (f ns x).1 ≤ additionCount ns + budget x)
    (nodes : List (Node ι)) (hn : inv nodes) :
    additionCount (mapBuild f nodes xs).1 ≤ additionCount nodes + (xs.map budget).sum := by
  induction xs generalizing nodes with
  | nil => simp [mapBuild]
  | cons x xs ih =>
    have hs := h nodes x (by simp) hn
    have ht := ih (fun ns y hy => hinv ns y (by simp [hy])) (fun ns y hy => h ns y (by simp [hy]))
      (f nodes x).1 (hinv nodes x (by simp) hn)
    simp only [mapBuild, List.map_cons, List.sum_cons]
    omega

omit [DecidableEq ι] in
/-- State-independent output facts of a loop body hold for every output. -/
theorem mapBuild_forall₂ (f : List (Node ι) → X → List (Node ι) × Y) (post : X → Y → Prop)
    (xs : List X) (h : ∀ ns, ∀ x ∈ xs, post x (f ns x).2) (nodes : List (Node ι)) :
    List.Forall₂ post xs (mapBuild f nodes xs).2 := by
  induction xs generalizing nodes with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    exact List.Forall₂.cons (h nodes x (by simp)) (ih (fun ns y hy => h ns y (by simp [hy])) _)

/-- A strip lookup returns the strip built for that vertex. -/
theorem stripLookup_of_forall₂ (post : ℕ × ℕ → Strip → Prop)
    (hv : ∀ ia s, post ia s → s.vertex = ia.2) (ias : List (ℕ × ℕ)) (strips : List Strip)
    (hs : List.Forall₂ post ias strips) (hn : (ias.map Prod.snd).Nodup) (ia : ℕ × ℕ) (hia : ia ∈ ias) :
    post ia (stripLookup strips ia.2) := by
  induction hs with
  | nil => simp at hia
  | @cons key entry keys entries hh _ ih =>
    obtain ⟨hne, htail⟩ := List.nodup_cons.mp hn
    have hvert := hv key entry hh
    rcases List.mem_cons.mp hia with rfl | hia
    · simpa [stripLookup, hvert] using hh
    · have hkey : entry.vertex ≠ ia.2 := by
        rw [hvert]
        intro he
        exact hne (he ▸ List.mem_map.mpr ⟨ia, hia, rfl⟩)
      simpa [stripLookup, hkey] using ih htail hia

/-- Consecutive grouping of an odd interval: pairs, then one singleton. -/
theorem groups_range' (s m : ℕ) :
    PairGrouping.groups (List.range' s (2 * m + 1)) =
      (List.range m).map (fun i => [s + 2 * i, s + 2 * i + 1]) ++ [[s + 2 * m]] := by
  induction m generalizing s with
  | zero => simp [PairGrouping.groups]
  | succ m ih =>
    have h : List.range' s (2 * (m + 1) + 1) = s :: (s + 1) :: List.range' (s + 2) (2 * m + 1) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega, List.range'_succ, List.range'_succ]
    rw [h, PairGrouping.groups, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.cons_append, List.cons.injEq]
    refine ⟨by simp, ?_⟩
    congr 1
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, List.cons.injEq, and_true]
      omega
    · congr 2; omega

theorem groups_range_odd (m : ℕ) :
    PairGrouping.groups (List.range (2 * m + 1)) =
      (List.range m).map (fun i => [2 * i, 2 * i + 1]) ++ [[2 * m]] := by
  rw [List.range_eq_range', groups_range']
  simp

end IntegerMultBounds.Networks.PairedLevelTools
