module

public import IntegerMultBounds.MathlibTM2.M8.Local.Schedule
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card

/-!
# The slot count of the compiler

Every leaf takes one slot and every free use after a node's first takes one more, so the
compiler uses `Σ_y |freeUses y| − (N − v)` slots (`compile_next_sum`). Counting uses by their
nodes, the free uses are all uses but the linked ones: `2 (N − v)` argument uses and one use per
root, less one per donor. So the slot count is `(N − v) + rootCount − #donors` (`compile_next`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Classical Finset

namespace Dag
variable (D : Dag)

theorem step_next (_hv : D.Valid) (st : State) {k : ℕ} (_hk : k < D.N) :
    (D.step st k).next = st.next + ((D.freeUses k).length - 1) + (if k < D.v then 1 else 0) := by
  unfold step
  split_ifs with hleaf
  · rw [(State.serve_ops _ _ _ _).2]; simp only; omega
  · cases hl : D.link k with
    | none => dsimp only; rw [(State.serve_ops _ _ _ _).2]; simp
    | some l =>
      obtain ⟨o, t, pos⟩ := l
      dsimp only
      rw [(State.serve_ops _ _ _ _).2]; simp

theorem freeUses_length_pos (hv : D.Valid) {k : ℕ} (hk : k < D.N) : 1 ≤ (D.freeUses k).length :=
  List.length_pos_iff.mpr (hv.free_ne k hk)

theorem compileTo_next (hv : D.Valid) : ∀ k, k ≤ D.N →
    (D.compileTo k).next + (min k D.v - min k D.v) + k =
      ((List.range k).map fun n => (D.freeUses n).length).sum + min k D.v := by
  intro k
  induction k with
  | zero => intro _; simp [compileTo, start]
  | succ k ih =>
    intro hk
    have he : D.compileTo (k + 1) = D.step (D.compileTo k) k := by
      simp only [compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [he, D.step_next hv _ (by omega), List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]
    have h1 := ih (by omega)
    have h2 := D.freeUses_length_pos hv (show k < D.N by omega)
    simp only [Nat.sub_self, add_zero] at h1 ⊢
    split_ifs with hkv
    · rw [show min (k + 1) D.v = min k D.v + 1 by omega]; omega
    · rw [show min (k + 1) D.v = min k D.v by omega]; omega

/-- **The slot count**, as a sum over nodes. -/
theorem compile_next_sum (hv : D.Valid) :
    D.compile.next + D.N = ((List.range D.N).map fun n => (D.freeUses n).length).sum + D.v := by
  have h := D.compileTo_next hv D.N le_rfl
  simp only [Nat.sub_self, add_zero, min_eq_right hv.v_le] at h
  exact h

/-! ### Counting uses -/

/-- The uses of the nodes: arguments of additions and roots. -/
def allUses : Finset Use :=
  ((Finset.range D.N).filter (D.v ≤ ·) ×ˢ (Finset.univ : Finset Bool)).image (fun p => Use.gate p.1 p.2) ∪
    (Finset.range D.rootCount).image Use.root

theorem mem_allUses (u : Use) : u ∈ D.allUses ↔
    (∃ t pos, u = .gate t pos ∧ t < D.N ∧ D.v ≤ t) ∨ ∃ r, u = .root r ∧ r < D.rootCount := by
  simp only [allUses, Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_filter,
    Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro (⟨t, pos, ⟨ht, hv⟩, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact Or.inl ⟨t, pos, rfl, ht, hv⟩
    · exact Or.inr ⟨r, rfl, hr⟩
  · rintro (⟨t, pos, rfl, ht, hv⟩ | ⟨r, rfl, hr⟩)
    · exact Or.inl ⟨t, pos, ⟨ht, hv⟩, rfl⟩
    · exact Or.inr ⟨r, hr, rfl⟩

theorem card_allUses : D.allUses.card = 2 * (D.N - D.v) + D.rootCount := by
  rw [allUses, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun p q h => by
        obtain ⟨a, b⟩ := p; obtain ⟨c, e⟩ := q; simp only [Use.gate.injEq] at h
        rw [h.1, h.2]),
      Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_product,
      Finset.card_range, Finset.card_univ, Fintype.card_bool]
    have : ((Finset.range D.N).filter (D.v ≤ ·)).card = D.N - D.v := by
      rw [show (Finset.range D.N).filter (D.v ≤ ·) = Finset.Ico D.v D.N by
        ext n; simp [Finset.mem_Ico, and_comm], Nat.card_Ico]
    rw [this]; omega
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_image]
    rintro _ ⟨p, -, rfl⟩ ⟨r, -, h⟩
    cases h

theorem freeUses_toFinset (_hv : D.Valid) {y : ℕ} :
    (D.freeUses y).toFinset = D.allUses.filter fun u => D.useNode u = y ∧ D.linkedB u = false := by
  ext u
  rw [List.mem_toFinset, D.mem_freeUses, Finset.mem_filter, D.mem_allUses]
  constructor
  · rintro ⟨hu, hl⟩
    refine ⟨?_, D.useNode_of_mem_uses hu, hl⟩
    cases u with
    | gate t pos =>
      obtain ⟨ht, hvt, -⟩ := (D.mem_uses_gate _ t pos).mp hu
      exact Or.inl ⟨t, pos, rfl, ht, hvt⟩
    | root r =>
      obtain ⟨hr, -⟩ := (D.mem_uses_root _ r).mp hu
      exact Or.inr ⟨r, rfl, hr⟩
  · rintro ⟨hu, hy, hl⟩
    refine ⟨?_, hl⟩
    rcases hu with ⟨t, pos, rfl, ht, hvt⟩ | ⟨r, rfl, hr⟩
    · exact (D.mem_uses_gate _ t pos).mpr ⟨ht, hvt, hy⟩
    · exact (D.mem_uses_root _ r).mpr ⟨hr, hy⟩

theorem useNode_lt (hv : D.Valid) {u : Use} (hu : u ∈ D.allUses) : D.useNode u < D.N := by
  rcases (D.mem_allUses u).mp hu with ⟨t, pos, rfl, ht, hvt⟩ | ⟨r, rfl, hr⟩
  · exact lt_trans (hv.arg_lt t hvt ht pos) ht
  · exact hv.root_lt r hr

theorem list_sum_range_nat (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The free uses, counted by their nodes. -/
theorem sum_freeUses (hv : D.Valid) :
    ((List.range D.N).map fun n => (D.freeUses n).length).sum =
      (D.allUses.filter fun u => D.linkedB u = false).card := by
  have hlen : ∀ y, (D.freeUses y).length =
      ((D.allUses.filter fun u => D.linkedB u = false).filter fun u => D.useNode u = y).card := by
    intro y
    rw [← List.toFinset_card_of_nodup (D.freeUses_nodup y), D.freeUses_toFinset hv,
      Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro u _
    exact and_comm
  rw [list_sum_range_nat, Finset.sum_congr rfl fun y _ => hlen y]
  refine (Finset.card_eq_sum_card_fiberwise fun u hu => ?_).symm
  exact Finset.mem_range.mpr (D.useNode_lt hv (Finset.mem_filter.mp hu).1)

/-- The use a donor links, as a use. -/
def linkedOf (n : ℕ) : Use :=
  match D.link n with
  | some (_, t, pos) => .gate t pos
  | none => .root 0

theorem linkUse_linkedOf {n : ℕ} (h : (D.link n).isSome) : D.linkUse n = some (D.linkedOf n) := by
  unfold linkUse linkedOf
  cases hl : D.link n with
  | none => rw [hl] at h; cases h
  | some l => obtain ⟨o, t, pos⟩ := l; rfl

/-- The donors. -/
def donors : Finset ℕ := (Finset.range D.N).filter fun n => (D.link n).isSome

theorem card_linked (hv : D.Valid) :
    (D.allUses.filter fun u => D.linkedB u = true).card = D.donors.card := by
  symm
  apply Finset.card_bij (fun n _ => D.linkedOf n)
  · intro n hn
    simp only [donors, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hs⟩ := hn
    have hlu := D.linkUse_linkedOf hs
    refine Finset.mem_filter.mpr ⟨?_, (D.linkedB_iff _).mpr ⟨n, hnN, hlu⟩⟩
    obtain ⟨o, t, pos, hl, he⟩ := D.linkUse_eq.mp hlu
    rw [D.mem_allUses]
    obtain ⟨hnt, htN, -⟩ := hv.link_user n o t pos hl
    have hvn := (hv.link_donor n o t pos hl).1
    exact Or.inl ⟨t, pos, he, htN, by omega⟩
  · intro n hn n' hn' h
    simp only [donors, Finset.mem_filter, Finset.mem_range] at hn hn'
    have h1 := D.linkUse_linkedOf hn.2
    have h2 := D.linkUse_linkedOf hn'.2
    obtain ⟨o, t, pos, hl, he⟩ := D.linkUse_eq.mp h1
    obtain ⟨o', t', pos', hl', he'⟩ := D.linkUse_eq.mp h2
    rw [← h, he] at he'
    cases he'
    exact hv.link_inj _ _ _ _ _ _ hl hl'
  · intro u hu
    obtain ⟨-, hl⟩ := Finset.mem_filter.mp hu
    obtain ⟨n, hn, hlu⟩ := (D.linkedB_iff u).mp hl
    have hs : (D.link n).isSome := by
      unfold linkUse at hlu
      cases h : D.link n with
      | none => rw [h] at hlu; cases hlu
      | some _ => rfl
    refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hs⟩, ?_⟩
    rw [D.linkUse_linkedOf hs] at hlu
    exact Option.some.inj hlu

/-- **The slot count**: one slot per addition and root, less one per donor. -/
theorem compile_next (hv : D.Valid) :
    D.compile.next + D.donors.card = (D.N - D.v) + D.rootCount := by
  have h1 := D.compile_next_sum hv
  rw [D.sum_freeUses hv] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := D.allUses)
    (fun u => D.linkedB u = true)
  simp only [Bool.not_eq_true] at h2
  rw [D.card_allUses, D.card_linked hv] at h2
  have h3 := hv.v_le
  omega

end Dag

end IntegerMultBounds.MathlibTM2.M8.Local
