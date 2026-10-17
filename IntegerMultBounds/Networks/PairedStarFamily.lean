module

public import IntegerMultBounds.Networks.PairedStarMatch
public import IntegerMultBounds.Networks.PairedTopStars
public import IntegerMultBounds.Networks.PairedHubStars

/-! Every counted leaf list is the leaf set of a star the local constructor
stores: top strip values, prefixes, suffixes and omissions, right cross sums,
and at vertex `48` the coarse edges of every level and three base sums. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedStarFamily

open DisjointCircuit DisjointBuilder PairedCircuit PairedStarCount PairedStarPresence PairedTopStars
open PairedHubStars PairedTopPruning

/-- The star from `v` to the leaves `xs`, as a set of increasing input pairs. -/
def star (v : ℕ) (xs : List ℕ) : Finset (ℕ × ℕ) := (xs.map (fun x => (min v x, max v x))).toFinset

theorem mem_star (v : ℕ) (xs : List ℕ) (z : ℕ × ℕ) :
    z ∈ star v xs ↔ ∃ x ∈ xs, z = (min v x, max v x) := by
  simp only [star, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem mem_grp (j x : ℕ) (hj : j ≤ 24) : x ∈ grp j ↔ x ≤ 48 ∧ x / 2 = j := by
  simp only [grp]
  split_ifs <;> simp <;> omega

theorem mem_leavesOf (js : List ℕ) (hjs : ∀ j ∈ js, j ≤ 24) (x : ℕ) :
    x ∈ leavesOf js ↔ x ≤ 48 ∧ x / 2 ∈ js := by
  simp only [leavesOf, List.mem_flatMap]
  constructor
  · rintro ⟨j, hj, hx⟩
    have h := (mem_grp j x (hjs j hj)).mp hx
    exact ⟨h.1, h.2 ▸ hj⟩
  · rintro ⟨hx, hj⟩
    exact ⟨x / 2, hj, (mem_grp _ x (hjs _ hj)).mpr ⟨hx, rfl⟩⟩

theorem star_leaves (v : ℕ) (js : List ℕ) (hjs : ∀ j ∈ js, j ≤ 24) :
    star v (leavesOf js) = edgesAt 24 v js := by
  ext z
  rw [mem_star, mem_edgesAt]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := (mem_leavesOf js hjs x).mp hx
    exact ⟨x, by omega, h.2, rfl⟩
  · rintro ⟨x, hx, hj, rfl⟩
    exact ⟨x, (mem_leavesOf js hjs x).mpr ⟨by omega, hj⟩, rfl⟩

theorem star_hub (xs : List ℕ) (F : Finset ℕ) (h : ∀ x, x ∈ xs ↔ x ∈ F) : star 48 xs = star48 F := by
  ext z
  rw [mem_star]
  simp only [star48, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, (h x).mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, (h x).mpr hx, rfl⟩

theorem others_eq (i : ℕ) : others i = other 24 i := rfl

theorem mem_others (i j : ℕ) : j ∈ others i ↔ j ≤ 24 ∧ j ≠ i := by
  simp only [others, List.mem_filter, List.mem_range, bne_iff_ne]
  omega

theorem others_le (i : ℕ) (js : List ℕ) (hs : js.Sublist (others i)) : ∀ j ∈ js, j ≤ 24 :=
  fun j hj => ((mem_others i j).mp (hs.subset hj)).1

theorem leaves_nodup : ∀ i < 24, (leavesOf (others i)).Nodup := by decide +kernel

/-- Stated for a symbolic half-size, so no concrete circuit is compared by unfolding. -/
theorem stored_C (m : ℕ) (S : Finset (ℕ × ℕ)) (h : Stored (C m) S) :
    Stored (PairedInitialGraph.circuit (List.range (2 * m + 1))).nodes S := h

/-- Top-level facts transported to the 49-vertex circuit. -/
theorem stored_range (n : ℕ) (hn : 2 * 24 + 1 = n) (S : Finset (ℕ × ℕ)) (h : Stored (C 24) S) :
    Stored (PairedInitialGraph.circuit (List.range n)).nodes S := by
  subst hn; exact stored_C 24 S h

theorem fam_stored (v : ℕ) (hv : v < 49) (xs : List ℕ) (hx : xs ∈ fam v) :
    Stored (PairedInitialGraph.circuit (List.range 49)).nodes (star v xs) := by
  unfold fam at hx
  split_ifs at hx with h48
  · subst h48
    have hub := hub_49
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with ((((⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | rfl | rfl | rfl)
    · rw [star_hub _ (F1 j) (fun x => by rw [mem_grp j x (by omega), F1_spec j (by omega)]; omega)]
      exact hub.1 j hj
    · rw [star_hub _ (F2 k) (fun x => by
        simp only [PairedStarCount.block, List.mem_range'_1]; rw [ F2_spec k (by omega)]; omega)]
      exact hub.2.1 k hk
    · rw [star_hub _ (F3 k) (fun x => by
        simp only [PairedStarCount.block, List.mem_range'_1]; rw [ F3_spec k (by omega)]; omega)]
      exact hub.2.2.1 k hk
    · rw [star_hub _ (PairedBasePruning.F4 k) (fun x => by
        simp only [PairedStarCount.block, List.mem_range'_1]; rw [ F4_spec' k (by omega)]; omega)]
      exact hub.2.2.2.1 k hk
    · rw [star_hub _ (PairedBasePruning.F4 0 ∪ PairedBasePruning.F4 2) (fun x => by
        simp only [Finset.mem_union, List.mem_append, PairedStarCount.block, List.mem_range'_1]; rw [
          F4_spec' 0 (by omega), F4_spec' 2 (by omega)]; omega)]
      exact hub.2.2.2.2.2.1
    · rw [star_hub _ (PairedBasePruning.F4 0 ∪ PairedBasePruning.F4 1) (fun x => by
        rw [Finset.mem_union, List.mem_range, F4_spec' 0 (by omega), F4_spec' 1 (by omega)]; omega)]
      exact hub.2.2.2.2.1
    · rw [star_hub _ (PairedBasePruning.F4 1 ∪ PairedBasePruning.F4 2) (fun x => by
        rw [Finset.mem_union, List.mem_range'_1, F4_spec' 1 (by omega), F4_spec' 2 (by omega)]; omega)]
      exact hub.2.2.2.2.2.2
  · apply stored_range 49 rfl
    let i := v / 2
    have hi : i < 24 := by omega
    let b := if v = 2 * i then 2 * i + 1 else 2 * i
    have hb : b = 2 * i ∨ b = 2 * i + 1 := by simp only [b]; split_ifs <;> omega
    have hpv : partner i b = v := by simp only [partner, b]; split_ifs <;> omega
    have ht := top_stars 24 (by decide) i b hi hb
    rw [hpv] at ht
    have hlen : (other 24 i).length = 24 := other_length 24 i (by omega)
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_range', List.mem_filter,
      decide_eq_true_eq] at hx
    rcases hx with ((⟨j, ⟨hj, hj24⟩, rfl⟩ | ⟨s, ⟨hs1, hs2⟩, rfl⟩) |
      ((⟨s, ⟨hs1, hs2⟩, rfl⟩ | ⟨t, ht', rfl⟩) | ⟨a, ha, rfl⟩))
    · have hgrp : grp j = leavesOf [j] := by simp [leavesOf]
      rw [hgrp, star_leaves v [j] (by simp; omega)]
      rw [others_eq] at hj
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hj
      exact ht.2.2.2 k hk
    · rw [star_leaves v _ (others_le i _ (List.take_sublist _ _)), others_eq]
      exact ht.1 s (by omega) (by omega)
    · rw [star_leaves v _ (others_le i _ (List.drop_sublist _ _)), others_eq]
      exact ht.2.1 s (by omega) (by omega)
    · rw [star_leaves v _ (others_le i _ (List.eraseIdx_sublist _ _)), others_eq]
      exact ht.2.2.1 t (by omega)
    · have hg : a / 2 ∈ other 24 i := by
        rw [← others_eq, mem_others]; omega
      obtain ⟨k, hk, hkg⟩ := List.mem_iff_getElem.mp hg
      have ha' : a = 2 * (a / 2) ∨ a = 2 * (a / 2) + 1 := by omega
      have hc := cross_stored 24 (by decide) (a / 2) i (by omega) hi a b ha' hb k hk hkg
      have hnd : (other 24 i).Nodup := List.nodup_range.filter _
      have herase : (other 24 i).eraseIdx k = (other 24 i).erase (a / 2) := by
        rw [← hkg, hnd.erase_getElem]
      have hpa := partner_facts (a / 2) a ha'
      convert hc using 1
      ext z
      rw [mem_star, Finset.mem_union, mem_edgesAt, Finset.mem_singleton, herase, hpv]
      have hl := leaves_nodup i hi
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hl.mem_erase_iff, mem_leavesOf _ (others_le i _ (List.Sublist.refl _)), mem_others] at hx
        by_cases hxg : x / 2 = a / 2
        · right
          have : x = partner (a / 2) a := by simp only [partner]; split_ifs <;> omega
          rw [this, min_comm, max_comm]
        · left
          refine ⟨x, by omega, ?_, rfl⟩
          rw [hnd.mem_erase_iff, ← others_eq, mem_others]
          omega
      · rintro (⟨x, hx, hxs, rfl⟩ | rfl)
        · rw [hnd.mem_erase_iff, ← others_eq, mem_others] at hxs
          refine ⟨x, ?_, rfl⟩
          rw [hl.mem_erase_iff, mem_leavesOf _ (others_le i _ (List.Sublist.refl _)), mem_others]
          omega
        · refine ⟨partner (a / 2) a, ?_, by rw [min_comm, max_comm]⟩
          rw [hl.mem_erase_iff, mem_leavesOf _ (others_le i _ (List.Sublist.refl _)), mem_others]
          simp only [partner] at hpa ⊢
          split_ifs at hpa ⊢ <;> omega

end IntegerMultBounds.Networks.PairedStarFamily
