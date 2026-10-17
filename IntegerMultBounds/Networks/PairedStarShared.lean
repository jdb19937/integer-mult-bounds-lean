module

public import IntegerMultBounds.Networks.PairedStarNodes
public import IntegerMultBounds.Networks.SharedPointLocalFamily
public import IntegerMultBounds.Networks.DAGCompactSource

/-! The sharp fifty-copy count, from structure alone. Over the local circuit
less its 102 credited dead additions, each copy has at most 9,813 additions.
Every counted star is such an addition, and copies `c < c'` share the lifted
star of center `c' - 1` in copy `c` and center `c` in copy `c'`. The 40,256
counted shared stars are genuine duplicate witnesses, so at most 450,394
distinct supports remain, and the pruned circuit used by replay has no others.

Every argument is stated for an arbitrary local circuit with the needed
properties and specialized only at the end, so no concrete circuit is ever
compared by evaluation. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedStarShared

open DisjointCircuit DisjointBuilder PairedCircuit DisjointPruning DAGSupportTrace DAGAdditionIds
open PairedInitialGraph PairedStarCount PairedStarFamily PairedStarPresence PairedStarNodes
open SharedPointMatching

/-- The pair labels, typed at the local circuit's own coordinate type. -/
def e49 : Fin 1176 ↪ ℕ × ℕ := PairedIndexedPruning.pairEmbedding 49

theorem e49_apply (t : Fin 1176) : e49 t = PairMask.pairAt 49 t := rfl

/-! ### Coordinates -/

section Coordinates

variable (P : PairedLocalCircuit) (N : List (Node Input))

theorem map_getElem? (hmap : P.nodes.map (PairedRename.node e49) = N) (j : ℕ) :
    N[j]? = P.nodes[j]?.map (PairedRename.node e49) := by
  subst hmap; simp

theorem map_additionIds (hmap : P.nodes.map (PairedRename.node e49) = N) :
    additionIds P.nodes = additionIds N := by
  subst hmap
  ext i
  rw [mem_additionIds, mem_additionIds, List.getElem?_map]
  constructor
  · rintro ⟨n, hn, l, r, hk⟩
    exact ⟨_, by rw [hn]; rfl, l, r, by simp [PairedRename.node, PairedRename.kind, hk]⟩
  · rintro ⟨n, hn, l, r, hk⟩
    cases hi : P.nodes[i]? with
    | none => rw [hi] at hn; simp at hn
    | some m =>
      rw [hi] at hn
      have hn' := Option.some.inj hn
      subst hn'
      cases hm : m.kind with
      | input p => simp [PairedRename.node, PairedRename.kind, hm] at hk
      | add l' r' => exact ⟨m, rfl, l', r', hm⟩

theorem map_additionCount (hmap : P.nodes.map (PairedRename.node e49) = N) :
    DAGAllocator.additionCount P.nodes = DAGAllocator.additionCount N := by
  subst hmap; exact (PairedRename.additionCount_map e49 _).symm

theorem map_mark (hmap : P.nodes.map (PairedRename.node e49) = N) (roots : Finset ℕ) :
    mark P.nodes roots = mark N roots := by
  subst hmap; exact (PairedRename.mark_map e49 _ _).symm

end Coordinates

/-! ### The node of a counted star -/

section Star

variable (N : List (Node Input))

theorem star_nodup (v : ℕ) (xs : List ℕ) (hv : v ∉ xs) (hn : xs.Nodup) :
    (xs.map (fun x => (min v x, max v x))).Nodup := by
  apply hn.map_on
  intro x hx y hy he
  simp only [Prod.mk.injEq] at he
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  have hyv : y ≠ v := fun h => hv (h ▸ hy)
  omega

theorem star_card (v : ℕ) (xs : List ℕ) (hv : v ∉ xs) (hn : xs.Nodup) : (star v xs).card = xs.length := by
  unfold PairedStarFamily.star
  rw [List.toFinset_card_of_nodup (star_nodup v xs hv hn), List.length_map]

/-- A star determines its increasing leaf list. -/
theorem star_injective (v : ℕ) (xs ys : List ℕ) (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·))
    (hvx : v ∉ xs) (hvy : v ∉ ys) (he : star v xs = star v ys) : xs = ys := by
  have hmem : ∀ (zs : List ℕ), v ∉ zs → ∀ x, x ∈ zs ↔ x ≠ v ∧ (min v x, max v x) ∈ star v zs := by
    intro zs hvz x
    rw [mem_star]
    constructor
    · intro hxz
      exact ⟨fun h => hvz (h ▸ hxz), x, hxz, rfl⟩
    · rintro ⟨hxv, x', hx', hxe⟩
      have hx'v : x' ≠ v := fun h => hvz (h ▸ hx')
      simp only [Prod.mk.injEq] at hxe
      have : x = x' := by omega
      exact this ▸ hx'
  have hp : xs.Perm ys := by
    apply (List.perm_ext_iff_of_nodup (hx.imp (fun h => ne_of_lt h)) (hy.imp (fun h => ne_of_lt h))).mpr
    intro x
    rw [hmem xs hvx, hmem ys hvy, he]
  exact hp.eq_of_sortedLE (List.sortedLT_iff_pairwise.mpr hx).sortedLE
    (List.sortedLT_iff_pairwise.mpr hy).sortedLE

open Classical in
/-- The local node carrying a counted star. -/
noncomputable def idx (v : ℕ) (xs : List ℕ) : ℕ :=
  if h : ∃ j, ∃ hj : j < N.length, N[j].support = star v xs then Classical.choose h else 0

theorem idx_spec (v : ℕ) (xs : List ℕ) (h : star v xs ∈ N.map Node.support) :
    ∃ hj : idx N v xs < N.length, N[idx N v xs].support = star v xs := by
  have hex : ∃ j, ∃ hj : j < N.length, N[j].support = star v xs := by
    obtain ⟨n, hn, he⟩ := List.mem_map.mp h
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hn
    exact ⟨j, hj, he⟩
  simp only [idx, dite_eq_left_of_eq_true (eq_true hex)]
  exact Classical.choose_spec hex

theorem idx_get (v : ℕ) (xs : List ℕ) (h : star v xs ∈ N.map Node.support) :
    N[idx N v xs]?.map Node.support = some (star v xs) := by
  obtain ⟨hj, hs⟩ := idx_spec N v xs h
  rw [List.getElem?_eq_getElem hj, Option.map_some, hs]

theorem idx_addition (hvN : Valid N) (v : ℕ) (hv : v < 49) (xs : List ℕ) (hx : xs ∈ fam v)
    (h : star v xs ∈ N.map Node.support) : idx N v xs ∈ additionIds N := by
  obtain ⟨hj, hs⟩ := idx_spec N v xs h
  obtain ⟨hsort, hvx, -, h2, -⟩ := fam_shape' v hv xs hx
  have hcard : 2 ≤ N[idx N v xs].support.card := by
    rw [hs, star_card v xs hvx (hsort.imp (fun h => ne_of_lt h))]; exact h2
  have hnode := DAGValueTransfer.validFrom_get [] N hvN _ hj
  cases hkind : N[idx N v xs].kind with
  | input p =>
    have heq : N[idx N v xs].support = {p} := by simpa only [Node.Valid, hkind] using hnode
    rw [heq, Finset.card_singleton] at hcard
    omega
  | add l r => exact (mem_additionIds _ _).mpr ⟨_, List.getElem?_eq_getElem hj, l, r, hkind⟩

/-- Equal star nodes have equal leaf lists. -/
theorem idx_injective (v : ℕ) (hv : v < 49) (xs ys : List ℕ) (hx : xs ∈ fam v) (hy : ys ∈ fam v)
    (hsx : star v xs ∈ N.map Node.support) (hsy : star v ys ∈ N.map Node.support)
    (he : idx N v xs = idx N v ys) : xs = ys := by
  have h1 := idx_get N v xs hsx
  have h2 := idx_get N v ys hsy
  rw [he, h2] at h1
  obtain ⟨hxs, hvx, -⟩ := fam_shape' v hv xs hx
  obtain ⟨hys, hvy, -⟩ := fam_shape' v hv ys hy
  exact star_injective v xs ys hxs hys hvx hvy (Option.some.inj h1).symm

end Star

/-! ### Endpoint summaries of a star node -/

theorem star_endpoints (P : PairedLocalCircuit) (N : List (Node Input))
    (hmap : P.nodes.map (PairedRename.node e49) = N) (v : ℕ) (hv : v < 49) (xs : List ℕ)
    (hx : xs ∈ fam v) (j : ℕ) (hs : N[j]?.map Node.support = some (star v xs)) :
    P.endpointCore j = {⟨v, hv⟩} ∧
      P.endpointUnion j = insert ⟨v, hv⟩ (Finset.univ.filter (fun u : Fin 49 => u.val ∈ xs)) := by
  obtain ⟨hsort, hvx, hlt, h2, -⟩ := fam_shape' v hv xs hx
  rw [map_getElem? P N hmap, Option.map_map] at hs
  obtain ⟨n, hn, hns⟩ := Option.map_eq_some_iff.mp hs
  have hns' : n.support.map e49 = star v xs := hns
  have hsup : P.support j = n.support := by
    simp [PairedLocalCircuit.support, hn]
  have hmem : ∀ t, t ∈ P.support j ↔ PairMask.pairAt 49 t ∈ star v xs := by
    intro t
    rw [hsup, ← hns', ← e49_apply, Finset.mem_map' e49]
  have hpre : ∀ z ∈ star v xs, ∃ t : Fin (Nat.choose 49 2), t ∈ P.support j ∧ PairMask.pairAt 49 t = z := by
    intro z hz
    rw [← hns'] at hz
    obtain ⟨t, ht, he⟩ := Finset.mem_map.mp hz
    exact ⟨t, hsup ▸ ht, he⟩
  have hpay : ∀ (t : Fin (Nat.choose 49 2)) (u : Fin 49), u ∈ SharedPointLift.pairPayload 49 t ↔
      u.val = (PairMask.pairAt 49 t).1 ∨ u.val = (PairMask.pairAt 49 t).2 := by
    intro t u
    simp only [SharedPointLift.pairPayload, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
      SharedPointLift.pairLeft, SharedPointLift.pairRight]
  have hx0 : 0 < xs.length := by omega
  have hx1 : 1 < xs.length := by omega
  have hne : xs[0] ≠ xs[1] := fun h =>
    (List.pairwise_iff_getElem.mp hsort 0 1 hx0 hx1 (by omega)).ne h
  have hst : ∀ x ∈ xs, (min v x, max v x) ∈ star v xs := fun x hx => (mem_star v xs _).mpr ⟨x, hx, rfl⟩
  constructor
  · ext u
    simp only [PairedLocalCircuit.endpointCore, MaskSignature.core, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · intro hu
      obtain ⟨t0, ht0, he0⟩ := hpre _ (hst _ (List.getElem_mem hx0))
      obtain ⟨t1, ht1, he1⟩ := hpre _ (hst _ (List.getElem_mem hx1))
      have hu0 := (hpay t0 u).mp (hu t0 ht0)
      have hu1 := (hpay t1 u).mp (hu t1 ht1)
      rw [he0] at hu0
      rw [he1] at hu1
      apply Fin.ext
      simp only at hu0 hu1 ⊢
      omega
    · rintro rfl t ht
      obtain ⟨x, -, he⟩ := (mem_star v xs _).mp ((hmem t).mp ht)
      rw [hpay, he]
      simp only
      omega
  · have hunion : ∀ u, u ∈ P.endpointUnion j ↔ ∃ t : Fin (Nat.choose 49 2),
        t ∈ P.support j ∧ u ∈ SharedPointLift.pairPayload 49 t :=
      fun u => Finset.mem_biUnion
    ext u
    rw [hunion]
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, hu⟩
      obtain ⟨x, hxm, he⟩ := (mem_star v xs _).mp ((hmem t).mp ht)
      rw [hpay, he] at hu
      by_cases hvx' : v ≤ x
      · rw [min_eq_left hvx', max_eq_right hvx'] at hu
        rcases hu with hu | hu
        · left; exact Fin.ext hu
        · right; rw [hu]; exact hxm
      · rw [min_eq_right (by omega), max_eq_left (by omega)] at hu
        rcases hu with hu | hu
        · right; rw [hu]; exact hxm
        · left; exact Fin.ext hu
    · rintro (rfl | hu)
      · obtain ⟨t, ht, he⟩ := hpre _ (hst _ (List.getElem_mem hx0))
        refine ⟨t, ht, ?_⟩
        rw [hpay, he]
        simp only
        omega
      · obtain ⟨t, ht, he⟩ := hpre _ (hst _ hu)
        refine ⟨t, ht, ?_⟩
        rw [hpay, he]
        simp only
        omega

end IntegerMultBounds.Networks.PairedStarShared
