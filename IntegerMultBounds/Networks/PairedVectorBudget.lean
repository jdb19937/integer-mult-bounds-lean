module

public import IntegerMultBounds.Networks.DisjointSharingBudget
public import IntegerMultBounds.Networks.PairedVectorCorrect

/-! Structural sharing bounds for the actual prefix/suffix vector constructor.
The full total built by the prefix pass is already interned when the suffix
pass reaches it. No generated circuit or concrete graph size is used. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedVectorBudget

open DisjointCircuit DisjointBuilder DisjointUnique DisjointExclusion
open PairedCircuit PairedVectorCorrect DAGAllocator DisjointSharingBudget

variable {ι : Type*} [DecidableEq ι]

/-- Reusing a stored union is free, including either zero-elision branch. -/
theorem smartAdd_additions_of_union_mem (nodes : List (Node ι)) (l r : Ref)
    (hm : refSupport nodes l ∪ refSupport nodes r ∈ nodes.map Node.support) :
    additionCount (smartAdd nodes l r).1 = additionCount nodes := by
  cases l with
  | none => simp [smartAdd]
  | some l =>
    cases r with
    | none => simp [smartAdd]
    | some r => exact smartAdd_reuses nodes l r hm

/-- Reusing a union leaves the actual node list unchanged, not merely its
addition count. This lets pruning proofs discard the unused lookup operands. -/
theorem smartAdd_nodes_of_union_mem (nodes : List (Node ι)) (l r : Ref)
    (hm : refSupport nodes l ∪ refSupport nodes r ∈ nodes.map Node.support) :
    (smartAdd nodes l r).1 = nodes := by
  cases l with
  | none => rfl
  | some l =>
    cases r with
    | none => rfl
    | some r =>
      simp only [smartAdd]
      unfold intern
      split
      · rfl
      · rename_i hn
        exact False.elim ((findSupport_none_iff _ _).mp hn hm)

omit [DecidableEq ι] in
/-- A valid stored reference's support occurs in the support bank. -/
theorem refSupport_mem (nodes : List (Node ι)) (i : ℕ) (hi : RefValid nodes (some i)) :
    refSupport nodes (some i) ∈ nodes.map Node.support := by
  rw [refSupport_some nodes i hi]
  exact List.mem_map.mpr ⟨nodes[i], List.getElem_mem hi, rfl⟩

/-- A present valid reference has nonempty support; an empty support must be zero. -/
theorem ref_eq_none_of_support_empty (nodes : List (Node ι)) (r : Ref)
    (hv : Valid nodes) (hr : RefValid nodes r) (he : refSupport nodes r = ∅) : r = none := by
  cases r with
  | none => rfl
  | some i =>
    have hn := refSupport_nonempty nodes (valid_nonempty nodes hv) i hr
    rw [he] at hn
    exact False.elim (Finset.not_nonempty_empty hn)

/-- The final backwards addition only looks up the prefix pass's stored
union. It emits no node pointing to the otherwise unused strict suffix. -/
theorem suffixBuild_cons_nodes_of_stored (nodes : List (Node ι)) (r : Ref) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes (r :: refs)) (hd : DisjointRefs nodes (r :: refs))
    (hm : supports nodes (r :: refs) ∈ nodes.map Node.support) :
    (suffixBuild nodes (r :: refs)).1 = (suffixBuild nodes refs).1 := by
  have hrs : RefsValid nodes refs := fun x hx => hr x (by simp [hx])
  have ht := suffixes_built nodes refs hv hrs (List.pairwise_cons.mp hd).2
  have hu : refSupport (suffixBuild nodes refs).1 r ∪
      refSupport (suffixBuild nodes refs).1 ((suffixBuild nodes refs).2.headD none) =
      supports nodes (r :: refs) := by
    simp only [suffixBuild_eq, List.headD_cons]
    rw [refSupport_extends ht.built.extension (hr r (by simp)), ht.built.support_eq]
    rfl
  simp only [suffixBuild]
  apply smartAdd_nodes_of_union_mem
  rw [hu]
  have he : Extends nodes (suffixBuild nodes refs).1 := by
    simpa only [suffixBuild_eq] using ht.built.extension
  obtain ⟨tail, htail⟩ := he
  rw [htail, List.map_append]
  exact List.mem_append_left _ hm

/-- Once the full union is stored, the backwards pass needs at most k minus
two additions for k at least two present operands. Its final union is reused. -/
theorem suffixBuild_additions_le_stored (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (hm : supports nodes refs ∈ nodes.map Node.support) (hk : 2 ≤ presentCount refs) :
    additionCount (suffixBuild nodes refs).1 ≤
      additionCount nodes + (presentCount refs - 2) := by
  induction refs generalizing nodes with
  | nil => simp [presentCount] at hk
  | cons r rs ih =>
    have hrs : RefsValid nodes rs := fun x hx => hr x (by simp [hx])
    have hds := (List.pairwise_cons.mp hd).2
    cases r with
    | none =>
      have hm' : supports nodes rs ∈ nodes.map Node.support := by
        simpa [supports, refSupport] using hm
      have hk' : 2 ≤ presentCount rs := by simpa [presentCount] using hk
      simpa [suffixBuild, smartAdd, presentCount] using ih nodes hv hrs hds hm' hk'
    | some i =>
      rw [suffixBuild_cons_nodes_of_stored nodes (some i) rs hv hr hd hm]
      have hb := suffixBuild_additions_le_present nodes rs
      simp only [presentCount, List.countP_cons, Option.isSome_some, ite_true] at hk ⊢
      unfold presentCount at hb
      omega

/-- The prefix pass stores the full total whenever a present operand exists. -/
theorem prefix_total_mem (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (hk : 0 < presentCount refs) :
    supports nodes refs ∈ (prefixBuild nodes none refs).1.map Node.support := by
  have hp := prefixBuild_built nodes none refs hv trivial hr
    (List.pairwise_cons.mpr ⟨by simp [refSupport], hd⟩)
  have hpres := prefixBuild_presence nodes none refs
  have hs : refSupport (prefixBuild nodes none refs).1
      ((prefixBuild nodes none refs).2.getLast?.getD none) = supports nodes refs := by
    have hh := congrArg (fun xs : List (Finset ι) => xs.getLast?.getD ∅) hp.supports_eq
    rw [List.getLast?_map, beforeSupports_last] at hh
    cases he : (prefixBuild nodes none refs).2.getLast? with
    | none => simpa [he, refSupport] using hh
    | some r => simpa [he, refSupport] using hh
  have hvlast : RefValid (prefixBuild nodes none refs).1
      ((prefixBuild nodes none refs).2.getLast?.getD none) := by
    cases he : (prefixBuild nodes none refs).2.getLast? with
    | none => trivial
    | some r => exact hp.refs_valid r (List.mem_of_getLast? he)
  cases he : (prefixBuild nodes none refs).2.getLast?.getD none with
  | none => simp [he] at hpres; omega
  | some i =>
    rw [← hs, he]
    exact refSupport_mem _ i (he ▸ hvlast)

/-- Prefix and suffix construction together need at most two k minus three
additions for k at least two present operands, including arbitrary zero slots. -/
theorem prefix_suffix_additions_le (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (hk : 2 ≤ presentCount refs) :
    additionCount (suffixBuild (prefixBuild nodes none refs).1 refs).1 ≤
      additionCount nodes + (2 * presentCount refs - 3) := by
  have hp := prefixBuild_built nodes none refs hv trivial hr
    (List.pairwise_cons.mpr ⟨by simp [refSupport], hd⟩)
  have hm := prefix_total_mem nodes refs hv hr hd (by omega)
  rw [← supports_extends hp.extension refs hr] at hm
  have hs := suffixBuild_additions_le_stored (prefixBuild nodes none refs).1 refs hp.valid
    (refsValid_extends hp.extension hr) (disjointRefs_extends hp.extension refs hr hd) hm hk
  have hb := prefixBuild_additions_le_present nodes refs
  omega

private theorem supports_eq_empty_of_presentCount_zero (nodes : List (Node ι)) (refs : List Ref)
    (hz : presentCount refs = 0) : supports nodes refs = ∅ := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | none => simpa [supports, refSupport] using ih (by simpa [presentCount] using hz)
    | some i => simp [presentCount] at hz

private theorem prefixBuild_additions_le_zero_tail (nodes : List (Node ι)) (acc : Ref)
    (refs : List Ref) (hz : presentCount refs = 0) :
    additionCount (prefixBuild nodes acc refs).1 ≤ additionCount nodes := by
  have hp := prefixBuild_present_le nodes acc refs
  rw [prefixBuild_presence, hz] at hp
  cases acc <;> simp_all

/-- A prefix pass whose full union was already stored saves its final addition.
This extra saving is needed when pruning a vector total that aliases old work:
the same node must never be charged once for reuse and again for pruning. -/
theorem prefixBuild_additions_le_stored (nodes : List (Node ι)) (acc : Ref) (refs : List Ref)
    (hv : Valid nodes) (ha : RefValid nodes acc) (hr : RefsValid nodes refs)
    (hd : DisjointRefs nodes (acc :: refs))
    (hm : refSupport nodes acc ∪ supports nodes refs ∈ nodes.map Node.support)
    (hk : 2 ≤ acc.isSome.toNat + presentCount refs) :
    additionCount (prefixBuild nodes acc refs).1 ≤
      additionCount nodes + (acc.isSome.toNat + presentCount refs - 2) := by
  induction refs generalizing nodes acc with
  | nil => cases acc <;> simp [presentCount] at hk
  | cons r rs ih =>
    have hrs : RefsValid nodes rs := fun x hx => hr x (by simp [hx])
    have hdp := List.pairwise_cons.mp hd
    have hdr := List.pairwise_cons.mp hdp.2
    cases acc with
    | none =>
      cases r with
      | none =>
        have hnew : DisjointRefs nodes (none :: rs) :=
          List.pairwise_cons.mpr ⟨by simp [refSupport], hdr.2⟩
        simpa [prefixBuild, smartAdd, presentCount] using
          ih nodes none hv trivial hrs hnew (by simpa [supports, refSupport] using hm)
            (by
              simp only [presentCount, List.countP_cons, Option.isSome_none,
                Bool.toNat_false, Bool.false_eq_true, ite_false] at hk ⊢
              omega)
      | some i =>
        have hk' : 2 ≤ (some i : Ref).isSome.toNat + presentCount rs := by
          simp only [presentCount, List.countP_cons, Option.isSome_none, Option.isSome_some,
            Bool.toNat_false, Bool.toNat_true, ite_true] at hk ⊢
          omega
        have ht := ih nodes (some i) hv (hr _ (by simp)) hrs hdp.2
          (by simpa [supports, refSupport] using hm) hk'
        change additionCount (prefixBuild nodes (some i) rs).1 ≤ _
        simp only [presentCount, List.countP_cons, Option.isSome_none, Option.isSome_some,
          Bool.toNat_false, Bool.toNat_true, ite_true] at ht ⊢
        omega
    | some a =>
      cases r with
      | none =>
        have hnew : DisjointRefs nodes (some a :: rs) := List.pairwise_cons.mpr
          ⟨fun x hx => hdp.1 x (by simp [hx]), hdr.2⟩
        simpa [prefixBuild, smartAdd, presentCount] using
          ih nodes (some a) hv ha hrs hnew (by simpa [supports, refSupport] using hm)
            (by
              simp only [presentCount, List.countP_cons, Option.isSome_none, Option.isSome_some,
                Bool.toNat_true, Bool.false_eq_true, ite_false] at hk ⊢
              omega)
      | some r =>
        let next := smartAdd nodes (some a) (some r)
        have hs := smartAdd_built nodes (some a) (some r) hv ha (hr _ (by simp))
          (hdp.1 _ (by simp))
        have hnew : DisjointRefs next.1 (next.2 :: rs) := by
          apply List.pairwise_cons.mpr
          refine ⟨?_, disjointRefs_extends hs.extension rs hrs hdr.2⟩
          intro x hx
          rw [hs.support_eq, refSupport_extends hs.extension (hrs x hx)]
          exact Finset.disjoint_union_left.mpr ⟨hdp.1 x (by simp [hx]), hdr.1 x hx⟩
        have hnext : next.2.isSome.toNat = 1 := by simp [next, smartAdd]
        by_cases hz : presentCount rs = 0
        · have hempty := supports_eq_empty_of_presentCount_zero nodes rs hz
          have hfree := smartAdd_additions_of_union_mem nodes (some a) (some r)
            (by simpa [supports, hempty] using hm)
          have ht := prefixBuild_additions_le_zero_tail next.1 next.2 rs hz
          change additionCount (prefixBuild next.1 next.2 rs).1 ≤ _
          change additionCount next.1 = additionCount nodes at hfree
          rw [hfree] at ht
          simp only [presentCount, List.countP_cons, Option.isSome_some, Bool.toNat_true, ite_true] at hz ⊢
          omega
        · have hmem : refSupport next.1 next.2 ∪ supports next.1 rs ∈ next.1.map Node.support := by
            rw [hs.support_eq, supports_extends hs.extension rs hrs, Finset.union_assoc]
            obtain ⟨tail, he⟩ := hs.extension
            rw [he, List.map_append]
            exact List.mem_append_left _ hm
          have ht := ih next.1 next.2 hs.valid hs.refValid
            (refsValid_extends hs.extension hrs) hnew hmem (by rw [hnext]; omega)
          have hcost := PairedCircuitBudget.smartAdd_additions_le nodes (some a) (some r)
          rw [hnext] at ht
          change additionCount (prefixBuild next.1 next.2 rs).1 ≤ _
          change additionCount next.1 ≤ _ at hcost
          simp only [presentCount, List.countP_cons, Option.isSome_some, Bool.toNat_true, ite_true]
          unfold presentCount at ht hz
          omega

theorem addPairs_additions_le_last (nodes : List (Node ι)) (ps : List (Ref × Ref))
    (hlast : (ps.getLast?.getD (none, none)).2 = none) :
    additionCount (mapBuild (fun ns p => smartAdd ns p.1 p.2) nodes ps).1 ≤
      additionCount nodes + (ps.length - 1) := by
  induction ps generalizing nodes with
  | nil => simp [mapBuild]
  | cons p ps ih =>
    cases ps with
    | nil =>
      have hp : p.2 = none := by simpa using hlast
      cases h : p.1 <;> simp [mapBuild, hp, h, smartAdd]
    | cons q qs =>
      have ht := ih (smartAdd nodes p.1 p.2).1 (by simpa using hlast)
      have hs := PairedCircuitBudget.smartAdd_additions_le nodes p.1 p.2
      simp only [mapBuild, List.length_cons] at ht ⊢
      omega

/-- The two endpoint omissions each have a zero operand and allocate nothing. -/
theorem addPairs_additions_le_endpoints (nodes : List (Node ι)) (ps : List (Ref × Ref))
    (hfirst : (ps.headD (none, none)).1 = none)
    (hlast : (ps.getLast?.getD (none, none)).2 = none) :
    additionCount (mapBuild (fun ns p => smartAdd ns p.1 p.2) nodes ps).1 ≤
      additionCount nodes + (ps.length - 2) := by
  cases ps with
  | nil => simp [mapBuild]
  | cons p ps =>
    have hp : p.1 = none := by simpa using hfirst
    cases ps with
    | nil => simp [mapBuild, hp, smartAdd]
    | cons q qs =>
      have ht := addPairs_additions_le_last nodes (q :: qs) (by simpa using hlast)
      simpa [mapBuild, hp, smartAdd] using ht

theorem suffixBuild_last (nodes : List (Node ι)) (refs : List Ref) :
    (suffixBuild nodes refs).2.getLast? = some none := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    have hn : (suffixBuild nodes rs).2 ≠ [] := by
      intro he
      have := suffixBuild_length nodes rs
      simp [he] at this
    simpa only [suffixBuild, List.getLast?_cons_of_ne_nil hn] using ih

theorem prefixBuild_head (nodes : List (Node ι)) (acc : Ref) (refs : List Ref) :
    (prefixBuild nodes acc refs).2.headD none = acc := by
  cases refs <;> rfl

/-- The omission pass needs at most length minus two additions. This bound is
independent of supports, input zeros, and previous support interning. -/
theorem vector_omissions_additions_le (nodes : List (Node ι)) (refs : List Ref) :
    let pre := prefixBuild nodes none refs
    let suf := suffixBuild pre.1 refs
    additionCount (mapBuild (fun ns p => smartAdd ns p.1 p.2) suf.1
      (pre.2.zip suf.2.tail)).1 ≤ additionCount suf.1 + (refs.length - 2) := by
  dsimp only
  apply (addPairs_additions_le_endpoints _ _ ?_ ?_).trans
  · simp only [List.length_zip, prefixBuild_length, List.length_tail, suffixBuild_length]
    omega
  · have hhead := prefixBuild_head nodes none refs
    cases hx : (prefixBuild nodes none refs).2 with
    | nil => simp
    | cons x xs =>
      have hx0 : x = none := by simpa [hx] using hhead
      cases hy : (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail <;> simp [hx0]
  · have hmap : (((prefixBuild nodes none refs).2.zip
        (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail).map Prod.snd) =
        (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail := by
      apply List.map_snd_zip
      simp only [List.length_tail, suffixBuild_length, prefixBuild_length]
      omega
    have hh := congrArg (fun xs : List Ref => xs.getLast?.getD none) hmap
    rw [List.getLast?_map] at hh
    have hend : (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail.getLast?.getD none = none := by
      cases refs with
      | nil => rfl
      | cons r rs => simp only [suffixBuild, List.tail_cons, suffixBuild_last, Option.getD_some]
    rw [hend] at hh
    cases he : ((prefixBuild nodes none refs).2.zip
        (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail).getLast? <;>
      simp_all

/-- Sharp three-pass allocation bound for vectors whose operands are all
present. The prefix, suffix, and omission passes cost at most k-1, k-2, and k-2. -/
theorem vectorFalse_additions_le_sharp (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (hall : ∀ r ∈ refs, r.isSome = true) (hk : 2 ≤ refs.length) :
    additionCount (vectorFalse nodes refs).nodes ≤ additionCount nodes + (3 * refs.length - 5) := by
  have hcount : presentCount refs = refs.length := by
    unfold presentCount
    exact List.countP_eq_length.mpr hall
  have hp := prefix_suffix_additions_le nodes refs hv hr hd (by omega)
  have ho := vector_omissions_additions_le nodes refs
  change additionCount (mapBuild _ _ _).1 ≤ _
  dsimp only at ho
  rw [hcount] at hp
  omega

/-- If an older stage already stored the total, prefix reuse replaces the
pruning credit: the vector allocates at most three k minus six additions.
This bound is safe to compose with savings already claimed for older nodes. -/
theorem vectorFalse_additions_le_stored (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (hall : ∀ r ∈ refs, r.isSome = true) (hk : 2 ≤ refs.length)
    (hm : supports nodes refs ∈ nodes.map Node.support) :
    additionCount (vectorFalse nodes refs).nodes ≤ additionCount nodes + (3 * refs.length - 6) := by
  have hcount : presentCount refs = refs.length := List.countP_eq_length.mpr hall
  have hp := prefixBuild_built nodes none refs hv trivial hr
    (List.pairwise_cons.mpr ⟨by simp [refSupport], hd⟩)
  have hb := prefixBuild_additions_le_stored nodes none refs hv trivial hr
    (List.pairwise_cons.mpr ⟨by simp [refSupport], hd⟩)
    (by simpa [refSupport] using hm) (by simpa only [Option.isSome_none,
      Bool.toNat_false, Nat.zero_add, hcount] using hk)
  have hmem := prefix_total_mem nodes refs hv hr hd (by omega)
  rw [← supports_extends hp.extension refs hr] at hmem
  have hs := suffixBuild_additions_le_stored (prefixBuild nodes none refs).1 refs hp.valid
    (refsValid_extends hp.extension hr) (disjointRefs_extends hp.extension refs hr hd)
    hmem (by omega)
  have ho := vector_omissions_additions_le nodes refs
  simp only [Option.isSome_none, Bool.toNat_false, Nat.zero_add, hcount] at hb hs
  dsimp only at ho
  change additionCount (mapBuild _ _ _).1 ≤ _
  omega

/-- A leading zero is free in all three passes. In particular, unweighted
strips use exactly the same allocation bound as their present tail. -/
theorem vectorFalse_cons_none_nodes (nodes : List (Node ι)) (refs : List Ref) :
    (vectorFalse nodes (none :: refs)).nodes = (vectorFalse nodes refs).nodes := by
  have hn : (suffixBuild (prefixBuild nodes none refs).1 refs).2 ≠ [] := by
    intro he
    have := suffixBuild_length (prefixBuild nodes none refs).1 refs
    simp [he] at this
  simp only [vectorFalse, prefixBuild, smartAdd, suffixBuild]
  cases hs : suffixBuild (prefixBuild nodes none refs).1 refs with
  | mk ns ss =>
    cases ss with
    | nil => simp [hs] at hn
    | cons r rs => rfl

/-- Unweighted strips have an absent carry followed by present cross-group
values. The leading zero does not change the sharp allocation bound. -/
theorem vectorFalse_cons_none_additions_le_sharp (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (hall : ∀ r ∈ refs, r.isSome = true) (hk : 2 ≤ refs.length) :
    additionCount (vectorFalse nodes (none :: refs)).nodes ≤
      additionCount nodes + (3 * refs.length - 5) := by
  rw [vectorFalse_cons_none_nodes]
  exact vectorFalse_additions_le_sharp nodes refs hv hr hd hall hk

/-- Expose the actual operands used after a strip discards its carry omission.
The full suffix lookup emits no node, and the remaining omission loop uses
only strict suffixes. The suffix total is not an operand of that loop. -/
theorem vectorFalse_cons_tail_nodes (nodes : List (Node ι)) (carry : Ref) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes (carry :: refs))
    (hd : DisjointRefs nodes (carry :: refs))
    (hk : 0 < presentCount (carry :: refs)) :
    (vectorFalse nodes (carry :: refs)).nodes =
      (mapBuild (fun ns p => smartAdd ns p.1 p.2)
        (suffixBuild (prefixBuild nodes carry refs).1 refs).1
        ((prefixBuild nodes carry refs).2.zip
          (suffixBuild (prefixBuild nodes carry refs).1 refs).2.tail)).1 := by
  let pre := prefixBuild nodes carry refs
  have hpre : prefixBuild nodes none (carry :: refs) = (pre.1, none :: pre.2) := rfl
  have hp := prefixBuild_built nodes none (carry :: refs) hv trivial hr
    (List.pairwise_cons.mpr ⟨by simp [refSupport], hd⟩)
  have hm := prefix_total_mem nodes (carry :: refs) hv hr hd hk
  rw [← supports_extends hp.extension (carry :: refs) hr] at hm
  have hfree := suffixBuild_cons_nodes_of_stored (prefixBuild nodes none (carry :: refs)).1
    carry refs hp.valid (refsValid_extends hp.extension hr)
    (disjointRefs_extends hp.extension _ hr hd) hm
  rw [hpre] at hfree
  dsimp only at hfree
  simp only [suffixBuild] at hfree
  rw [vectorFalse, hpre]
  simp only [suffixBuild]
  rw [hfree]
  have hn : (suffixBuild pre.1 refs).2 ≠ [] := by
    intro he
    have := suffixBuild_length pre.1 refs
    simp [he] at this
  cases hs : (suffixBuild pre.1 refs).2 with
  | nil => simp [hs] at hn
  | cons r rs => rfl

private theorem prefixBuild_replicate_none (nodes : List (Node ι)) (n : ℕ) :
    prefixBuild nodes none (List.replicate n none) = (nodes, List.replicate (n+1) none) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, prefixBuild, smartAdd, ih]

private theorem suffixBuild_replicate_none (nodes : List (Node ι)) (n : ℕ) :
    suffixBuild nodes (List.replicate n none) = (nodes, List.replicate (n+1) none) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, suffixBuild, smartAdd, ih]

/-- Empty singleton-group strips allocate nothing, even with arbitrarily many
zero slots. They need no small-size certificate or validity assumption. -/
theorem vectorFalse_replicate_none_nodes (nodes : List (Node ι)) (n : ℕ) :
    (vectorFalse nodes (List.replicate n none)).nodes = nodes := by
  simp only [vectorFalse, prefixBuild_replicate_none, suffixBuild_replicate_none]
  have hm : ∀ n, (mapBuild (fun ns (p : Ref × Ref) => smartAdd ns p.1 p.2) nodes
      (List.replicate n (none, none))).1 = nodes := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ, mapBuild, smartAdd] using ih
  simpa using hm n

omit [DecidableEq ι] in
private theorem zip_last_snd {α β : Type*} (xs : List α) (ys : List β) (h : ys.length ≤ xs.length) :
    (xs.zip ys).getLast?.map Prod.snd = ys.getLast? := by
  rw [← List.getLast?_map, List.map_snd_zip h]

/-- The strip vector's omission pass: its final pair always has a zero suffix. -/
private theorem tail_pairs_last (nodes : List (Node ι)) (carry : Ref) (values : List Ref)
    (hk : 0 < values.length) :
    let pre := prefixBuild nodes none (carry :: values)
    let suf := suffixBuild pre.1 values.tail
    (((pre.2.drop 1).zip (suf.2.take values.length)).getLast?.getD (none, none)).2 = none := by
  intro pre suf
  have hlen : suf.2.length = values.length := by
    simp only [suf, suffixBuild_length, List.length_tail]; omega
  have htake : suf.2.take values.length = suf.2 := List.take_of_length_le (by omega)
  have hz := zip_last_snd (pre.2.drop 1) (suf.2.take values.length) (by
    simp only [pre, List.length_take, List.length_drop, prefixBuild_length, List.length_cons]; omega)
  rw [htake, suffixBuild_last] at hz
  rw [htake]
  cases he : ((pre.2.drop 1).zip suf.2).getLast? with
  | none => rfl
  | some p =>
    rw [he] at hz
    simp only [Option.map_some, Option.some.injEq] at hz
    simp [hz]

theorem tail_pairs_length (nodes : List (Node ι)) (carry : Ref) (values : List Ref) :
    let pre := prefixBuild nodes none (carry :: values)
    let suf := suffixBuild pre.1 values.tail
    ((pre.2.drop 1).zip (suf.2.take values.length)).length = values.length := by
  intro pre suf
  simp only [pre, suf, List.length_zip, List.length_drop, prefixBuild_length, List.length_take,
    suffixBuild_length, List.length_tail, List.length_cons]
  omega

/-- With every operand present, the strip vector allocates at most 3k minus 6
nodes for k operands: no support sharing is needed, since the carry's omission
and its strict suffix total are never built. -/
theorem vectorTail_additions_le_sharp (nodes : List (Node ι)) (refs : List Ref)
    (hall : ∀ r ∈ refs, r.isSome = true) (hk : 3 ≤ refs.length) :
    additionCount (vectorTail nodes refs).nodes ≤ additionCount nodes + (3 * refs.length - 6) := by
  cases refs with
  | nil => simp at hk
  | cons carry values =>
    have hcount : presentCount (carry :: values) = values.length + 1 := by
      unfold presentCount
      rw [List.countP_eq_length.mpr hall, List.length_cons]
    have htail : presentCount values.tail ≤ values.tail.length := List.countP_le_length
    have hp := prefixBuild_additions_le_present nodes (carry :: values)
    have hs := suffixBuild_additions_le_present (prefixBuild nodes none (carry :: values)).1 values.tail
    have ho := addPairs_additions_le_last
      (suffixBuild (prefixBuild nodes none (carry :: values)).1 values.tail).1 _
      (tail_pairs_last nodes carry values (by simp at hk; omega))
    rw [tail_pairs_length] at ho
    have hlen : values.tail.length = values.length - 1 := List.length_tail
    simp only [List.length_cons] at hk ⊢
    change additionCount (mapBuild _ _ _).1 ≤ _
    rw [hcount] at hp
    omega

/-- An absent carry is free: the strip vector then costs at most 3m minus 5
for m present cross-group values. -/
theorem vectorTail_cons_none_additions_le_sharp (nodes : List (Node ι)) (values : List Ref)
    (hall : ∀ r ∈ values, r.isSome = true) (hk : 2 ≤ values.length) :
    additionCount (vectorTail nodes (none :: values)).nodes ≤
      additionCount nodes + (3 * values.length - 5) := by
  have hcount : presentCount (none :: values) = values.length := by
    unfold presentCount
    rw [List.countP_cons, List.countP_eq_length.mpr hall]
    simp
  have htail : presentCount values.tail ≤ values.tail.length := List.countP_le_length
  have hp := prefixBuild_additions_le_present nodes (none :: values)
  have hs := suffixBuild_additions_le_present (prefixBuild nodes none (none :: values)).1 values.tail
  have hfirst : ((((prefixBuild nodes none (none :: values)).2.drop 1).zip
      ((suffixBuild (prefixBuild nodes none (none :: values)).1 values.tail).2.take
        values.length)).headD (none, none)).1 = none := by
    have hpre : (prefixBuild nodes none (none :: values)).2.drop 1 =
        (prefixBuild nodes none values).2 := rfl
    rw [hpre]
    have hh := prefixBuild_head nodes none values
    cases hx : (prefixBuild nodes none values).2 with
    | nil => simp
    | cons x xs =>
      rw [hx] at hh
      cases (suffixBuild (prefixBuild nodes none (none :: values)).1 values.tail).2.take
        values.length <;> simp_all
  have ho := addPairs_additions_le_endpoints
    (suffixBuild (prefixBuild nodes none (none :: values)).1 values.tail).1 _ hfirst
    (tail_pairs_last nodes none values (by omega))
  rw [tail_pairs_length] at ho
  have hlen : values.tail.length = values.length - 1 := List.length_tail
  change additionCount (mapBuild _ _ _).1 ≤ _
  rw [hcount] at hp
  omega

end IntegerMultBounds.Networks.PairedVectorBudget
