module

public import IntegerMultBounds.Networks.PairedStripCorrect
public import IntegerMultBounds.Networks.PairedVectorCorrect
import IntegerMultBounds.Networks.PairedLevelTools

/-! Intermediate sums of a strip are stored, not only its total and
omissions. Every nonempty prefix of the strip vector, every suffix after the
carry's neighbour and every grouped value is the support of a stored node. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedStarPresence

open DisjointCircuit DisjointBuilder PairedCircuit DisjointExclusion PairedVectorCorrect
open PairedCircuitCorrect PairedLevelTools

variable {ι : Type*} [DecidableEq ι]

/-- A support carried by some node of the list. -/
def Stored (nodes : List (Node ι)) (s : Finset ι) : Prop := s ∈ nodes.map Node.support

omit [DecidableEq ι] in
theorem stored_extends {nodes larger : List (Node ι)} (he : Extends nodes larger) {s : Finset ι}
    (h : Stored nodes s) : Stored larger s := by
  obtain ⟨tail, rfl⟩ := he
  unfold Stored
  rw [List.map_append]
  exact List.mem_append_left _ h

omit [DecidableEq ι] in
/-- A valid reference with nonempty support points at a node carrying it. -/
theorem stored_of_ref (nodes : List (Node ι)) (r : Ref) (hr : RefValid nodes r)
    (hne : refSupport nodes r ≠ ∅) : Stored nodes (refSupport nodes r) := by
  cases r with
  | none => exact False.elim (hne rfl)
  | some i =>
    have hi : i < nodes.length := hr
    rw [refSupport_some nodes i hi]
    exact List.mem_map_of_mem (List.getElem_mem hi)

omit [DecidableEq ι] in
theorem map_getElem_eq {α β : Type*} {f : α → β} {l : List α} {l' : List β} (h : l.map f = l')
    (t : ℕ) (ht : t < l.length) (x : β) (hx : l'[t]? = some x) : f l[t] = x := by
  subst h
  simpa [List.getElem?_map, List.getElem?_eq_getElem ht] using hx

theorem beforeSupports_get (nodes : List (Node ι)) (acc : Finset ι) (refs : List Ref) (t : ℕ)
    (ht : t ≤ refs.length) :
    (beforeSupports nodes acc refs)[t]? = some (acc ∪ supports nodes (refs.take t)) := by
  induction refs generalizing acc t with
  | nil =>
    have : t = 0 := by simpa using ht
    subst this
    simp [beforeSupports, supports]
  | cons r rs ih =>
    cases t with
    | zero => simp [beforeSupports, supports]
    | succ t =>
      simp only [beforeSupports, List.getElem?_cons_succ, List.take_succ_cons, supports]
      rw [ih _ t (by simpa using ht), Finset.union_assoc]

theorem afterSupports_get (nodes : List (Node ι)) (refs : List Ref) (k : ℕ) (hk : k < refs.length) :
    (afterSupports nodes refs)[k]? = some (supports nodes (refs.drop (k + 1))) := by
  induction refs generalizing k with
  | nil => simp at hk
  | cons r rs ih =>
    cases k with
    | zero => simp [afterSupports]
    | succ k =>
      simp only [afterSupports, List.getElem?_cons_succ, List.drop_succ_cons]
      exact ih k (by simpa using hk)

theorem supports_nil_drop (nodes : List (Node ι)) (refs : List Ref) (d : ℕ) (hd : refs.length ≤ d) :
    supports nodes (refs.drop d) = ∅ := by
  rw [List.drop_eq_nil_of_le hd]
  rfl

/-- The strip vector stores every nonempty prefix and every nonempty suffix
starting after its second entry. -/
theorem vectorTail_stored (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    (∀ t ≤ refs.length, supports nodes (refs.take t) ≠ ∅ →
      Stored (vectorTail nodes refs).nodes (supports nodes (refs.take t))) ∧
    (∀ d, 2 ≤ d → supports nodes (refs.drop d) ≠ ∅ →
      Stored (vectorTail nodes refs).nodes (supports nodes (refs.drop d))) := by
  cases refs with
  | nil =>
    refine ⟨fun t _ h => False.elim (h (by simp [supports])), fun d _ h => False.elim (h ?_)⟩
    simp [supports]
  | cons carry values =>
    let pre := prefixBuild nodes none (carry :: values)
    have hp := prefixBuild_built nodes none (carry :: values) hv trivial hr
      (List.pairwise_cons.mpr ⟨by simp [refSupport], hd⟩)
    have hvr : RefsValid nodes values := fun x hx => hr x (by simp [hx])
    have hdv := (List.pairwise_cons.mp hd).2
    have hvt : RefsValid nodes values.tail := fun x hx => hvr x (List.mem_of_mem_tail hx)
    have hdt : DisjointRefs nodes values.tail := hdv.sublist (List.tail_sublist _)
    let suf := suffixes pre.1 values.tail
    have hs := suffixes_built pre.1 values.tail hp.valid (refsValid_extends hp.extension hvt)
      (disjointRefs_extends hp.extension _ hvt hdt)
    have hsuf : Extends suf.nodes (vectorTail nodes (carry :: values)).nodes := by
      simp only [vectorTail, suffixBuild_eq]
      exact mapBuild_extends _ (fun ns (p : Ref × Ref) => smartAdd_extends ns p.1 p.2) _ _
    have hpre : Extends pre.1 (vectorTail nodes (carry :: values)).nodes :=
      extends_trans hs.built.extension hsuf
    refine ⟨?_, ?_⟩
    · intro t ht hne
      have hlen : t < pre.2.length := by
        rw [prefixBuild_length]; exact Nat.lt_succ_of_le ht
      have he := map_getElem_eq hp.supports_eq t hlen _ (beforeSupports_get _ _ _ t ht)
      rw [refSupport, Finset.empty_union] at he
      have hval := hp.refs_valid _ (List.getElem_mem hlen)
      rw [← he] at hne ⊢
      exact stored_extends hpre (stored_of_ref _ _ hval hne)
    · intro d hd2 hne
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
      have hdrop : (carry :: values).drop (k + 2) = values.tail.drop k := by
        cases values <;> simp
      rw [hdrop] at hne ⊢
      have hext : supports pre.1 (values.tail.drop k) = supports nodes (values.tail.drop k) :=
        supports_extends hp.extension _ (fun x hx => hvt x (List.mem_of_mem_drop hx))
      cases k with
      | zero =>
        have he := hs.built.support_eq
        rw [List.drop_zero] at hext ⊢ hne
        rw [hext] at he
        have hval := hs.built.refValid
        rw [← he] at hne ⊢
        exact stored_extends hsuf (stored_of_ref _ _ hval hne)
      | succ k =>
        by_cases hk : k < values.tail.length
        · have hlen : k < suf.after.length := by rw [suffixes_after_length]; exact hk
          have he := map_getElem_eq hs.after_supports k hlen _ (afterSupports_get _ _ k hk)
          rw [hext] at he
          have hval := hs.after_valid _ (List.getElem_mem hlen)
          rw [← he] at hne ⊢
          exact stored_extends hsuf (stored_of_ref _ _ hval hne)
        · exact False.elim (hne (supports_nil_drop _ _ _ (by omega)))

theorem supports_batch_take (nodes : List (Node ι)) (queries : List (List Ref))
    (result : List (Node ι) × List Ref) (hb : DisjointPaired.BatchBuilt nodes queries result) (t : ℕ) :
    supports result.1 (result.2.take t) = supports nodes (queries.take t).flatten := by
  rw [supports_foldr, List.map_take, hb.supports_eq, supports_flatten, List.map_take]

theorem supports_batch_drop (nodes : List (Node ι)) (queries : List (List Ref))
    (result : List (Node ι) × List Ref) (hb : DisjointPaired.BatchBuilt nodes queries result) (d : ℕ) :
    supports result.1 (result.2.drop d) = supports nodes (queries.drop d).flatten := by
  rw [supports_foldr, List.map_drop, hb.supports_eq, supports_flatten, List.map_drop]

/-- Facts about the stored sums of one strip, phrased in original operands. -/
structure StripStored (original : List (Node ι)) (queries : List (List Ref))
    (nodes : List (Node ι)) : Prop where
  value : ∀ k (hk : k < queries.length), supports original queries[k] ≠ ∅ →
    Stored nodes (supports original queries[k])
  prefix_ : ∀ t ≤ queries.length, supports original (queries.take t).flatten ≠ ∅ →
    Stored nodes (supports original (queries.take t).flatten)
  suffix : ∀ d, 2 ≤ d → supports original (queries.drop d).flatten ≠ ∅ →
    Stored nodes (supports original (queries.drop d).flatten)
  omission : ∀ k, 1 ≤ k → k < queries.length → supports original (queries.eraseIdx k).flatten ≠ ∅ →
    Stored nodes (supports original (queries.eraseIdx k).flatten)

theorem stripStored_extends {original nodes larger : List (Node ι)} {queries : List (List Ref)}
    (he : Extends nodes larger) (h : StripStored original queries nodes) :
    StripStored original queries larger :=
  ⟨fun k hk hne => stored_extends he (h.value k hk hne),
    fun t ht hne => stored_extends he (h.prefix_ t ht hne),
    fun d hd hne => stored_extends he (h.suffix d hd hne),
    fun k hk hk' hne => stored_extends he (h.omission k hk hk' hne)⟩

theorem supports_sub {a b : List (Node ι)} (he : Extends a b) (all refs : List Ref)
    (hr : RefsValid a all) (hs : ∀ r ∈ refs, r ∈ all) : supports b refs = supports a refs :=
  DisjointExclusion.supports_extends he _ (fun r hm => hr r (hs r hm))

/-- Stored strip facts may be restated over any earlier valid list. -/
theorem stripStored_change {a b : List (Node ι)} (queries : List (List Ref)) (nodes : List (Node ι))
    (he : Extends a b) (hr : RefsValid a queries.flatten) (h : StripStored b queries nodes) :
    StripStored a queries nodes := by
  have hm : ∀ qs : List (List Ref), (∀ q ∈ qs, q ∈ queries) → ∀ r ∈ qs.flatten, r ∈ queries.flatten :=
    fun qs hqs r hr' => by
      obtain ⟨q, hq, hrq⟩ := List.mem_flatten.mp hr'
      exact List.mem_flatten.mpr ⟨q, hqs q hq, hrq⟩
  refine ⟨fun k hk hne => ?_, fun t ht hne => ?_, fun d hd hne => ?_, fun k hk hk' hne => ?_⟩
  · have hs := supports_sub he queries.flatten queries[k] hr
      (fun r hr' => List.mem_flatten.mpr ⟨_, List.getElem_mem hk, hr'⟩)
    rw [← hs] at hne ⊢; exact h.value k hk hne
  · have hs := supports_sub he queries.flatten _ hr (hm (queries.take t) (fun q hq => List.mem_of_mem_take hq))
    rw [← hs] at hne ⊢; exact h.prefix_ t ht hne
  · have hs := supports_sub he queries.flatten _ hr (hm (queries.drop d) (fun q hq => List.mem_of_mem_drop hq))
    rw [← hs] at hne ⊢; exact h.suffix d hd hne
  · have hs := supports_sub he queries.flatten _ hr
      (hm (queries.eraseIdx k) (fun q hq => (List.eraseIdx_sublist _ _).subset hq))
    rw [← hs] at hne ⊢; exact h.omission k hk hk' hne

theorem batchVector_stored (nodes : List (Node ι)) (queries : List (List Ref)) (hv : Valid nodes)
    (hr : RefsValid nodes queries.flatten) (hd : DisjointRefs nodes queries.flatten) :
    StripStored nodes queries
      (vectorTail (DisjointPaired.batch nodes queries).1 (DisjointPaired.batch nodes queries).2).nodes := by
  have hb := DisjointPaired.batch_built nodes queries hv
    (fun q hq r hr' => hr r (List.mem_flatten.mpr ⟨q, hq, hr'⟩))
    (List.pairwise_flatten.mp hd).1
  have hdis := batch_disjoint nodes queries hv hr hd
  have hvec := vectorTail_stored _ _ hb.valid hb.refsValid hdis
  have hext := vectorTail_extends (DisjointPaired.batch nodes queries).1
    (DisjointPaired.batch nodes queries).2
  have hblen : (DisjointPaired.batch nodes queries).2.length = queries.length := by
    have hh := congrArg List.length hb.supports_eq
    simpa only [List.length_map] using hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk hne
    have hlen : k < (DisjointPaired.batch nodes queries).2.length := by omega
    have he := map_getElem_eq hb.supports_eq k hlen _
      (by rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl)
    have hval := hb.refsValid _ (List.getElem_mem hlen)
    rw [← he] at hne ⊢
    exact stored_extends hext (stored_of_ref _ _ hval hne)
  · intro t ht hne
    have h := hvec.1 t (by omega) (by rw [supports_batch_take nodes queries _ hb]; exact hne)
    rw [supports_batch_take nodes queries _ hb] at h
    exact h
  · intro d hd2 hne
    have h := hvec.2 d hd2 (by rw [supports_batch_drop nodes queries _ hb]; exact hne)
    rw [supports_batch_drop nodes queries _ hb] at h
    exact h
  · intro k hk hk' hne
    have hlen : k < (DisjointPaired.batch nodes queries).2.length := by omega
    have hs := PairedVectorCorrect.vectorTail_support _ _ hb.valid hb.refsValid hdis k hk hlen
    rw [batch_erase_support nodes queries hv hr hd k] at hs
    have hout : k < (vectorTail (DisjointPaired.batch nodes queries).1
        (DisjointPaired.batch nodes queries).2).one.length := by rw [vectorTail_length]; exact hlen
    have hval := (PairedVectorCorrect.vectorTail_built _ _ hb.valid hb.refsValid hdis).one_valid _
      (List.getElem_mem hout)
    rw [List.getElem?_eq_getElem hout, Option.getD_some] at hs
    rw [← hs] at hne ⊢
    exact stored_of_ref _ _ hval hne

theorem buildStrip_stored (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) (hv : Valid nodes)
    (hr : RefsValid nodes (stripQueries groups edges weights ia).flatten)
    (hd : DisjointRefs nodes (stripQueries groups edges weights ia).flatten) :
    StripStored nodes (stripQueries groups edges weights ia)
      (buildStrip nodes groups edges weights ia).1 := by
  rw [buildStrip_eq]
  exact batchVector_stored nodes _ hv hr hd

end IntegerMultBounds.Networks.PairedStarPresence
