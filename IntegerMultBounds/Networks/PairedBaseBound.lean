module

public import IntegerMultBounds.Networks.DAGSimulation
public import IntegerMultBounds.Networks.PairedGraphSpec

/-! The four-vertex base block with one zero vertex weight, counted once on
abstract atoms. Simulation transfers the count to every real base call with
the same zero pattern, whatever supports its edges and weights carry. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedBaseBound

open DisjointCircuit DisjointBuilder PairedCircuit DAGAllocator

/-- Nine atoms: six edges, then three present vertex weights. -/
def atoms : List (Node (Fin 9)) := (List.finRange 9).map (fun k => ⟨.input k, {k}⟩)

def edges : EdgeTable := (pairs (List.range 4)).zipIdx.map (fun p => (p.1, some p.2))

def weights : WeightTable := [(0, some 6), (1, some 7), (2, some 8), (3, none)]

theorem abstract_count :
    additionCount (baseBlock atoms (List.range 4) edges weights).nodes = 24 := by
  decide +kernel

section Simulation

open DAGSimulation

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι] (f : α → Finset ι)

/-- Tables with the same keys whose references are related. -/
def TableRel {K : Type*} (abs : List (Node α)) (real : List (Node ι))
    (ta : List (K × Ref)) (tr : List (K × Ref)) : Prop :=
  List.Forall₂ (fun a b => a.1 = b.1 ∧ RefRel f abs real a.2 b.2) ta tr

omit [DecidableEq α] in
theorem tableRel_extends {K : Type*} {abs abs' : List (Node α)} {real real' : List (Node ι)}
    (ha : Extends abs abs') (hr : Extends real real') {ta : List (K × Ref)} {tr : List (K × Ref)}
    (h : TableRel f abs real ta tr) : TableRel f abs' real' ta tr :=
  h.imp (fun _ _ hab => ⟨hab.1, refRel_extends f ha hr hab.2⟩)

omit [DecidableEq α] in
theorem refRel_none (abs : List (Node α)) (real : List (Node ι)) :
    RefRel f abs real none none := ⟨trivial, trivial, rfl, by simp [refSupport, image]⟩

omit [DecidableEq α] in
/-- Filtering by a key predicate keeps related tables related. -/
theorem filter_rel {K : Type*} (abs : List (Node α)) (real : List (Node ι))
    (q : K × Ref → Bool) (hq : ∀ a b : K × Ref, a.1 = b.1 → q a = q b)
    {ta tr : List (K × Ref)} (h : TableRel f abs real ta tr) :
    List.Forall₂ (RefRel f abs real) ((ta.filter q).map Prod.snd) ((tr.filter q).map Prod.snd) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b ta tr hab _ ih =>
    rw [List.filter_cons, List.filter_cons, hq a b hab.1]
    split
    · exact List.Forall₂.cons hab.2 ih
    · exact ih

omit [DecidableEq α] in
theorem lookup_rel {K : Type*} [DecidableEq K] (abs : List (Node α)) (real : List (Node ι))
    {ta tr : List (K × Ref)} (h : TableRel f abs real ta tr) (k : K) :
    RefRel f abs real (lookup ta k) (lookup tr k) := by
  induction h with
  | nil => exact refRel_none f abs real
  | @cons a b ta tr hab _ ih =>
    by_cases hk : a.1 = k
    · have hk' : b.1 = k := hab.1 ▸ hk
      simpa [lookup, hk, hk'] using hab.2
    · have hk' : ¬ b.1 = k := hab.1 ▸ hk
      simpa [lookup, hk, hk'] using ih

omit [DecidableEq α] in
theorem forall₂_append' {X Y : Type*} {R : X → Y → Prop} {a b : List X} {c d : List Y}
    (h₁ : List.Forall₂ R a c) (h₂ : List.Forall₂ R b d) : List.Forall₂ R (a ++ b) (c ++ d) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact List.Forall₂.cons h ih

omit [DecidableEq α] in
theorem query_rel (abs : List (Node α)) (real : List (Node ι)) {ea er : EdgeTable}
    {wa wr : WeightTable} (he : TableRel f abs real ea er) (hw : TableRel f abs real wa wr)
    (excluded : List ℕ) :
    List.Forall₂ (RefRel f abs real) (query ea wa excluded) (query er wr excluded) :=
  forall₂_append' (filter_rel f abs real _ (fun a b h => by rw [h]) he)
    (filter_rel f abs real _ (fun a b h => by rw [h]) hw)

omit [DecidableEq α] in
theorem removed_rel (abs : List (Node α)) (real : List (Node ι)) {ea er : EdgeTable}
    {wa wr : WeightTable} (he : TableRel f abs real ea er) (hw : TableRel f abs real wa wr)
    (excluded : List ℕ) :
    List.Forall₂ (RefRel f abs real) (removed ea wa excluded) (removed er wr excluded) :=
  forall₂_append' (filter_rel f abs real _ (fun a b h => by rw [h]) he)
    (filter_rel f abs real _ (fun a b h => by rw [h]) hw)

/-- The base block with related graph tables is simulated. -/
theorem baseBlock_sim (abs : List (Node α)) (real : List (Node ι)) (points : List ℕ)
    (ea er : EdgeTable) (wa wr : WeightTable) (hc : Covers f abs real)
    (he : TableRel f abs real ea er) (hw : TableRel f abs real wa wr) :
    Step f abs real (baseBlock abs points ea wa).nodes (baseBlock real points er wr).nodes := by
  let out := fun (abs' : List (Node α)) (real' : List (Node ι)) (y : ℕ × Ref) (z : ℕ × Ref) =>
    y.1 = z.1 ∧ RefRel f abs' real' y.2 z.2
  have hout : ∀ abs abs' real real' y z, Extends abs abs' → Extends real real' →
      out abs real y z → out abs' real' y z :=
    fun _ _ _ _ _ _ ha hr h => ⟨h.1, refRel_extends f ha hr h.2⟩
  obtain ⟨s1, o1⟩ := mapBuild_sim f
    (fun ns a => let r := DisjointBalanced.total ns (query ea wa [a]); (r.1, (a, r.2)))
    (fun ns a => let r := DisjointBalanced.total ns (query er wr [a]); (r.1, (a, r.2)))
    out hout abs real points (fun a _ abs' real' ha hr hc' => by
      obtain ⟨st, rt⟩ := total_sim f abs' real' _ _ hc'
        (query_rel f abs' real' (tableRel_extends f ha hr he) (tableRel_extends f ha hr hw) [a])
      exact ⟨st, rfl, rt⟩) abs real (extends_refl _) (extends_refl _) hc
  let one := mapBuild (fun ns a => let r := DisjointBalanced.total ns (query ea wa [a]); (r.1, (a, r.2)))
    abs points
  let one' := mapBuild (fun ns a => let r := DisjointBalanced.total ns (query er wr [a]); (r.1, (a, r.2)))
    real points
  change Step f abs real one.1 one'.1 at s1
  change List.Forall₂ (out one.1 one'.1) one.2 one'.2 at o1
  obtain ⟨s2, o2⟩ := mapBuild_sim f
    (fun ns (p : ℕ × ℕ) => let r := DisjointBalanced.total ns (query ea wa [p.1, p.2]); (r.1, (p, r.2)))
    (fun ns (p : ℕ × ℕ) => let r := DisjointBalanced.total ns (query er wr [p.1, p.2]); (r.1, (p, r.2)))
    (fun abs' real' (y : (ℕ × ℕ) × Ref) z => y.1 = z.1 ∧ RefRel f abs' real' y.2 z.2)
    (fun _ _ _ _ _ _ ha hr h => ⟨h.1, refRel_extends f ha hr h.2⟩) one.1 one'.1 (pairs points)
    (fun p _ abs' real' ha hr hc' => by
      have ha' := extends_trans s1.abs_extends ha
      have hr' := extends_trans s1.real_extends hr
      obtain ⟨st, rt⟩ := total_sim f abs' real' _ _ hc'
        (query_rel f abs' real' (tableRel_extends f ha' hr' he) (tableRel_extends f ha' hr' hw) [p.1, p.2])
      exact ⟨st, rfl, rt⟩) one.1 one'.1 (extends_refl _) (extends_refl _) s1.covers
  let two := mapBuild (fun ns (p : ℕ × ℕ) =>
    let r := DisjointBalanced.total ns (query ea wa [p.1, p.2]); (r.1, (p, r.2))) one.1 (pairs points)
  let two' := mapBuild (fun ns (p : ℕ × ℕ) =>
    let r := DisjointBalanced.total ns (query er wr [p.1, p.2]); (r.1, (p, r.2))) one'.1 (pairs points)
  change Step f one.1 one'.1 two.1 two'.1 at s2
  have hA := extends_trans s1.abs_extends s2.abs_extends
  have hR := extends_trans s1.real_extends s2.real_extends
  have s12 := Step.trans f s1 s2
  cases hl : points.getLast? with
  | none =>
    obtain ⟨st, _⟩ := total_sim f two.1 two'.1 _ _ s2.covers
      (query_rel f two.1 two'.1 (tableRel_extends f hA hR he) (tableRel_extends f hA hR hw) [])
    have h := Step.trans f s12 st
    simpa only [baseBlock, hl] using h
  | some a =>
    obtain ⟨st, rt⟩ := total_sim f two.1 two'.1 _ _ s2.covers
      (removed_rel f two.1 two'.1 (tableRel_extends f hA hR he) (tableRel_extends f hA hR hw) [a])
    have hone : TableRel f one.1 one'.1 one.2 one'.2 := o1
    have hone' := tableRel_extends f (extends_trans s2.abs_extends st.abs_extends)
      (extends_trans s2.real_extends st.real_extends) hone
    obtain ⟨sa, _⟩ := smartAdd_sim f _ _ _ _ _ _ st.covers (lookup_rel f _ _ hone' a) rt
    have h := Step.trans f (Step.trans f s12 st) sa
    simpa only [baseBlock, hl] using h

end Simulation

section Real

open DAGSimulation

variable {ι : Type*} [DecidableEq ι]

theorem atoms_length : atoms.length = 9 := by simp [atoms]

theorem atoms_additions : additionCount atoms = 0 := by decide

theorem refSupport_atoms (k : ℕ) (hk : k < 9) : refSupport atoms (some k) = {⟨k, hk⟩} := by
  simp [atoms, refSupport, hk]

/-- The real reference standing for abstract atom `k`. -/
def atomRef (er : EdgeTable) (wr : WeightTable) (k : ℕ) : Ref :=
  if k < 6 then (er[k]?.map Prod.snd).getD none else (wr[k - 6]?.map Prod.snd).getD none

def atomSupport (real : List (Node ι)) (er : EdgeTable) (wr : WeightTable) (k : Fin 9) : Finset ι :=
  refSupport real (atomRef er wr k.val)

private theorem image_atom (real : List (Node ι)) (er : EdgeTable) (wr : WeightTable)
    (k : ℕ) (hk : k < 9) :
    image (atomSupport real er wr) (refSupport atoms (some k)) = refSupport real (atomRef er wr k) := by
  rw [refSupport_atoms k hk]
  simp [image, atomSupport]

/-- Every real four-vertex base call with three present weights and a zero
last weight allocates at most twenty-four additions. -/
theorem base_additions_le (real : List (Node ι)) (er : EdgeTable) (wr : WeightTable)
    (hE : er.map Prod.fst = pairs (List.range 4))
    (hEs : ∀ e ∈ er, ∃ i, e.2 = some i ∧ i < real.length)
    (hW : wr.map Prod.fst = List.range 4)
    (hWs : ∀ w ∈ wr, w.1 < 3 → ∃ i, w.2 = some i ∧ i < real.length)
    (hW3 : ∀ w ∈ wr, 3 ≤ w.1 → w.2 = none) :
    additionCount (baseBlock real (List.range 4) er wr).nodes ≤ additionCount real + 24 := by
  let g := atomSupport real er wr
  have hel : er.length = 6 := by
    have h := congrArg List.length hE
    have h6 : (pairs (List.range 4)).length = 6 := by decide
    simp only [List.length_map] at h
    omega
  have hwl : wr.length = 4 := by
    have h := congrArg List.length hW
    simpa using h
  have hkey (i : ℕ) (hi : i < er.length) : er[i].1 = (pairs (List.range 4))[i]'(by
      rw [← hE, List.length_map]; exact hi) := by
    simp only [← hE, List.getElem_map]
  have hwkey (i : ℕ) (hi : i < wr.length) : wr[i].1 = i := by
    have h := congrArg (fun l : List ℕ => l[i]?) hW
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some] at h
    rw [List.getElem?_range (by omega)] at h
    exact Option.some.inj h
  have hE' : TableRel g atoms real edges er := by
    apply List.forall₂_iff_get.mpr
    refine ⟨by rw [hel]; decide, ?_⟩
    intro i h1 h2
    have hi6 : i < 6 := by rw [hel] at h2; exact h2
    obtain ⟨j, hj, hjl⟩ := hEs _ (List.getElem_mem h2)
    simp only [List.get_eq_getElem]
    have hed : edges[i]'h1 = ((pairs (List.range 4))[i]'(by rw [← hE, List.length_map]; exact h2),
        some i) := by
      simp only [edges, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rw [hed]
    refine ⟨(hkey i h2).symm, by simp [RefValid, atoms_length]; omega, by rw [hj]; exact hjl,
      by rw [hj]; rfl, ?_⟩
    rw [image_atom real er wr i (by omega)]
    simp [atomRef, hi6, List.getElem?_eq_getElem h2]
  have hW' : TableRel g atoms real weights wr := by
    apply List.forall₂_iff_get.mpr
    refine ⟨by rw [hwl]; rfl, ?_⟩
    intro i h1 h2
    have hi4 : i < 4 := by rw [hwl] at h2; exact h2
    simp only [List.get_eq_getElem]
    have hk := hwkey i h2
    by_cases h3 : i < 3
    · obtain ⟨j, hj, hjl⟩ := hWs _ (List.getElem_mem h2) (by rw [hk]; exact h3)
      have hwd : weights[i]'h1 = (i, some (6 + i)) := by
        interval_cases i <;> rfl
      rw [hwd]
      refine ⟨hk.symm, by simp [RefValid, atoms_length]; omega, by rw [hj]; exact hjl,
        by rw [hj]; rfl, ?_⟩
      rw [image_atom real er wr (6 + i) (by omega)]
      simp [atomRef, List.getElem?_eq_getElem h2]
    · have hi : i = 3 := by omega
      subst hi
      have hnone := hW3 _ (List.getElem_mem h2) (by rw [hk])
      have hwd : weights[3]'h1 = (3, none) := rfl
      rw [hwd]
      exact ⟨hk.symm, by rw [hnone]; exact refRel_none g atoms real⟩
  have hc : Covers g atoms real := by
    intro s hs
    obtain ⟨node, hn, rfl⟩ := List.mem_map.mp hs
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hn
    have hk : k.val < 9 := k.isLt
    have him : image g ({k} : Finset (Fin 9)) = refSupport real (atomRef er wr k.val) := by
      simp [image, g, atomSupport]
    change image g {k} ∈ _
    rw [him]
    have hsome : ∃ j, atomRef er wr k.val = some j ∧ j < real.length := by
      by_cases h6 : k.val < 6
      · obtain ⟨j, hj, hjl⟩ := hEs _ (List.getElem_mem (show k.val < er.length by omega))
        exact ⟨j, by simp [atomRef, h6, List.getElem?_eq_getElem (show k.val < er.length by omega), hj], hjl⟩
      · have hw : k.val - 6 < wr.length := by omega
        obtain ⟨j, hj, hjl⟩ := hWs _ (List.getElem_mem hw) (by rw [hwkey _ hw]; omega)
        exact ⟨j, by simp [atomRef, h6, List.getElem?_eq_getElem hw, hj], hjl⟩
    obtain ⟨j, hj, hjl⟩ := hsome
    rw [hj, refSupport_some real j hjl]
    exact List.mem_map_of_mem (List.getElem_mem hjl)
  have hs := baseBlock_sim g atoms real (List.range 4) edges er weights wr hc hE' hW'
  have hcount := hs.count
  rw [abstract_count, atoms_additions] at hcount
  omega

end Real

end IntegerMultBounds.Networks.PairedBaseBound
