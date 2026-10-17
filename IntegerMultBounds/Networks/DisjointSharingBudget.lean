module

public import IntegerMultBounds.Networks.PairedCircuitBudget
public import IntegerMultBounds.Networks.DisjointUnique

/-! Exact allocation accounting for persistent support interning. The cost is
zero for absent operands and for an already stored union. Stateful loops charge
against the current bank, so sharing with earlier iterations is preserved. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DisjointSharingBudget

open DisjointCircuit DisjointBuilder DisjointUnique PairedCircuit DAGAllocator

variable {ι X Y : Type*} [DecidableEq ι]

/-- Charge one only when smart addition really allocates a new support. -/
def smartAddCost (nodes : List (Node ι)) : Ref → Ref → ℕ
  | none, _ => 0
  | _, none => 0
  | some l, some r =>
    if refSupport nodes (some l) ∪ refSupport nodes (some r) ∈ nodes.map Node.support
    then 0 else 1

/-- Exact accounting includes both zero elision and support reuse. -/
theorem smartAdd_additions (nodes : List (Node ι)) (l r : Ref) :
    additionCount (smartAdd nodes l r).1 = additionCount nodes + smartAddCost nodes l r := by
  cases l with
  | none => simp [smartAdd, smartAddCost]
  | some l =>
    cases r with
    | none => simp [smartAdd, smartAddCost]
    | some r =>
      simp only [smartAdd, smartAddCost]
      unfold intern
      split
      · rename_i i hi
        have hm : refSupport nodes (some l) ∪ refSupport nodes (some r) ∈ nodes.map Node.support := by
          by_contra hn
          have hf := (findSupport_none_iff _ _).mpr hn
          simp [hf] at hi
        simp [hm]
      · rename_i hn
        have hm := (findSupport_none_iff _ _).mp hn
        simp [hm, additionCount, List.countP_append]

/-- A symbolic proof that a union was already stored discharges its cost. -/
theorem smartAdd_reuses (nodes : List (Node ι)) (l r : ℕ)
    (h : refSupport nodes (some l) ∪ refSupport nodes (some r) ∈ nodes.map Node.support) :
    additionCount (smartAdd nodes (some l) (some r)).1 = additionCount nodes := by
  rw [smartAdd_additions]
  simp [smartAddCost, h]

/-- Extend an intern bank without invalidating a previously established saving. -/
theorem union_mem_of_extends (nodes larger : List (Node ι)) (l r : Ref)
    (he : Extends nodes larger) (hl : RefValid nodes l) (hr : RefValid nodes r)
    (hm : refSupport nodes l ∪ refSupport nodes r ∈ nodes.map Node.support) :
    refSupport larger l ∪ refSupport larger r ∈ larger.map Node.support := by
  rw [refSupport_extends he hl, refSupport_extends he hr]
  obtain ⟨tail, rfl⟩ := he
  simpa only [List.map_append] using List.mem_append_left (tail.map Node.support) hm

/-- Stateful cost fold, using precisely the banks seen by the actual loop. -/
def loopCost (f : List (Node ι) → X → List (Node ι) × Y)
    (cost : List (Node ι) → X → ℕ) (nodes : List (Node ι)) : List X → ℕ
  | [] => 0
  | x :: xs => cost nodes x + loopCost f cost (f nodes x).1 xs

omit [DecidableEq ι] in
/-- Exact per-step accounting composes without losing any inter-iteration reuse. -/
theorem mapBuild_additions (f : List (Node ι) → X → List (Node ι) × Y)
    (cost : List (Node ι) → X → ℕ)
    (h : ∀ ns x, additionCount (f ns x).1 = additionCount ns + cost ns x)
    (nodes : List (Node ι)) (xs : List X) :
    additionCount (mapBuild f nodes xs).1 = additionCount nodes + loopCost f cost nodes xs := by
  induction xs generalizing nodes with
  | nil => simp [mapBuild, loopCost]
  | cons x xs ih =>
    simp only [mapBuild, loopCost]
    rw [ih, h]
    omega

/-- Number of actual operands; absent references do not consume additions. -/
def presentCount (refs : List Ref) : ℕ := refs.countP Option.isSome

private theorem smartAdd_presence (nodes : List (Node ι)) (l r : Ref) :
    ((smartAdd nodes l r).2.isSome.toNat) = max l.isSome.toNat r.isSome.toNat := by
  cases l <;> cases r <;> simp [smartAdd]

private theorem smartAdd_potential (nodes : List (Node ι)) (l r : Ref) :
    additionCount (smartAdd nodes l r).1 + (smartAdd nodes l r).2.isSome.toNat ≤
      additionCount nodes + l.isSome.toNat + r.isSome.toNat := by
  have h := PairedCircuitBudget.smartAdd_additions_le nodes l r
  cases l <;> cases r <;> simp_all [smartAdd]

/-- Prefix accounting carries one unit of potential in its final accumulator.
This charges exactly the number of present operands minus one, including zeros
at arbitrary positions, without examining their supports. -/
theorem prefixBuild_present_le (nodes : List (Node ι)) (acc : Ref) (refs : List Ref) :
    additionCount (prefixBuild nodes acc refs).1 +
        ((prefixBuild nodes acc refs).2.getLast?.getD none).isSome.toNat ≤
      additionCount nodes + acc.isSome.toNat + presentCount refs := by
  induction refs generalizing nodes acc with
  | nil => simp [prefixBuild, presentCount]
  | cons r rs ih =>
    have hs := smartAdd_potential nodes acc r
    have ht := ih (smartAdd nodes acc r).1 (smartAdd nodes acc r).2
    have hn : (prefixBuild (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs).2 ≠ [] := by
      have := prefixBuild_length (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs
      intro he
      simp [he] at this
    simp only [prefixBuild, List.getLast?_cons_of_ne_nil hn]
    simp only [presentCount, List.countP_cons] at ht ⊢
    unfold presentCount at *
    cases r <;> simp only [Option.isSome, Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true,
      ite_false, ite_true] at hs ht ⊢ <;> omega

/-- Suffix accounting obeys the same potential law despite running backwards. -/
theorem suffixBuild_present_le (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (suffixBuild nodes refs).1 +
        ((suffixBuild nodes refs).2.headD none).isSome.toNat ≤
      additionCount nodes + presentCount refs := by
  induction refs with
  | nil => simp [suffixBuild, presentCount]
  | cons r rs ih =>
    have hs := smartAdd_potential (suffixBuild nodes rs).1 r
      ((suffixBuild nodes rs).2.headD none)
    simp only [suffixBuild, List.headD_cons]
    simp only [presentCount, List.countP_cons]
    cases r <;> simp_all [presentCount]
    all_goals omega

theorem prefixBuild_presence (nodes : List (Node ι)) (acc : Ref) (refs : List Ref) :
    ((prefixBuild nodes acc refs).2.getLast?.getD none).isSome.toNat =
      min 1 (acc.isSome.toNat + presentCount refs) := by
  induction refs generalizing nodes acc with
  | nil => cases acc <;> simp [prefixBuild, presentCount]
  | cons r rs ih =>
    have hn : (prefixBuild (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs).2 ≠ [] := by
      have := prefixBuild_length (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs
      intro he
      simp [he] at this
    simp only [prefixBuild, List.getLast?_cons_of_ne_nil hn, ih, smartAdd_presence,
      presentCount, List.countP_cons]
    cases acc <;> cases r <;> simp

theorem suffixBuild_presence (nodes : List (Node ι)) (refs : List Ref) :
    ((suffixBuild nodes refs).2.headD none).isSome.toNat = min 1 (presentCount refs) := by
  induction refs with
  | nil => simp [suffixBuild, presentCount]
  | cons r rs ih =>
    simp only [suffixBuild, List.headD_cons, smartAdd_presence, ih,
      presentCount, List.countP_cons]
    cases r <;> simp

/-- A prefix pass starting from zero allocates at most k minus one additions
for k present operands, regardless of the number and positions of zeros. -/
theorem prefixBuild_additions_le_present (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (prefixBuild nodes none refs).1 ≤
      additionCount nodes + (presentCount refs - 1) := by
  have h := prefixBuild_present_le nodes none refs
  rw [prefixBuild_presence] at h
  simp only [Option.isSome_none, Bool.toNat_false, Nat.zero_add, Nat.add_zero] at h
  omega

/-- The backwards pass has the same k minus one bound. Support interning can
only reduce it further, including reuse of the prefix pass's full total. -/
theorem suffixBuild_additions_le_present (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (suffixBuild nodes refs).1 ≤
      additionCount nodes + (presentCount refs - 1) := by
  have h := suffixBuild_present_le nodes refs
  rw [suffixBuild_presence] at h
  omega

/-- The actual interning costs of each pass remain available separately for
symbolic reuse proofs and for composing recursive construction stages. -/
def prefixCost (nodes : List (Node ι)) (acc : Ref) : List Ref → ℕ
  | [] => 0
  | r :: rs => smartAddCost nodes acc r +
      prefixCost (smartAdd nodes acc r).1 (smartAdd nodes acc r).2 rs

theorem prefixBuild_additions (nodes : List (Node ι)) (acc : Ref) (refs : List Ref) :
    additionCount (prefixBuild nodes acc refs).1 =
      additionCount nodes + prefixCost nodes acc refs := by
  induction refs generalizing nodes acc with
  | nil => simp [prefixBuild, prefixCost]
  | cons r rs ih =>
    simp only [prefixBuild, prefixCost]
    rw [ih, smartAdd_additions]
    omega

def suffixCost (nodes : List (Node ι)) : List Ref → ℕ
  | [] => 0
  | r :: rs => suffixCost nodes rs + smartAddCost (suffixBuild nodes rs).1 r
      ((suffixBuild nodes rs).2.headD none)

theorem suffixBuild_additions (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (suffixBuild nodes refs).1 = additionCount nodes + suffixCost nodes refs := by
  induction refs with
  | nil => simp [suffixBuild, suffixCost]
  | cons r rs ih =>
    simp only [suffixBuild, suffixCost]
    rw [smartAdd_additions, ih]
    omega

/-- Exact allocation cost of the actual three-pass vector, retaining every
zero-elision and support-sharing saving in the persistent bank. -/
def vectorCost (nodes : List (Node ι)) (refs : List Ref) : ℕ :=
  let pre := prefixBuild nodes none refs
  let suf := suffixBuild pre.1 refs
  prefixCost nodes none refs + suffixCost pre.1 refs +
    loopCost (fun ns p => smartAdd ns p.1 p.2)
      (fun ns p => smartAddCost ns p.1 p.2) suf.1 (pre.2.zip suf.2.tail)

theorem vectorFalse_additions (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (vectorFalse nodes refs).nodes = additionCount nodes + vectorCost nodes refs := by
  have ho := mapBuild_additions (fun ns (p : Ref × Ref) => smartAdd ns p.1 p.2)
    (fun ns p => smartAddCost ns p.1 p.2) (fun ns p => smartAdd_additions ns p.1 p.2)
    (suffixBuild (prefixBuild nodes none refs).1 refs).1
    ((prefixBuild nodes none refs).2.zip (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail)
  simp only [vectorFalse, vectorCost]
  rw [ho, suffixBuild_additions, prefixBuild_additions]
  omega

/-- Keep the omission pass's exact state-dependent cost while replacing both
linear passes by symbolic zero-aware bounds. This is useful when a structural
argument establishes reuse for particular omission unions. -/
theorem vectorFalse_additions_le_present (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (vectorFalse nodes refs).nodes ≤
      additionCount nodes + 2 * (presentCount refs - 1) +
        loopCost (fun ns p => smartAdd ns p.1 p.2)
          (fun ns p => smartAddCost ns p.1 p.2)
          (suffixBuild (prefixBuild nodes none refs).1 refs).1
          ((prefixBuild nodes none refs).2.zip
            (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail) := by
  have hp := prefixBuild_additions_le_present nodes refs
  have hs := suffixBuild_additions_le_present (prefixBuild nodes none refs).1 refs
  have ho := mapBuild_additions (fun ns (p : Ref × Ref) => smartAdd ns p.1 p.2)
    (fun ns p => smartAddCost ns p.1 p.2) (fun ns p => smartAdd_additions ns p.1 p.2)
    (suffixBuild (prefixBuild nodes none refs).1 refs).1
    ((prefixBuild nodes none refs).2.zip (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail)
  change additionCount (mapBuild _ _ _).1 ≤ _
  rw [ho]
  omega

/-- A cheaper drop-in bound for vector construction when only the number of
present inputs is known. The omission pass is conservatively charged per slot. -/
theorem vectorFalse_additions_le_present_length (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (vectorFalse nodes refs).nodes ≤
      additionCount nodes + 2 * (presentCount refs - 1) + refs.length := by
  have hp := prefixBuild_additions_le_present nodes refs
  have hs := suffixBuild_additions_le_present (prefixBuild nodes none refs).1 refs
  have ho := PairedCircuitBudget.mapBuild_additions_le
    (fun ns (p : Ref × Ref) => smartAdd ns p.1 p.2) (fun _ => 1)
    (suffixBuild (prefixBuild nodes none refs).1 refs).1
    ((prefixBuild nodes none refs).2.zip (suffixBuild (prefixBuild nodes none refs).1 refs).2.tail)
    (fun ns p => PairedCircuitBudget.smartAdd_additions_le ns p.1 p.2)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one,
    List.length_zip, prefixBuild_length, List.length_tail, suffixBuild_length] at ho
  change additionCount (mapBuild _ _ _).1 ≤ _
  omega

/-- The strip vector obeys the same zero-aware bound. -/
theorem vectorTail_additions_le_present_length (nodes : List (Node ι)) (refs : List Ref) :
    additionCount (vectorTail nodes refs).nodes ≤
      additionCount nodes + 2 * (presentCount refs - 1) + refs.length := by
  cases refs with
  | nil => simp [vectorTail]
  | cons carry values =>
    have hp := prefixBuild_additions_le_present nodes (carry :: values)
    have hs := suffixBuild_additions_le_present (prefixBuild nodes none (carry :: values)).1 values.tail
    have hmono : presentCount values.tail ≤ presentCount (carry :: values) := by
      unfold presentCount
      exact ((List.tail_sublist values).trans (List.sublist_cons_self carry values)).countP_le
    have ho := PairedCircuitBudget.mapBuild_additions_le
      (fun ns (p : Ref × Ref) => smartAdd ns p.1 p.2) (fun _ => 1)
      (suffixBuild (prefixBuild nodes none (carry :: values)).1 values.tail).1
      (((prefixBuild nodes none (carry :: values)).2.drop 1).zip
        ((suffixBuild (prefixBuild nodes none (carry :: values)).1 values.tail).2.take values.length))
      (fun ns p => PairedCircuitBudget.smartAdd_additions_le ns p.1 p.2)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one, List.length_zip,
      List.length_drop, prefixBuild_length, List.length_take, suffixBuild_length] at ho
    change additionCount (mapBuild _ _ _).1 ≤ _
    simp only [List.length_cons] at hp ho ⊢
    omega

/-- Zero-aware budget for an actual strip. Only the vector's present-input
count depends on the produced references; the balanced totals use shape bounds. -/
def stripPresentBudget (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) : ℕ :=
  let remaining := (groupAt groups ia.1).filter (· != ia.2)
  let other := (List.range groups.length).filter (· != ia.1)
  let carry := DisjointBalanced.total nodes (remaining.map (lookup weights))
  let vals := mapBuild (fun ns j => DisjointBalanced.total ns
    (crossRefs edges remaining (groupAt groups j))) carry.1 other
  (remaining.length - 1) +
    (other.map (fun j => remaining.length * (groupAt groups j).length - 1)).sum +
    2 * (presentCount (carry.2 :: vals.2) - 1) + (1 + other.length)

/-- The refined vector bound transfers to the actual recursive strip builder,
so future reductions in present operands require no new compiler proof. -/
theorem buildStrip_additions_le_present (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) :
    additionCount (buildStrip nodes groups edges weights ia).1 ≤
      additionCount nodes + stripPresentBudget nodes groups edges weights ia := by
  let remaining := (groupAt groups ia.1).filter (· != ia.2)
  let other := (List.range groups.length).filter (· != ia.1)
  let carry := DisjointBalanced.total nodes (remaining.map (lookup weights))
  let vals := mapBuild (fun ns j => DisjointBalanced.total ns
    (crossRefs edges remaining (groupAt groups j))) carry.1 other
  have hc := PairedCircuitBudget.total_additions_le nodes (remaining.map (lookup weights))
  have hv := PairedCircuitBudget.mapBuild_additions_le (fun ns j => DisjointBalanced.total ns
    (crossRefs edges remaining (groupAt groups j)))
    (fun j => remaining.length * (groupAt groups j).length - 1) carry.1 other
    (fun ns j => by simpa only [PairedCircuitBudget.crossRefs_length] using
      PairedCircuitBudget.total_additions_le ns (crossRefs edges remaining (groupAt groups j)))
  have hs := vectorTail_additions_le_present_length vals.1 (carry.2 :: vals.2)
  have hlen : vals.2.length = other.length := mapBuild_length _ _ _
  simp only [List.length_map] at hc
  simp only [List.length_cons, hlen] at hs
  change additionCount carry.1 ≤ _ at hc
  change additionCount vals.1 ≤ _ at hv
  change additionCount (vectorTail vals.1 (carry.2 :: vals.2)).nodes ≤ _
  change _ ≤ additionCount nodes + ((remaining.length - 1) +
    (other.map (fun j => remaining.length * (groupAt groups j).length - 1)).sum +
      2 * (presentCount (carry.2 :: vals.2) - 1) + (1 + other.length))
  omega

/-- Exact sharing-aware cost of the single-exclusion stage of a paired level. -/
def singlesCost (nodes : List (Node ι)) (groups : List (List ℕ))
    (outside : WeightTable) (strips : List Strip) : ℕ :=
  loopCost (fun ns ia =>
    let r := smartAdd ns (lookup outside ia.1) (stripLookup strips ia.2).total
    (r.1, (ia.2, r.2)))
    (fun ns ia => smartAddCost ns (lookup outside ia.1) (stripLookup strips ia.2).total)
    nodes (members groups)

theorem buildSingles_additions (nodes : List (Node ι)) (groups : List (List ℕ))
    (outside : WeightTable) (strips : List Strip) :
    additionCount (buildSingles nodes groups outside strips).1 =
      additionCount nodes + singlesCost nodes groups outside strips := by
  unfold buildSingles singlesCost
  apply mapBuild_additions
  intro ns ia
  exact smartAdd_additions ns _ _

end IntegerMultBounds.Networks.DisjointSharingBudget
