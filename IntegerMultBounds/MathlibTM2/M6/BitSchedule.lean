module

public import IntegerMultBounds.MathlibTM2.M6.BitOccurrences
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Recipe

/-!
# The nine-stage schedule, its hosting windows and its child list

`schedule K` is the node's schedule (upstream `global_k.py`): the recipe's sweeps, bridges and
exchange, with the idle entries that follow certain sweeps. After the sweep of stage `s`, an odd
`s ≤ 2K-3` idles pair `(s+1)/2` at rank `7(s+1)`, an even `2 ≤ s ≤ 2K-2` idles pair `s/2` at
rank `7`, and `s = 2K` idles every pair `j` at rank `7(2K-(2j+2))`.

`windows` is upstream's hosting window (`audit_hosted_k.py`, `windows`). An idle of pair `p` at
schedule position `q` can host residuals of the stages swept strictly between the last touch of
`p` and `q`, on other pairs.
* `windows_four` computes the nine-stage windows, and `idle_rank_window` shows each idle rank is
  `7` per window stage.
* `selection_in_windows` checks that every stage hosted into an idle by the frozen selection lies
  in that idle's window. This is the hosting check that `BitOccurrences` leaves open.
* `nodeChildren` lists the node's children in schedule order: the 32 invocations of each sweep,
  then each idle's remainders in each replica. `nodeChildren_realizes` shows it realizes
  `bitHistogram`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitSchedule

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.MathlibTM2.Layer.SelectedMoments
open IntegerMultBounds.MathlibTM2.M6.BitOccurrences

/-- A schedule entry. -/
inductive Entry where
  | sweep (stage pair : ℕ)
  | idle (pair rank : ℕ)
  | bridge (dst src : ℕ)
  | exchange
  deriving DecidableEq, Repr

/-- The schedule entries of one recipe event. -/
def entriesOf (K : ℕ) : Nine.Event → List Entry
  | .sweep s p _ =>
      .sweep s p ::
        (if s % 2 = 1 ∧ s ≤ 2 * K - 3 then [.idle ((s + 1) / 2) (7 * (s + 1))]
        else if s % 2 = 0 ∧ 2 ≤ s ∧ s ≤ 2 * K - 2 then [.idle (s / 2) 7]
        else if s = 2 * K then (List.range K).map fun j => .idle j (7 * (2 * K - (2 * j + 2)))
        else [])
  | .bridge d s _ => [.bridge d s]
  | .exchange => [.exchange]

def schedule (K : ℕ) : List Entry := (Nine.recipe K).flatMap (entriesOf K)

def touches (p : ℕ) : Entry → Bool
  | .sweep _ q => q == p
  | .bridge d s => d == p || s == p
  | _ => false

/-- The stages swept on other pairs strictly between the last touch of pair `p` and position
`pos`. -/
def windowAt (sch : List Entry) (pos p : ℕ) : List ℕ :=
  let before := (sch.take pos).zipIdx
  let start := before.foldl (fun acc x => if touches p x.1 then x.2 + 1 else acc) 0
  (before.drop start).filterMap fun x => match x.1 with
    | .sweep s q => if q ≠ p then some s else none
    | _ => none

/-- Each idle in schedule order, with its pair, rank and window. -/
def windows (sch : List Entry) : List (ℕ × ℕ × List ℕ) :=
  sch.zipIdx.filterMap fun x => match x.1 with
    | .idle p r => some (p, r, windowAt sch x.2 p)
    | _ => none

theorem windows_four : windows (schedule 4) =
    [(1, 14, [0, 1]), (1, 7, [2]), (2, 28, [0, 1, 2, 3]), (2, 7, [4]), (3, 42, [0, 1, 2, 3, 4, 5]),
     (3, 7, [6]), (0, 42, [3, 4, 5, 6, 7, 8]), (1, 28, [5, 6, 7, 8]), (2, 14, [7, 8]), (3, 0, [])] := by
  decide +kernel

/-- The idle ranks of the schedule are those of `BitOccurrences`. -/
theorem windows_ranks : (windows (schedule 4)).map (·.2.1) = idleRanks 4 := by
  decide +kernel

/-- Each idle rank is seven coordinates per stage of its window. -/
theorem idle_rank_window : ∀ w ∈ windows (schedule 4), w.2.1 = 7 * w.2.2.length := by
  decide +kernel

/-- Every stage that the frozen selection hosts into an idle lies in that idle's window. -/
theorem selection_in_windows :
    ∀ e ∈ stageCounts, e.2.2.1 ∈ ((windows (schedule 4)).getD e.1 (0, 0, [])).2.2 := by
  decide +kernel

def isSweep : Entry → Bool
  | .sweep _ _ => true
  | _ => false

/-- The schedule has the nine sweeps of the recipe. -/
theorem schedule_sweeps : (schedule 4).countP isSweep = 9 := by
  decide +kernel

/-! ### The child list -/

/-- The hosted remainders of idle `i` on its `2V` copy positions. -/
def remaindersOf (i : ℕ) : List ℕ :=
  (patterns.filter (·.1 = i)).flatMap fun p => List.replicate p.2.2 ((idleRanks 4).getD i 0 - p.2.1.sum)

theorem remainders_split : remainders = (List.range 10).flatMap remaindersOf := by
  decide +kernel

/-- The node's children in schedule order: the 32 local invocations of each sweep, then each
idle's remainders in each of the 32 replicas. -/
noncomputable def nodeChildren : List ℕ :=
  ((schedule 4).flatMap fun e => if isSweep e then (List.replicate 32 Geometry.Moves.localPaid).flatten
    else []) ++
  (List.range 10).flatMap fun i => (List.replicate 32 (remaindersOf i)).flatten

theorem sum_flatMap {α : Type*} (l : List α) (f : α → List ℕ) (price : ℕ → ℕ) :
    ((l.flatMap f).map price).sum = (l.map fun x => ((f x).map price).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_flatMap_ite {α : Type*} (l : List α) (q : α → Bool) (X : List ℕ) (price : ℕ → ℕ) :
    ((l.flatMap fun e => if q e then X else []).map price).sum = l.countP q * (X.map price).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.countP_cons]
    by_cases h : q e <;> simp [h] <;> ring

theorem sum_replicate_flatten (n : ℕ) (X : List ℕ) (price : ℕ → ℕ) :
    (((List.replicate n X).flatten).map price).sum = n * (X.map price).sum := by
  rw [List.map_flatten, List.sum_flatten, List.map_replicate, List.map_replicate, List.sum_replicate,
    smul_eq_mul]

/-- The node's child list realizes the selected bit histogram. -/
theorem nodeChildren_realizes : Realizes nodeChildren bitHistogram := by
  apply realizes_of_cost
  intro price
  have hnine := (nineRanks_realizes.map price).sum_eq
  rw [sum_map_expand] at hnine
  simp only [smul_eq_mul] at hnine
  rw [← hnine, nodeChildren, nineRanks, List.map_append, List.sum_append, List.map_append,
    List.sum_append, sum_flatMap_ite, schedule_sweeps, sum_flatMap, sum_replicate_flatten,
    sum_replicate_flatten, sum_replicate_flatten, remainders_split, sum_flatMap]
  simp only [sum_replicate_flatten, List.sum_map_mul_left]
  ring

end IntegerMultBounds.MathlibTM2.M6.BitSchedule
