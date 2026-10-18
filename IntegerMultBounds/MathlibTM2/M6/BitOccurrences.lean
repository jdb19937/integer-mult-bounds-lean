module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Moves.Profile
public import IntegerMultBounds.MathlibTM2.Layer.SelectedMoments

/-!
# The nine-stage PR589 occurrence list

The selected bit bill `SelectedMoments.bit_bill_le` prices the selected word on its nine-stage
hosted pipeline: PR #510's chain with `L = 9` stages, `T = 32` replicas, `V = 111` live ports and
`R = 439` helpers, parent width `m = 1 + 7L = 64` and live stock `W = 2·4·V·T = 28416` (upstream
`research/e8-bit-p111-tuned`, scripts `global_k.py` and `audit_hosted_k.py` under `vendor/pr510`).
Its child occurrences are
* the local paid ranks `Moves.localPaid` of each of the `L·T = 288` local invocations, certified
  from the frame replay and the label dimensions, and
* the hosted idle remainders: on each of the `2V = 222` copy positions of each positive-rank idle
  of the schedule, and in each replica, the idle rank minus the residual widths that the frozen
  selection `data/selection9-p111.json` hosts there.

`nineRanks_realizes` proves that this list realizes `bitHistogram`, so `nine_moment_le` is the
selected bit bill with no open occurrence link. The windows of the hosted slots and the
physical hosting itself are not checked here.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitOccurrences

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.MathlibTM2.Layer.SelectedMoments

/-! ### The schedule and the frozen selection -/

/-- Idle ranks of the `2K+1`-stage schedule in schedule order (`global_k.py`): after the local
sweep of stage `s`, an odd `s ≤ 2K-3` idles one pair at rank `7(s+1)`, an even
`2 ≤ s ≤ 2K-2` idles one pair at rank `7`, and `s = 2K` idles each pair `j` at rank
`7(2K-(2j+2))`. -/
def idleRanks (K : ℕ) : List ℕ :=
  (List.range (2 * K)).flatMap fun t =>
    if (t + 1) % 2 = 1 ∧ t + 1 ≤ 2 * K - 3 then [7 * (t + 2)]
    else if (t + 1) % 2 = 0 ∧ 2 ≤ t + 1 ∧ t + 1 ≤ 2 * K - 2 then [7]
    else if t + 1 = 2 * K then (List.range K).map fun j => 7 * (2 * K - (2 * j + 2))
    else []

theorem idleRanks_four : idleRanks 4 = [14, 7, 28, 7, 42, 7, 42, 28, 14, 0] := by
  decide +kernel

/-- `selection9-p111.json`, `patterns`: an idle index, the residual widths hosted on one copy
position, and the number of copy positions carrying that pattern. -/
def patterns : List (ℕ × List ℕ × ℕ) :=
  [(0, [8], 222), (1, [], 222), (2, [8, 8, 8], 222), (3, [], 222), (4, [8, 8, 8, 8, 8], 222),
   (5, [], 222), (6, [], 9), (6, [8, 8, 8, 8, 8], 213), (7, [8, 8, 8], 222), (8, [8], 222)]

/-- `selection9-p111.json`, `stages`: an idle index, a residual width, the source stage and the
number of that stage's helpers hosted into the idle. -/
def stageCounts : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 8, 1, 222), (2, 8, 0, 439), (2, 8, 1, 217), (2, 8, 2, 10), (4, 8, 2, 429), (4, 8, 4, 252),
   (4, 8, 5, 429), (6, 8, 3, 439), (6, 8, 4, 187), (6, 8, 7, 439), (7, 8, 5, 10), (7, 8, 6, 439),
   (7, 8, 8, 217), (8, 8, 8, 222)]

/-- Each of the nine positive-rank idles is covered on all `2V = 222` copy positions. -/
theorem patterns_cover : ∀ i < 9, ((patterns.filter (·.1 = i)).map (·.2.2)).sum = 222 := by
  decide +kernel

/-- The hosted widths of every pattern fit inside its idle rank. -/
theorem patterns_fit : ∀ p ∈ patterns, p.2.1.sum ≤ (idleRanks 4).getD p.1 0 := by
  decide +kernel

/-- The patterns host into each idle exactly the residuals that the stage counts list. -/
theorem patterns_stageCounts : ∀ i < 9,
    ((patterns.filter (·.1 = i)).map fun p => p.2.2 * p.2.1.length).sum =
      ((stageCounts.filter (·.1 = i)).map (·.2.2.2)).sum := by
  decide +kernel

/-- Every one of the `R = 439` helpers of every stage is hosted. -/
theorem stageCounts_all : ∀ s < 9, ((stageCounts.filter (·.2.2.1 = s)).map (·.2.2.2)).sum = 439 := by
  decide +kernel

/-- Every hosted residual has width eight. -/
theorem widths_eight : (∀ p ∈ patterns, ∀ w ∈ p.2.1, w = 8) ∧ ∀ e ∈ stageCounts, e.2.1 = 8 := by
  decide +kernel

/-- Every helper starts at a zero-dimensional frame, so its residual width `8 - dim` is eight. -/
theorem helper_width : ∀ h < 439, 8 - Geometry.Dimensions.value (Frames.initialRefs (222 + h)) = 8 := by
  decide +kernel

/-! ### The occurrence list -/

/-- The hosted idle remainders of one replica, one per copy position. -/
def remainders : List ℕ :=
  patterns.flatMap fun p => List.replicate p.2.2 ((idleRanks 4).getD p.1 0 - p.2.1.sum)

def remainderHist : List (ℕ × ℕ) :=
  [(6, 222), (7, 222), (4, 222), (7, 222), (2, 222), (7, 222), (42, 9), (2, 213), (4, 222),
   (6, 222)]

theorem remainders_eq : remainders = expand remainderHist := by
  decide +kernel

/-- The positive phase ranks, as a histogram. -/
def phaseHist : List (ℕ × ℕ) := [(1, 1323), (2, 1342), (3, 79), (4, 44), (5, 102), (6, 11), (7, 10)]

/-- Two lists bounded by `N` with the same counts below `N` are permutations of each other. -/
theorem perm_of_counts (l₁ l₂ : List ℕ) (N : ℕ) (h₁ : ∀ x ∈ l₁, x < N) (h₂ : ∀ x ∈ l₂, x < N)
    (hc : (List.range N).map l₁.count = (List.range N).map l₂.count) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro a
  by_cases ha : a < N
  · have h := congrArg (fun L : List ℕ => L[a]?) hc
    simpa only [List.getElem?_map, List.getElem?_range ha, Option.map_some, Option.some.injEq]
      using h
  · rw [List.count_eq_zero.mpr fun h => ha (h₁ a h), List.count_eq_zero.mpr fun h => ha (h₂ a h)]

theorem phase_perm : (Geometry.Moves.phaseValues.filter (· ≠ 0)).Perm (expand phaseHist) :=
  perm_of_counts _ _ 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The local paid histogram, `word.local_histogram` of the tuned word. -/
def localHist : List (ℕ × ℕ) := [(1, 1323), (2, 1342), (3, 79), (4, 44), (5, 102), (6, 11), (7, 19)]

theorem localPaid_realizes : Realizes Geometry.Moves.localPaid localHist := by
  rw [Realizes, Geometry.Moves.localPaid, Geometry.Moves.phase_ranks, Geometry.Moves.copyRanks_eq]
  have h : expand localHist = expand phaseHist ++ List.replicate 9 7 := by decide +kernel
  rw [h]
  exact phase_perm.append_right _

/-- The nine-stage occurrence list: the local paid ranks of each of the `9·32` local invocations,
then each replica's hosted idle remainders. -/
noncomputable def nineRanks : List ℕ :=
  (List.replicate (9 * 32) Geometry.Moves.localPaid).flatten ++ (List.replicate 32 remainders).flatten

/-- The nine-stage occurrence list realizes the selected bit histogram. -/
theorem nineRanks_realizes : Realizes nineRanks bitHistogram := by
  apply realizes_of_cost
  intro price
  have hl : (Geometry.Moves.localPaid.map price).sum = (localHist.map fun e => e.2 * price e.1).sum := by
    rw [(localPaid_realizes.map price).sum_eq, sum_map_expand]
    simp only [smul_eq_mul]
  have hr : (remainders.map price).sum = (remainderHist.map fun e => e.2 * price e.1).sum := by
    rw [remainders_eq, sum_map_expand]
    simp only [smul_eq_mul]
  simp only [nineRanks, List.map_append, List.sum_append, List.map_flatten, List.sum_flatten,
    List.map_replicate, List.sum_replicate, smul_eq_mul, hl, hr]
  simp only [localHist, remainderHist, bitHistogram, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ring

/-- The live stock and parent width of the nine-stage pipeline. -/
theorem stock : 2 * 4 * 111 * 32 = 28416 ∧ 1 + 7 * 9 = 64 := by norm_num

/-- The selected bit bill on the nine-stage occurrence list, with no open link. -/
theorem nine_moment_le :
    ∑ i : Fin nineRanks.length, (1 / (28416 : ℝ)) * ((nineRanks[i.1] : ℝ) / 64) ^ (1 - bitSaving) ≤
      1 - surcharge bitHistogram 64 (1 - bitSaving) / 28416 :=
  bit_occurrence_moment_le nineRanks_realizes

end IntegerMultBounds.MathlibTM2.M6.BitOccurrences
