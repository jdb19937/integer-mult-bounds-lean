module

public import IntegerMultBounds.MathlibTM2.M8.Global.Auto
public import IntegerMultBounds.MathlibTM2.M8.Exchange

/-!
# Interchange counts of aligned lists

A move between comparable frames costs the rank of their difference (`moveRank`). The
interchanges of an aligned list are the sums, over the wires, of the move costs along each wire's
frame sequence (`edgeRanks_autoSteps`). Along an increasing sequence of idempotents the costs
telescope to the rank of the last frame minus the rank of the first (`chainCost_mono`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical

variable {ι : Type} [DecidableEq ι] {d : ℕ}

/-- The cost of a move. -/
def moveRank (A B : Mat d) : ℕ := if A = B then 0 else if Le A B then (B - A).rank else (A - B).rank

/-- The cost of a frame sequence. -/
def chainCost : List (Mat d) → ℕ
  | a :: b :: l => moveRank a b + chainCost (b :: l)
  | _ => 0

omit [DecidableEq ι] in
theorem edgeRanks_move (i : ι) (A B : Mat d) : edgeRanks (move i A B) = moveRank A B := by
  unfold move moveRank
  split_ifs <;> simp [edgeRanks]

theorem edgeRanks_alignMoves (F : Mat d) :
    ∀ (ws : List ι) (cur : ι → Mat d), ws.Nodup →
      edgeRanks (alignMoves cur ws F) = (ws.map fun w => moveRank (cur w) F).sum
  | [], _, _ => rfl
  | w :: ws, cur, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [alignMoves]
    rw [edgeRanks_append, edgeRanks_move, edgeRanks_alignMoves F ws _ hnd.2, List.map_cons,
      List.sum_cons]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro w' hw'
    have hne : w' ≠ w := fun h => hnd.1 (by rw [← h]; exact hw')
    rw [Function.update_of_ne hne]

theorem chainCost_cons_cons (a b : Mat d) (l : List (Mat d)) :
    chainCost (a :: b :: l) = moveRank a b + chainCost (b :: l) := rfl

/-- **Interchanges as wire sums.** -/
theorem edgeRanks_autoSteps (W0 : Finset ι) :
    ∀ (L : List (FGate ι d)) (cur : ι → Mat d), GatesOk L →
      (∀ v ∈ L, ∀ w ∈ FramedCircuit.touched v.gate, w ∈ W0) →
        edgeRanks (autoSteps cur L) = ∑ w ∈ W0, chainCost (cur w :: fseq w L)
  | [], cur, _, _ => by simp [autoSteps, edgeRanks, fseq, chainCost]
  | v :: rest, cur, hg, hW => by
    have hnd := touched_nodup (hg v (by simp)).2
    have ih := edgeRanks_autoSteps W0 rest (setF cur (FramedCircuit.touched v.gate) v.frame)
      (fun v' hv' => hg v' (List.mem_cons_of_mem _ hv'))
      (fun v' hv' => hW v' (List.mem_cons_of_mem _ hv'))
    simp only [autoSteps]
    rw [edgeRanks_append, edgeRanks_append, edgeRanks_alignMoves _ _ _ hnd, ih]
    simp only [edgeRanks, add_zero]
    have hsplit : ∀ w, chainCost (cur w :: fseq w (v :: rest)) =
        (if w ∈ FramedCircuit.touched v.gate then moveRank (cur w) v.frame else 0) +
          chainCost (setF cur (FramedCircuit.touched v.gate) v.frame w :: fseq w rest) := by
      intro w
      rw [fseq_cons]
      simp only [setF]
      split_ifs with h
      · rfl
      · simp
    rw [Finset.sum_congr rfl fun w _ => hsplit w, Finset.sum_add_distrib, Finset.sum_ite,
      Finset.sum_const_zero, add_zero]
    congr 1
    rw [← List.sum_toFinset _ hnd]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext w
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun h => ⟨hW v (by simp) w h, h⟩, fun h => h.2⟩

/-- The rank of a nested difference. -/
theorem rank_sub_of_le {A B : Mat d} (hA : A * A = A) (hB : B * B = B) (h : Le A B) :
    (B - A).rank + A.rank = B.rank :=
  Exchange.rank_sub_add A B hA hB h.1 h.2

theorem moveRank_le {A B : Mat d} (hA : A * A = A) (hB : B * B = B) (h : Le A B) :
    moveRank A B + A.rank = B.rank := by
  unfold moveRank
  by_cases hab : A = B
  · subst hab; simp
  · rw [ite_eq_right hab, ite_eq_left h]
    exact rank_sub_of_le hA hB h

/-- **Telescoping.** Along an increasing sequence of idempotents the costs add up to the rise in
rank. -/
theorem chainCost_mono : ∀ (l : List (Mat d)) (a : Mat d), (a :: l).IsChain Le →
    (∀ x ∈ a :: l, x * x = x) → chainCost (a :: l) + a.rank = ((a :: l).getLast (by simp)).rank
  | [], a, _, _ => by simp [chainCost]
  | b :: l, a, hc, hid => by
    rw [List.isChain_cons_cons] at hc
    rw [chainCost_cons_cons, add_comm (moveRank a b), add_assoc,
      moveRank_le (hid a (by simp)) (hid b (by simp)) hc.1,
      chainCost_mono l b hc.2 (fun x hx => hid x (List.mem_cons_of_mem _ hx))]
    simp

end

end IntegerMultBounds.MathlibTM2.M8.Global
