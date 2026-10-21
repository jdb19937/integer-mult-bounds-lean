module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeCost

/-!
# Moments of the move ranks

Stage 2 replaces the rank-one children of a move by one child of the move's rank, so its cost
needs every moment `Σ φ (rank)` over the moves, not only their total rank. Each move of an
aligned list is a move along one wire's frame sequence, so the moment of the list is the sum,
over the wires, of the moments of their frame sequences (`edgeMoment_autoSteps`); with the sinks
the node's moment is the sum of the wire moments (`edgeMoment_node`). A move between equal
frames is no move; between distinct frames it has the rank of their difference (`moveRank`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical

variable {ι : Type} [DecidableEq ι] {d : ℕ} {M : Type} [AddCommMonoid M]

/-- The moment of the moves of a framed list: `φ` of each move's rank. -/
def edgeMoment (φ : ℕ → M) : List (FStep ι d) → M
  | [] => 0
  | .up _ A B :: rest => φ (B - A).rank + edgeMoment φ rest
  | .down _ A B :: rest => φ (A - B).rank + edgeMoment φ rest
  | _ :: rest => edgeMoment φ rest

omit [DecidableEq ι] in
theorem edgeMoment_append (φ : ℕ → M) : ∀ (a b : List (FStep ι d)),
    edgeMoment φ (a ++ b) = edgeMoment φ a + edgeMoment φ b
  | [], _ => by simp [edgeMoment]
  | s :: a, b => by
    cases s <;> simp [edgeMoment, edgeMoment_append φ a b, add_assoc]

/-- One step of a frame sequence: no move between equal frames. -/
def stepMoment (φ : ℕ → M) (A B : Mat d) : M := if A = B then 0 else φ (moveRank A B)

/-- The moment of the moves along a frame sequence. -/
def chainMoment (φ : ℕ → M) : List (Mat d) → M
  | a :: b :: l => stepMoment φ a b + chainMoment φ (b :: l)
  | _ => 0

omit [DecidableEq ι] in
theorem edgeMoment_move (φ : ℕ → M) (i : ι) (A B : Mat d) :
    edgeMoment φ (move i A B) = stepMoment φ A B := by
  unfold move stepMoment moveRank
  split_ifs <;> simp [edgeMoment]

theorem edgeMoment_alignMoves (φ : ℕ → M) (F : Mat d) :
    ∀ (ws : List ι) (cur : ι → Mat d), ws.Nodup →
      edgeMoment φ (alignMoves cur ws F) = (ws.map fun w => stepMoment φ (cur w) F).sum
  | [], _, _ => by simp [alignMoves, edgeMoment]
  | w :: ws, cur, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [alignMoves]
    rw [edgeMoment_append, edgeMoment_move, edgeMoment_alignMoves φ F ws _ hnd.2, List.map_cons,
      List.sum_cons]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro w' hw'
    have hne : w' ≠ w := fun h => hnd.1 (by rw [← h]; exact hw')
    rw [Function.update_of_ne hne]

/-- **Moments as wire sums.** -/
theorem edgeMoment_autoSteps (φ : ℕ → M) (W0 : Finset ι) :
    ∀ (L : List (FGate ι d)) (cur : ι → Mat d), GatesOk L →
      (∀ v ∈ L, ∀ w ∈ FramedCircuit.touched v.gate, w ∈ W0) →
        edgeMoment φ (autoSteps cur L) = ∑ w ∈ W0, chainMoment φ (cur w :: fseq w L)
  | [], cur, _, _ => by simp [autoSteps, edgeMoment, fseq, chainMoment]
  | v :: rest, cur, hg, hW => by
    have hnd := touched_nodup (hg v (by simp)).2
    have ih := edgeMoment_autoSteps φ W0 rest (setF cur (FramedCircuit.touched v.gate) v.frame)
      (fun v' hv' => hg v' (List.mem_cons_of_mem _ hv'))
      (fun v' hv' => hW v' (List.mem_cons_of_mem _ hv'))
    simp only [autoSteps]
    rw [edgeMoment_append, edgeMoment_append, edgeMoment_alignMoves φ _ _ _ hnd, ih]
    simp only [edgeMoment, add_zero]
    have hsplit : ∀ w, chainMoment φ (cur w :: fseq w (v :: rest)) =
        (if w ∈ FramedCircuit.touched v.gate then stepMoment φ (cur w) v.frame else 0) +
          chainMoment φ (setF cur (FramedCircuit.touched v.gate) v.frame w :: fseq w rest) := by
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

/-- The moment along a wire, with its sink. -/
def wireMoment (φ : ℕ → M) (w : Wire) : M :=
  chainMoment φ (gInit w :: fseq w allGates) +
    if w ∈ sideWires then stepMoment φ (lastFrame w) 1 else 0

/-- **Moments of an aligned list with sinks**, as a sum over the wires. -/
theorem moment_sinks {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ℕ → M) (L : List (FGate ι d))
    (cur : ι → Mat d) (hg : GatesOk L) (hc : ChainOk cur L) {ws : List ι} (hnd : ws.Nodup)
    [DecidablePred (· ∈ ws)] :
    edgeMoment φ (autoSteps cur L ++ alignMoves (finalFrames (autoSteps cur L) cur) ws 1) =
      ∑ w, (chainMoment φ (cur w :: fseq w L) +
        if w ∈ ws then stepMoment φ ((fseq w L).getLast?.getD (cur w)) 1 else 0) := by
  rw [edgeMoment_append,
    edgeMoment_autoSteps φ Finset.univ L cur hg (fun _ _ _ _ => Finset.mem_univ _),
    edgeMoment_alignMoves φ _ _ _ hnd, (valid_autoSteps L cur (fun _ => False) hg hc).2,
    Finset.sum_add_distrib, ← List.sum_toFinset _ hnd, ← Finset.sum_filter]
  congr 2
  ext w
  simp

/-- **The node's moment** is the sum of the wire moments. -/
theorem edgeMoment_node (φ : ℕ → M) : edgeMoment φ framedNode = ∑ w, wireMoment φ w := by
  rw [framedNode, sinks]
  exact moment_sinks φ allGates gInit gatesOk_node chainOk_node sideWires_nodup

end

end IntegerMultBounds.MathlibTM2.M8.Global
