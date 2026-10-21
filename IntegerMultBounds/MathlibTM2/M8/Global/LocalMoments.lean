module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeMoments
public import IntegerMultBounds.MathlibTM2.M8.Local.SlotMoments
import Mathlib.Tactic.Abel

/-!
# The moments of the side slots' local chains

A side slot's local chain is `0`, the frames of the compiled operations touching it, the read
frame of the root it serves (if any), and `1`: the first pass at frame `0` and the uncompute at
frame `1` make no moves (`localMoment_root`, `localMoment_free`). Summing over the slots
(`sum_localMoment`), the compiled frames give the moves along the slots, which `SlotMoments`
writes node by node, and the ends give the last frame of every slot, which a telescoping cost
writes node by node as well; the roots add their read frames.

Between nested frames a move's moment is a function of the two ranks (`stepMoment_rank`), so the
whole sum is a combination of `φ` at rank differences of node frames (`sum_localMoment_ranks`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-! ### Chain algebra -/

section Chains
variable {d : ℕ} {M : Type} [AddCommMonoid M]

theorem chainMoment_split (φ : ℕ → M) : ∀ (pre : List (Mat d)) (a : Mat d) (X : List (Mat d)),
    chainMoment φ (pre ++ a :: X) = chainMoment φ (pre ++ [a]) + chainMoment φ (a :: X)
  | [], a, X => by simp [chainMoment]
  | [p], a, X => by simp [chainMoment]
  | p :: q :: pre, a, X => by
    have ih := chainMoment_split φ (q :: pre) a X
    simp only [List.cons_append] at ih ⊢
    rw [chainMoment_cons_cons, ih, chainMoment_cons_cons, add_assoc]

theorem chainMoment_const_tail (φ : ℕ → M) (a : Mat d) :
    ∀ (L X : List (Mat d)), (∀ x ∈ L, x = a) → chainMoment φ (a :: (L ++ X)) = chainMoment φ (a :: X)
  | [], _, _ => rfl
  | x :: L, X, h => by
    rw [h x (by simp), List.cons_append, chainMoment_cons_cons, stepMoment, ite_eq_left rfl,
      zero_add]
    exact chainMoment_const_tail φ a L X (fun y hy => h y (by simp [hy]))

theorem chainMoment_dedup (φ : ℕ → M) (pre : List (Mat d)) (a : Mat d) (L X : List (Mat d))
    (h : ∀ x ∈ L, x = a) : chainMoment φ (pre ++ a :: (L ++ X)) = chainMoment φ (pre ++ a :: X) := by
  rw [chainMoment_split, chainMoment_split φ pre a X, chainMoment_const_tail φ a L X h]

theorem append_const_comm {α : Type*} {a : α} : ∀ (L : List α), (∀ x ∈ L, x = a) → L ++ [a] = a :: L
  | [], _ => rfl
  | x :: L, h => by
    rw [h x (by simp), List.cons_append, append_const_comm L (fun y hy => h y (by simp [hy]))]

theorem chainMoment_const_one (φ : ℕ → M) (a : Mat d) (L : List (Mat d)) (h : ∀ x ∈ L, x = a) :
    chainMoment φ (a :: L) = 0 := by
  have := chainMoment_const_tail φ a L [] h
  simpa [chainMoment] using this

end Chains

/-! ### One slot -/

/-- The read frame of root `j`. -/
def readFrame (j : ℕ) : LMat :=
  if j < 3 * leafCount then hyperFrame (leafTriple (j / 3)) else starFrame (j - 3 * leafCount)

/-- The compiled frames along slot `s`. -/
abbrev slotFrames (s : ℕ) : List LMat := (nodesOf s dag.compile.ops).map nodeFrame

theorem mo_frames (s : ℕ) : ∀ f ∈ centreBlocks.flatMap (fseq (.inl (.aux s))) ++
    outputBlocks.flatMap (fseq (.inl (.aux s))), ∃ j < rootCount, slotOf j = s ∧ f = readFrame j := by
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · obtain ⟨c, hs, rfl⟩ := fseqM_aux s f h
    refine ⟨3 * leafCount + c, centre_root_lt c, hs.symm, ?_⟩
    have hn : ¬ 3 * leafCount + (c : ℕ) < 3 * leafCount := Nat.not_lt.mpr (Nat.le_add_right _ _)
    rw [readFrame, ite_eq_right_iff.mpr (fun h => absurd h hn), Nat.add_sub_cancel_left]
  · obtain ⟨j, hj, hs, rfl⟩ := fseqO_aux s f h
    exact ⟨j, out_root_lt hj, hs.symm, by rw [readFrame, ite_eq_left_iff.mpr (fun h => absurd hj h)]⟩

theorem localMoment_blocks {M : Type} [AddCommMonoid M] (φ : ℕ → M) (s : ℕ) :
    localMoment φ s = chainMoment φ ((0 : LMat) :: (slotFrames s ++
      ((centreBlocks.flatMap (fseq (.inl (.aux s))) ++ outputBlocks.flatMap (fseq (.inl (.aux s)))) ++
        (uncomputeBlocks.flatMap (fseq (.inl (.aux s))) ++ [1])))) := by
  have hP := fseqP_zero (.inl (.aux s))
  rw [localMoment, fseq_stage1, fseqC_aux, slotFrames]
  generalize pass1Blocks.flatMap (fseq (.inl (.aux s))) = P at hP ⊢
  generalize centreBlocks.flatMap (fseq (.inl (.aux s))) = Mb
  generalize outputBlocks.flatMap (fseq (.inl (.aux s))) = Ob
  generalize uncomputeBlocks.flatMap (fseq (.inl (.aux s))) = U
  generalize (nodesOf s dag.compile.ops).map nodeFrame = C
  have := chainMoment_const_tail φ (0 : LMat) P (C ++ (Mb ++ (Ob ++ (U ++ [1])))) hP
  simp only [List.append_assoc] at this ⊢
  exact this

/-- A slot that serves root `j`: the compiled frames, the read frame, then `1`. -/
theorem localMoment_root {M : Type} [AddCommMonoid M] (φ : ℕ → M) {s j : ℕ} (hj : j < rootCount)
    (hs : slotOf j = s) :
    localMoment φ s = chainMoment φ ((0 : LMat) :: (slotFrames s ++ [readFrame j, 1])) := by
  -- the read frame is on the slot's read blocks
  have hmem : readFrame j ∈ centreBlocks.flatMap (fseq (.inl (.aux s))) ++
      outputBlocks.flatMap (fseq (.inl (.aux s))) := by
    by_cases hjo : j < 3 * leafCount
    · refine List.mem_append_right _ ?_
      rw [readFrame, ite_eq_left_iff.mpr (fun h => absurd hjo h), outputBlocks, fseq_singles,
        mem_map_filter]
      exact ⟨j, List.mem_range.mpr hjo, decide_eq_true ((mem_touched_add _ _ _).mpr
        (Or.inr (by rw [hs]))), rfl⟩
    · have hc : j - 3 * leafCount < 23 := by
        have h1 : j < rootCount := hj
        have h2 : rootCount = 3 * leafCount + 23 := rfl
        omega
      refine List.mem_append_left _ ?_
      rw [readFrame, ite_eq_right_iff.mpr (fun h => absurd h hjo), centreBlocks, List.mem_flatMap]
      refine ⟨centreBlock ⟨j - 3 * leafCount, hc⟩, List.mem_map_of_mem (List.mem_finRange _), ?_⟩
      rw [fseq_centreBlock]
      have he : 3 * leafCount + (j - 3 * leafCount) = j := Nat.add_sub_cancel' (Nat.le_of_not_lt hjo)
      have hw : (.inl (.aux s) : LW) = .inr ⟨j - 3 * leafCount, hc⟩ ∨
          (.inl (.aux s) : LW) = .inl (.aux (slotOf (3 * leafCount + (⟨j - 3 * leafCount, hc⟩ : Fin 23)))) :=
        Or.inr (by rw [show (3 * leafCount + (⟨j - 3 * leafCount, hc⟩ : Fin 23).val) = j from he, hs])
      rw [ite_eq_left_iff.mpr (fun h => absurd hw h)]
      exact List.mem_append_left _ (List.mem_singleton_self _)
  have hMO : ∀ f ∈ centreBlocks.flatMap (fseq (.inl (.aux s))) ++
      outputBlocks.flatMap (fseq (.inl (.aux s))), f = readFrame j := by
    intro f hf
    obtain ⟨j', hj', hs', rfl⟩ := mo_frames s f hf
    rw [dag.root_slot_inj dag_valid hj' hj (hs'.trans hs.symm)]
  have hU : ∀ f ∈ uncomputeBlocks.flatMap (fseq (.inl (.aux s))), f = 1 := fseqU_one _
  rw [localMoment_blocks]
  generalize centreBlocks.flatMap (fseq (.inl (.aux s))) ++
    outputBlocks.flatMap (fseq (.inl (.aux s))) = MO at hmem hMO ⊢
  generalize uncomputeBlocks.flatMap (fseq (.inl (.aux s))) = U at hU ⊢
  generalize slotFrames s = C
  generalize readFrame j = R at hmem hMO ⊢
  rw [show U ++ [1] = (1 : LMat) :: U from append_const_comm U hU]
  cases MO with
  | nil => cases hmem
  | cons f MO' =>
    have hf : f = R := hMO f (List.mem_cons_self ..)
    have hMO' : ∀ x ∈ MO', x = R := fun x hx => hMO x (List.mem_cons_of_mem _ hx)
    subst hf
    rw [List.cons_append (a := f), ← List.cons_append (a := (0 : LMat)),
      chainMoment_dedup φ _ _ MO' _ hMO',
      List.append_cons, chainMoment_split φ _ 1 U, chainMoment_const_one φ 1 U hU, add_zero,
      List.append_assoc, List.singleton_append, List.cons_append]

/-- A slot that serves no root: the compiled frames, then `1`. -/
theorem localMoment_free {M : Type} [AddCommMonoid M] (φ : ℕ → M) {s : ℕ}
    (hs : ∀ j < rootCount, slotOf j ≠ s) :
    localMoment φ s = chainMoment φ ((0 : LMat) :: (slotFrames s ++ [1])) := by
  have hMO : centreBlocks.flatMap (fseq (.inl (.aux s))) ++
      outputBlocks.flatMap (fseq (.inl (.aux s))) = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr fun f hf => ?_
    obtain ⟨j, hj, hjs, -⟩ := mo_frames s f hf
    exact hs j hj hjs
  have hU : ∀ f ∈ uncomputeBlocks.flatMap (fseq (.inl (.aux s))), f = 1 := fseqU_one _
  rw [localMoment_blocks, hMO]
  generalize uncomputeBlocks.flatMap (fseq (.inl (.aux s))) = U at hU ⊢
  generalize slotFrames s = C
  rw [List.nil_append, show U ++ [1] = (1 : LMat) :: U from append_const_comm U hU]
  rw [← List.cons_append, chainMoment_split φ _ 1 U, chainMoment_const_one φ 1 U hU, add_zero,
    List.cons_append]

/-! ### Summing over the slots -/

theorem getLast?_cons_or {α : Type*} (n : α) : ∀ l : List α, (n :: l).getLast? = l.getLast?.or (some n)
  | [] => rfl
  | m :: l => by
    rw [List.getLast?_cons_cons, getLast?_cons_or m l]
    cases l.getLast? <;> rfl

/-- A telescoping cost along a chain. -/
theorem chainC_tele {G : Type*} [AddCommGroup G] (h : Option ℕ → G) :
    ∀ (p : Option ℕ) (l : List ℕ), chainC (fun p n => h (some n) - h p) p l = h (l.getLast?.or p) - h p
  | p, [] => by rw [chainC, List.getLast?_nil, Option.none_or, sub_self]
  | p, n :: l => by
    rw [chainC, chainC_tele h (some n) l, getLast?_cons_or]
    cases l.getLast? with
    | none => rw [Option.none_or, Option.some_or, sub_self, add_zero]
    | some m => rw [Option.some_or, Option.some_or]; abel

/-- The frame after an optional node: `0` for a fresh slot. -/
def frameO : Option ℕ → LMat
  | none => 0
  | some n => nodeFrame n

/-- The moment of one move along a slot. -/
def cMove (φ : ℕ → ℝ) (p : Option ℕ) (n : ℕ) : ℝ := stepMoment φ (frameO p) (nodeFrame n)

/-- The moment of the final move of a slot from `A` to `1`. -/
def endM (φ : ℕ → ℝ) (A : LMat) : ℝ := stepMoment φ A 1

/-- The telescoping cost of the final moves. -/
def cEnd (φ : ℕ → ℝ) (p : Option ℕ) (n : ℕ) : ℝ := endM φ (frameO (some n)) - endM φ (frameO p)

/-- The correction of root `j`: through its read frame rather than straight to `1`. -/
def rootCorr (φ : ℕ → ℝ) (j : ℕ) : ℝ :=
  stepMoment φ (frameO (some (dag.rootNode j))) (readFrame j) + stepMoment φ (readFrame j) 1 -
    endM φ (frameO (some (dag.rootNode j)))

theorem or_some_or {α : Type*} (o : Option α) (n : α) (p : Option α) :
    (o.or (some n)).or p = o.or (some n) := by
  cases o <;> rfl

/-- The moves along a slot's frames, then one more move to `X`. -/
theorem chainMoment_frames (φ : ℕ → ℝ) (X : LMat) :
    ∀ (p : Option ℕ) (l : List ℕ), chainMoment φ ((frameO p :: l.map nodeFrame) ++ [X]) =
      chainC (cMove φ) p l + stepMoment φ (frameO (l.getLast?.or p)) X
  | p, [] => by
    rw [List.map_nil, List.cons_append, List.nil_append, chainMoment_cons_cons, chainC,
      List.getLast?_nil, Option.none_or, zero_add]
    exact add_zero _
  | p, n :: l => by
    have ih : chainMoment φ ((nodeFrame n :: l.map nodeFrame) ++ [X]) =
        chainC (cMove φ) (some n) l + stepMoment φ (frameO (l.getLast?.or (some n))) X :=
      chainMoment_frames φ X (some n) l
    rw [List.map_cons, List.cons_append, List.cons_append, chainMoment_cons_cons, ← List.cons_append,
      ih, chainC, getLast?_cons_or, or_some_or, add_assoc]
    rfl

theorem cMove_self (φ : ℕ → ℝ) (n : ℕ) : cMove φ (some n) n = 0 := by
  change (if nodeFrame n = nodeFrame n then (0 : ℝ) else _) = 0
  exact ite_eq_left_iff.mpr (fun h => absurd rfl h)

theorem cEnd_self (φ : ℕ → ℝ) (n : ℕ) : cEnd φ (some n) n = 0 := sub_self _

theorem lastNode_eq (s : ℕ) :
    lastNode dag.compile.ops s = (nodesOf s dag.compile.ops).getLast?.or none := by
  have hl := nodesOf_getLast (s := s) dag.compile.ops (fun _ => none)
  rw [lastNode, hl]

/-- **One slot**: its moves, its final move, and the corrections of the roots it serves. -/
theorem localMoment_slot (φ : ℕ → ℝ) {s : ℕ} :
    localMoment φ s = chainC (cMove φ) none (nodesOf s dag.compile.ops) +
      endM φ (frameO (lastNode dag.compile.ops s)) +
        ∑ j ∈ (Finset.range rootCount).filter (fun j => slotOf j = s), rootCorr φ j := by
  by_cases hr : ∃ j < rootCount, slotOf j = s
  · obtain ⟨j, hj, hs⟩ := hr
    have hfilter : (Finset.range rootCount).filter (fun j => slotOf j = s) = {j} := by
      ext j'
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hj', hs'⟩; exact dag.root_slot_inj dag_valid hj' hj (hs'.trans hs.symm)
      · rintro rfl; exact ⟨hj, hs⟩
    have hlast : lastNode dag.compile.ops s = some (dag.rootNode j) := by
      rw [← hs]; exact dag.compile_root_last dag_valid nodeLe_order hj
    rw [hfilter, Finset.sum_singleton, localMoment_root φ hj hs, hlast, ← List.cons_append,
      chainMoment_snoc]
    have h := chainMoment_frames φ (readFrame j) none (nodesOf s dag.compile.ops)
    rw [← lastNode_eq, hlast] at h
    change chainMoment φ ((frameO none :: (nodesOf s dag.compile.ops).map nodeFrame) ++ [readFrame j]) +
      stepMoment φ (readFrame j) 1 = _
    rw [h, rootCorr]
    abel
  · have hr' : ∀ j < rootCount, slotOf j ≠ s := fun j hj h => hr ⟨j, hj, h⟩
    have hfilter : (Finset.range rootCount).filter (fun j => slotOf j = s) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun j hj => hr' j (Finset.mem_range.mp hj)
    rw [hfilter, Finset.sum_empty, add_zero, localMoment_free φ hr', ← List.cons_append]
    have h := chainMoment_frames φ 1 none (nodesOf s dag.compile.ops)
    rw [← lastNode_eq] at h
    exact h

/-- **The local moments, summed over the slots.** -/
theorem sum_localMoment (φ : ℕ → ℝ) :
    ∑ s : Slot, localMoment φ s =
      Dag.slotSum (cMove φ) dag.compile + Dag.slotSum (cEnd φ) dag.compile +
        dag.compile.next • endM φ 0 + ∑ j ∈ Finset.range rootCount, rootCorr φ j := by
  rw [Fin.sum_univ_eq_sum_range (fun s => localMoment φ s)]
  have hend : ∀ s, endM φ (frameO (lastNode dag.compile.ops s)) =
      chainC (cEnd φ) none (nodesOf s dag.compile.ops) + endM φ 0 := by
    intro s
    have := chainC_tele (fun o => endM φ (frameO o)) none (nodesOf s dag.compile.ops)
    change chainC (cEnd φ) none _ = _ at this
    rw [this, lastNode_eq]
    change _ = _ - endM φ 0 + endM φ 0
    rw [sub_add_cancel]
  have hslot : ∀ s, localMoment φ s = chainC (cMove φ) none (nodesOf s dag.compile.ops) +
      chainC (cEnd φ) none (nodesOf s dag.compile.ops) + endM φ 0 +
        ∑ j ∈ (Finset.range rootCount).filter (fun j => slotOf j = s), rootCorr φ j := by
    intro s
    rw [localMoment_slot φ, hend]
    abel
  rw [Finset.sum_congr rfl fun s _ => hslot s, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  have hroots : ∑ s ∈ Finset.range dag.compile.next,
      ∑ j ∈ (Finset.range rootCount).filter (fun j => slotOf j = s), rootCorr φ j =
        ∑ j ∈ Finset.range rootCount, rootCorr φ j := by
    rw [Finset.sum_comm' (t' := Finset.range rootCount) (s' := fun j => {slotOf j})]
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_singleton _ _
    · intro s j
      rw [Finset.mem_range, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hj, h⟩; exact ⟨h.symm, hj⟩
      · rintro ⟨h, hj⟩; exact ⟨h ▸ dag.root_slot_lt dag_valid hj, hj, h.symm⟩
  rw [hroots]
  rfl

end
end IntegerMultBounds.MathlibTM2.M8.Global
