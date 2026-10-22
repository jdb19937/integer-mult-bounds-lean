module

public import IntegerMultBounds.MathlibTM2.M8.Global.BlockTraceB

/-! Exact target-wire traces. A readout visits a target at most once, so its
frame appears precisely when the target belongs to that readout. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

private theorem flatMap_singletons {α β : Type*} (xs : List α) (p : α → Bool)
    (f : α → β) :
    (xs.flatMap fun a => bif p a then [f a] else []) = (xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.flatMap_cons, ih]
    cases h : p a <;> simp [h]

theorem readGate_target_trace (ts : List Nat) (hnd : ts.Nodup) (src : LW)
    (F : LMat) (t : Nat) (hsrc : (.inl (.y t) : LW) ≠ src) :
    fseq (.inl (.y t))
      (ts.map fun i => single (ReversibleFanout.add (.inl (.y i)) src) F).flatten =
      if t ∈ ts then [F] else [] := by
  rw [fseq_flatten, fseq_singles]
  have he : (ts.filter fun i => decide
      ((.inl (.y t) : LW) ∈ FramedCircuit.touched (ReversibleFanout.add (.inl (.y i)) src))) =
      ts.filter (· = t) := by
    apply List.filter_congr
    intro i _
    simp [mem_touched_add, hsrc, eq_comm]
  rw [he, List.filter_eq, List.map_replicate]
  by_cases ht : t ∈ ts
  · simp [ht, List.count_eq_one_of_mem hnd ht]
  · simp [ht, List.count_eq_zero_of_not_mem ht]

theorem readout_target_trace (F : FrameAssignment) (s t : Nat) :
    fseq (.inl (.y t))
      ((dagB.readout targets leafCount s).map fun g => single (gL g) (F.sigma s)).flatten =
      if t < leafCount ∧ dagB.cov targets s t = 1 then [F.sigma s] else [] := by
  have h := readGate_target_trace
    ((List.range leafCount).filter fun i => dagB.cov targets s i = 1)
    (List.nodup_range.filter _) (.inl (.aux s)) (F.sigma s) t (by simp)
  simpa only [Dag.readout, List.map_map, gL_add, Function.comp_def,
    List.mem_filter, List.mem_range, decide_eq_true_eq] using h

/-- Deferred readout order is retained exactly, without compressing equal frames. -/
theorem readBlocks_target_trace (F : FrameAssignment) (ss : List Nat) (t : Nat) :
    fseq (.inl (.y t)) (readBlocks F ss).flatten =
      (ss.filter fun s => decide (t < leafCount ∧ dagB.cov targets s t = 1)).map F.sigma := by
  rw [fseq_flatten, readBlocks, List.flatMap_assoc]
  have he (s : Nat) :
      (((dagB.readout targets leafCount s).map fun g => single (gL g) (F.sigma s)).flatMap
        (fseq (.inl (.y t)))) =
      if t < leafCount ∧ dagB.cov targets s t = 1 then [F.sigma s] else [] := by
    rw [← fseq_flatten]
    exact readout_target_trace F s t
  simp_rw [he]
  simpa only [Bool.cond_decide] using flatMap_singletons ss
    (fun s => decide (t < leafCount ∧ dagB.cov targets s t = 1)) F.sigma

theorem outBlocks_target_trace (F : FrameAssignment) (t : Nat) :
    fseq (.inl (.y t)) (outBlocks F).flatten =
      (outputRoots.filter fun j => decide (t ∈ targets j)).map F.output := by
  rw [fseq_flatten, outBlocks, List.flatMap_assoc]
  have he (j : Nat) :
      (((targets j).map fun i => single
        (gL (ReversibleFanout.add (.y i) (.aux (dagB.compile.pend (.root j)))) ) (F.output j)).flatMap
        (fseq (.inl (.y t)))) = if t ∈ targets j then [F.output j] else [] := by
    rw [← fseq_flatten]
    simpa only [gL_add] using readGate_target_trace (targets j) (targets_nodup j)
      (.inl (.aux (dagB.compile.pend (.root j)))) (F.output j) t (by simp)
  simp_rw [he]
  simpa only [Bool.cond_decide] using flatMap_singletons outputRoots
    (fun j => decide (t ∈ targets j)) F.output

theorem centreBlockAt_target_trace (slots : Fin 23 → Nat) (reads : Fin 23 → List Nat)
    (c : Fin 23) (hnd : (reads c).Nodup) (t : Nat) :
    fseq (.inl (.y t)) (centreBlockAt slots reads c) =
      if t ∈ reads c then [0] else [] := by
  rw [centreBlockAt, fseq_cons]
  simp only [mem_touched_add, Sum.inl.injEq, reduceCtorEq, or_self, ite_false]
  have h := readGate_target_trace (reads c) hnd (.inr c) 0 t (by simp)
  simpa only [single, ← List.flatMap_def, ← List.map_eq_flatMap] using h

theorem centres_target_trace (t : Nat) :
    fseq (.inl (.y t))
      ((List.finRange 23).map (centreBlockAt centreSlots centreTargets)).flatten =
      ((List.finRange 23).filter fun c => decide (t ∈ centreTargets c)).map (fun _ => 0) := by
  rw [fseq_flatten, List.flatMap_map]
  have he (c : Fin 23) : fseq (.inl (.y t)) (centreBlockAt centreSlots centreTargets c) =
      if t ∈ centreTargets c then [0] else [] :=
    centreBlockAt_target_trace centreSlots centreTargets c (targets_nodup (3 * leafCount + c.val)) t
  simp_rw [he]
  simpa only [Bool.cond_decide] using flatMap_singletons (List.finRange 23)
    (fun c => decide (t ∈ centreTargets c)) (fun _ => (0 : LMat))

/-- The full target trace consists of early readouts, centre scatters, deferred
readouts and final output reads; compiler gates never touch a target. -/
theorem stage_target_trace (F : FrameAssignment) (t : Nat) :
    fseq (.inl (.y t)) (stage F) =
      (nowSlots.filter fun s => decide (t < leafCount ∧ dagB.cov targets s t = 1)).map F.sigma ++
      ((List.finRange 23).filter fun c => decide (t ∈ centreTargets c)).map (fun _ => 0) ++
      ((lateSlots F.readoutOrder).filter fun s =>
        decide (t < leafCount ∧ dagB.cov targets s t = 1)).map F.sigma ++
      (outputRoots.filter fun j => decide (t ∈ targets j)).map F.output := by
  simp only [stage, blocks, preBlocks, postBlocks, List.flatten_append, fseq_append,
    fseq_opBlocks_y, readBlocks_target_trace, centres_target_trace, outBlocks_target_trace,
    List.append_nil, List.nil_append, List.append_assoc]

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
