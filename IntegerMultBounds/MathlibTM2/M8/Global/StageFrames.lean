module

public import IntegerMultBounds.MathlibTM2.M8.Global.Stage

/-!
# The frames along each local wire

For every local wire, the frames of the gates touching it in the first stage, after its starting
frame (`init1`), increase (`chain1_aux`, `chain1_x`, `chain1_y`); a temporary goes from its
centre's star frame down to `0` (`fseq1_tmp`). In the second stage, every register sees the
first stage's frames in reverse order, complemented (`fseq2_reg`), and a temporary goes up from
the complement of its star frame to `1` (`fseq2_tmp`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem le_trans' {d : ℕ} {A B C : Mat d} (h1 : Le A B) (h2 : Le B C) : Le A C :=
  ⟨by rw [← h1.1, Matrix.mul_assoc, h2.1],
    by rw [show C * A = C * (B * A) by rw [h1.2], ← Matrix.mul_assoc, h2.2, h1.2]⟩

instance {d : ℕ} : @Trans (Mat d) (Mat d) (Mat d) Le Le Le := ⟨le_trans'⟩

theorem zero_le {d : ℕ} (A : Mat d) : Le 0 A := ⟨by simp, by simp⟩

theorem le_one {d : ℕ} (A : Mat d) : Le A 1 := ⟨by simp, by simp⟩

theorem le_compl {d : ℕ} {A B : Mat d} (h : Le A B) : Le (1 - B) (1 - A) := by
  refine ⟨?_, ?_⟩
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h.2]; abel
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h.1]; abel

theorem le_of_nested {A B : LMat} (h : Nested A B) : Le A B := ⟨h.2, h.1⟩

/-! ### Frame sequences -/

theorem fseq_append {ι : Type} [DecidableEq ι] (w : ι) (A B : List (FGate ι d)) :
    fseq w (A ++ B) = fseq w A ++ fseq w B := by
  simp [fseq, List.filter_append]

theorem fseq_flatten {ι : Type} [DecidableEq ι] (w : ι) (Bs : List (List (FGate ι d))) :
    fseq w Bs.flatten = Bs.flatMap (fseq w) := by
  induction Bs with
  | nil => rfl
  | cons B Bs ih => rw [List.flatten_cons, fseq_append, ih, List.flatMap_cons]

theorem fseq_single (w : LW) (g : Circuit.Gate LW (ZMod 2)) (F : LMat) :
    fseq w (single g F) = if w ∈ FramedCircuit.touched g then [F] else [] := by
  simp only [single, fseq, List.filter_cons, List.filter_nil]
  split_ifs <;> simp_all

theorem mem_touched_add {ι : Type} (a b w : ι) :
    w ∈ FramedCircuit.touched (ReversibleFanout.add a b) ↔ w = a ∨ w = b := by
  simp [FramedCircuit.touched, ReversibleFanout.add]

theorem gL_add (a b : Reg) : gL (ReversibleFanout.add a b) = ReversibleFanout.add (.inl a) (.inl b) := by
  simp [gL, gateMap, ReversibleFanout.add]

theorem opGate_add (op : Op) : ∃ a b, opGate op = ReversibleFanout.add a b ∧
    (∀ w, w = a ∨ w = b ↔ (∃ s ∈ op.slots, w = .aux s) ∨ ∃ s n, op = .src s n ∧ w = .x n) := by
  cases op with
  | src s n =>
    refine ⟨.aux s, .x n, rfl, fun w => ?_⟩
    simp only [Op.slots, List.mem_singleton, exists_eq_left, Op.src.injEq]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨s, n, ⟨rfl, rfl⟩, rfl⟩
    · rintro (rfl | ⟨_, _, ⟨rfl, rfl⟩, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr rfl
  | add p o k =>
    refine ⟨.aux p, .aux o, rfl, fun w => ?_⟩
    simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_and, exists_false, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨p, Or.inl rfl, rfl⟩
      · exact ⟨o, Or.inr rfl, rfl⟩
    · rintro ⟨s, rfl | rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
  | copy p f k =>
    refine ⟨.aux f, .aux p, rfl, fun w => ?_⟩
    simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_and, exists_false, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨f, Or.inr rfl, rfl⟩
      · exact ⟨p, Or.inl rfl, rfl⟩
    · rintro ⟨s, rfl | rfl, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl rfl

theorem aux_mem_opGate (op : Op) (s : ℕ) :
    (.inl (.aux s) : LW) ∈ FramedCircuit.touched (gL (opGate op)) ↔ s ∈ op.slots := by
  obtain ⟨a, b, h, hw⟩ := opGate_add op
  rw [h, gL_add, mem_touched_add]
  have := hw (.aux s)
  constructor
  · rintro (h1 | h1) <;> cases h1 <;>
      rcases this.mp (by simp) with ⟨s', hs', he⟩ | ⟨_, _, _, he⟩ <;> cases he <;> exact hs'
  · intro hs
    rcases this.mpr (Or.inl ⟨s, hs, rfl⟩) with h1 | h1 <;> simp [h1]

theorem x_mem_opGate (op : Op) (n : ℕ) :
    (.inl (.x n) : LW) ∈ FramedCircuit.touched (gL (opGate op)) ↔ ∃ s, op = .src s n := by
  obtain ⟨a, b, h, hw⟩ := opGate_add op
  rw [h, gL_add, mem_touched_add]
  have := hw (.x n)
  constructor
  · rintro (h1 | h1) <;> cases h1 <;>
      rcases this.mp (by simp) with ⟨s', hs', he⟩ | ⟨s, n', hop, he⟩ <;> cases he <;> exact ⟨s, hop⟩
  · rintro ⟨s, hs⟩
    rcases this.mpr (Or.inr ⟨s, n, hs, rfl⟩) with h1 | h1 <;> simp [h1]

theorem y_not_mem_opGate (op : Op) (t : ℕ) :
    (.inl (.y t) : LW) ∉ FramedCircuit.touched (gL (opGate op)) := by
  obtain ⟨a, b, h, hw⟩ := opGate_add op
  rw [h, gL_add, mem_touched_add]
  have := hw (.y t)
  rintro (h1 | h1) <;> cases h1 <;>
    rcases this.mp (by simp) with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he

theorem inr_not_mem_gL (g : Circuit.Gate Reg (ZMod 2)) (c : Fin 23) :
    (.inr c : LW) ∉ FramedCircuit.touched (gL g) := by
  simp [gL, gateMap, FramedCircuit.touched]

/-- Frames of single blocks over a list. -/
theorem fseq_singles {α : Type*} (l : List α) (g : α → Circuit.Gate LW (ZMod 2)) (F : α → LMat)
    (w : LW) : (l.map fun a => single (g a) (F a)).flatMap (fseq w) =
      (l.filter fun a => w ∈ FramedCircuit.touched (g a)).map F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.flatMap_cons, ih, fseq_single, List.filter_cons]
    by_cases h : w ∈ FramedCircuit.touched (g a) <;> simp [h]

theorem pairwise_last {α : Type*} {R : α → α → Prop} {l : List α} (h : l.Pairwise R) {y : α}
    (hy : l.getLast? = some y) : ∀ x ∈ l, R x y ∨ x = y := by
  obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.mp hy
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inl ((List.pairwise_append.mp h).2.2 x hx y (by simp))
  · exact Or.inr (List.mem_singleton.mp hx)

/-! ### The node order of the PR97 operations -/

/-- Frames of nodes, in the node order. -/
def NodeLe (a b : ℕ) : Prop := a < nodeCount → b < nodeCount → Le (nodeFrame a) (nodeFrame b)

theorem nodeLe_order : dag.FrameOrder NodeLe where
  refl _n hn _ := le_refl_of_idem (nodeFrame_idem hn)
  arg _k hk hkN pos _ _ := le_of_nested (nodeFrame_arg (Nat.not_lt.mpr hk) hkN pos)
  link _n _o _t _pos h _ _ := le_of_nested (nodeFrame_link h)

theorem ops_node_lt {op : Op} (h : op ∈ dag.compile.ops) : op.node < nodeCount :=
  (dag.compile_ops_node op h).1

/-- Along each slot, the frames of the compiled operations increase. -/
theorem slot_frames_pairwise (s : ℕ) :
    ((nodesOf s dag.compile.ops).map nodeFrame).Pairwise Le := by
  have hc := dag.compile_chain dag_valid nodeLe_order s
  have hlt : ∀ n ∈ nodesOf s dag.compile.ops, n < nodeCount := by
    intro n hn
    simp only [nodesOf, List.mem_map, List.mem_filter] at hn
    obtain ⟨op, ⟨hop, -⟩, rfl⟩ := hn
    exact ops_node_lt hop
  have hc' : ((nodesOf s dag.compile.ops).map nodeFrame).IsChain Le := by
    rw [List.isChain_map]
    exact List.IsChain.imp_of_mem_imp (fun a b ha hb h => h (hlt a ha) (hlt b hb)) hc
  exact List.isChain_iff_pairwise.mp hc'

/-- A root slot's operation frames lie below its root's node frame. -/
theorem slot_frames_le_root {j : ℕ} (hj : j < rootCount) :
    ∀ f ∈ (nodesOf (slotOf j) dag.compile.ops).map nodeFrame, Le f (nodeFrame (dag.rootNode j)) := by
  have hlast := dag.compile_root_nodes dag_valid nodeLe_order (r := j) hj
  have hlast' : ((nodesOf (slotOf j) dag.compile.ops).map nodeFrame).getLast? =
      some (nodeFrame (dag.rootNode j)) := by
    rw [List.getLast?_map, hlast]; rfl
  intro f hf
  rcases pairwise_last (slot_frames_pairwise _) hlast' f hf with h | rfl
  · exact h
  · exact le_refl_of_idem (nodeFrame_idem (root_node hj))

/-! ### The frames of each part of the first stage -/

theorem fseq_map {α : Type*} (l : List α) (g : α → Circuit.Gate LW (ZMod 2)) (F : α → LMat)
    (w : LW) : fseq w (l.map fun a => (⟨g a, F a⟩ : FGate LW 23)) =
      (l.filter fun a => w ∈ FramedCircuit.touched (g a)).map F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, fseq_cons, ih, List.filter_cons]
    split_ifs <;> simp_all

theorem mem_map_filter {α : Type*} {l : List α} {p : α → Bool} {F : α → LMat} {f : LMat} :
    f ∈ (l.filter p).map F ↔ ∃ a ∈ l, p a = true ∧ F a = f := by
  simp [List.mem_map, List.mem_filter, and_assoc]

theorem pass1_gate_cases {g : Circuit.Gate Reg (ZMod 2)}
    (hg : g ∈ dag.sideGates ++ dag.rootReads targets ++ dag.sideGates.reverse) :
    ∃ a b, g = ReversibleFanout.add a b ∧ a.isX = false ∧ b.isX = false := by
  simp only [List.mem_append, List.mem_reverse] at hg
  have hside : g ∈ dag.sideGates → ∃ a b, g = ReversibleFanout.add a b ∧ a.isX = false ∧
      b.isX = false := by
    intro h
    simp only [Dag.sideGates, List.mem_map, List.mem_filter] at h
    obtain ⟨op, ⟨-, hsrc⟩, rfl⟩ := h
    cases op with
    | src _ _ => simp [Op.isSrc] at hsrc
    | add p o k => exact ⟨_, _, rfl, rfl, rfl⟩
    | copy p f k => exact ⟨_, _, rfl, rfl, rfl⟩
  rcases hg with (h | h) | h
  · exact hside h
  · simp only [Dag.rootReads, List.mem_flatMap, List.mem_map] at h
    obtain ⟨j, -, T, -, rfl⟩ := h
    exact ⟨_, _, rfl, rfl, rfl⟩
  · exact hside h

theorem fseqP_zero (w : LW) : ∀ f ∈ pass1Blocks.flatMap (fseq w), f = 0 := by
  intro f hf
  rw [pass1Blocks, fseq_singles, mem_map_filter] at hf
  obtain ⟨_, _, _, rfl⟩ := hf
  rfl

theorem fseqP_x (n : ℕ) : pass1Blocks.flatMap (fseq (.inl (.x n))) = [] := by
  rw [pass1Blocks, fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro g hg
  obtain ⟨a, b, rfl, ha, hb⟩ := pass1_gate_cases hg
  rw [gL_add, mem_touched_add]
  simp only [decide_eq_true_eq, not_or]
  constructor <;> rintro h <;> cases h <;> simp [Reg.isX] at ha hb

theorem fseqP_tmp (c : Fin 23) : pass1Blocks.flatMap (fseq (.inr c)) = [] := by
  rw [pass1Blocks, fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro g _
  simpa using inr_not_mem_gL g c

theorem fseqC_aux (s : ℕ) :
    computeBlocks.flatMap (fseq (.inl (.aux s))) = (nodesOf s dag.compile.ops).map nodeFrame := by
  have hf : ∀ op ∈ dag.compile.ops,
      decide ((.inl (.aux s) : LW) ∈ FramedCircuit.touched (gL (opGate op))) =
        decide (s ∈ op.slots) := fun op _ => decide_eq_decide.mpr (aux_mem_opGate op s)
  rw [computeBlocks, fseq_singles, nodesOf, List.map_map, List.filter_congr hf]
  rfl

theorem fseqC_x (n : ℕ) : ∀ f ∈ computeBlocks.flatMap (fseq (.inl (.x n))), f = nodeFrame n := by
  intro f hf
  rw [computeBlocks, fseq_singles, mem_map_filter] at hf
  obtain ⟨op, -, hx, rfl⟩ := hf
  obtain ⟨s, rfl⟩ := (x_mem_opGate op n).mp (by simpa using hx)
  rfl

theorem fseqC_y (t : ℕ) : computeBlocks.flatMap (fseq (.inl (.y t))) = [] := by
  rw [computeBlocks, fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro op _
  simpa using y_not_mem_opGate op t

theorem fseqC_tmp (c : Fin 23) : computeBlocks.flatMap (fseq (.inr c)) = [] := by
  rw [computeBlocks, fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro op _
  simpa using inr_not_mem_gL (opGate op) c

theorem fseqU_one (w : LW) : ∀ f ∈ uncomputeBlocks.flatMap (fseq w), f = 1 := by
  intro f hf
  rw [uncomputeBlocks, fseq_singles, mem_map_filter] at hf
  obtain ⟨_, _, _, rfl⟩ := hf
  rfl

theorem fseqU_y (t : ℕ) : uncomputeBlocks.flatMap (fseq (.inl (.y t))) = [] := by
  rw [uncomputeBlocks, fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro op _
  simpa using y_not_mem_opGate op t

theorem fseqU_tmp (c : Fin 23) : uncomputeBlocks.flatMap (fseq (.inr c)) = [] := by
  rw [uncomputeBlocks, fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro op _
  simpa using inr_not_mem_gL (opGate op) c

/-- The scatter of a centre block. -/
theorem fseq_scatter (c : Fin 23) (w : LW) :
    fseq w ((targets (3 * leafCount + c)).map fun t =>
      (⟨ReversibleFanout.add (.inl (.y t)) (.inr c), 0⟩ : FGate LW 23)) =
      ((targets (3 * leafCount + c)).filter fun t =>
        w ∈ FramedCircuit.touched (ReversibleFanout.add (.inl (.y t) : LW) (.inr c))).map
        fun _ => 0 :=
  fseq_map _ _ _ w

theorem fseq_centreBlock (c : Fin 23) (w : LW) :
    fseq w (centreBlock c) =
      (if w = .inr c ∨ w = .inl (.aux (slotOf (3 * leafCount + c))) then [starFrame c] else []) ++
        ((targets (3 * leafCount + c)).filter fun t =>
          w ∈ FramedCircuit.touched (ReversibleFanout.add (.inl (.y t) : LW) (.inr c))).map
          fun _ => 0 := by
  rw [centreBlock, fseq_cons, fseq_scatter]
  by_cases h : w = .inr c ∨ w = .inl (.aux (slotOf (3 * leafCount + c)))
  · rw [ite_eq_left ((mem_touched_add _ _ _).mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun h' => h ((mem_touched_add _ _ _).mp h')), ite_eq_right h]; rfl

theorem fseqM_aux (s : ℕ) : ∀ f ∈ centreBlocks.flatMap (fseq (.inl (.aux s))),
    ∃ c : Fin 23, s = slotOf (3 * leafCount + c) ∧ f = starFrame c := by
  intro f hf
  rw [centreBlocks, List.flatMap_map, List.mem_flatMap] at hf
  obtain ⟨c, -, hf⟩ := hf
  rw [fseq_centreBlock, List.mem_append] at hf
  rcases hf with h | h
  · by_cases hc : (.inl (.aux s) : LW) = .inr c ∨
        (.inl (.aux s) : LW) = .inl (.aux (slotOf (3 * leafCount + c)))
    · rw [ite_eq_left hc, List.mem_singleton] at h
      rcases hc with hc | hc
      · cases hc
      · exact ⟨c, by simpa using hc, h⟩
    · rw [ite_eq_right hc] at h; cases h
  · rw [mem_map_filter] at h
    obtain ⟨t, -, ht, -⟩ := h
    simp [mem_touched_add] at ht

theorem fseqM_y (t : ℕ) : ∀ f ∈ centreBlocks.flatMap (fseq (.inl (.y t))), f = 0 := by
  intro f hf
  rw [centreBlocks, List.flatMap_map, List.mem_flatMap] at hf
  obtain ⟨c, -, hf⟩ := hf
  rw [fseq_centreBlock, List.mem_append] at hf
  rcases hf with h | h
  · by_cases hc : (.inl (.y t) : LW) = .inr c ∨
        (.inl (.y t) : LW) = .inl (.aux (slotOf (3 * leafCount + c)))
    · rcases hc with hc | hc <;> cases hc
    · rw [ite_eq_right hc] at h; cases h
  · rw [mem_map_filter] at h
    obtain ⟨_, _, _, rfl⟩ := h
    rfl

theorem fseqM_x (n : ℕ) : centreBlocks.flatMap (fseq (.inl (.x n))) = [] := by
  rw [centreBlocks, List.flatMap_map, List.flatMap_eq_nil_iff]
  intro c _
  rw [fseq_centreBlock, ite_eq_right (by rintro (h | h) <;> cases h), List.nil_append,
    List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro t _
  simp [mem_touched_add]

theorem flatMap_one {α β : Type*} {l : List α} (hl : l.Nodup) {a : α} (ha : a ∈ l)
    {f : α → List β} (hf : ∀ b ∈ l, b ≠ a → f b = []) : l.flatMap f = f a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons]
    by_cases hx : x = a
    · subst hx
      rw [List.flatMap_eq_nil_iff.mpr fun b hb => hf b (List.mem_cons_of_mem _ hb)
        (fun e => hl.1 (e ▸ hb)), List.append_nil]
    · rw [hf x (by simp) hx, List.nil_append]
      exact ih hl.2 (by simpa [Ne.symm hx] using ha) fun b hb => hf b (List.mem_cons_of_mem _ hb)

theorem fseq_other_centre {c c' : Fin 23} (hc' : c' ≠ c) : fseq (.inr c) (centreBlock c') = [] := by
  rw [fseq_centreBlock, ite_eq_right, List.nil_append, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  · intro t _
    simp only [mem_touched_add, decide_eq_true_eq]
    rintro (h | h)
    · cases h
    · exact hc' (Sum.inr.inj h).symm
  · rintro (h | h)
    · exact hc' (Sum.inr.inj h).symm
    · cases h

theorem fseqM_tmp (c : Fin 23) :
    centreBlocks.flatMap (fseq (.inr c)) =
      starFrame c :: (targets (3 * leafCount + c)).map fun _ => 0 := by
  rw [centreBlocks, List.flatMap_map, flatMap_one (List.nodup_finRange 23) (List.mem_finRange c)
    fun c' _ hc' => fseq_other_centre hc', fseq_centreBlock, ite_eq_left (Or.inl rfl),
    List.singleton_append]
  congr 1
  rw [List.filter_eq_self.mpr]
  intro t _
  simp [mem_touched_add]

theorem fseqO_aux (s : ℕ) : ∀ f ∈ outputBlocks.flatMap (fseq (.inl (.aux s))),
    ∃ j < 3 * leafCount, s = slotOf j ∧ f = hyperFrame (leafTriple (j / 3)) := by
  intro f hf
  rw [outputBlocks, fseq_singles, mem_map_filter] at hf
  obtain ⟨j, hj, hw, rfl⟩ := hf
  simp only [mem_touched_add, decide_eq_true_eq] at hw
  rcases hw with hw | hw
  · cases hw
  · exact ⟨j, List.mem_range.mp hj, by injection hw with hw; injection hw, rfl⟩

theorem fseqO_y (t : ℕ) : ∀ f ∈ outputBlocks.flatMap (fseq (.inl (.y t))),
    f = hyperFrame (leafTriple t) := by
  intro f hf
  rw [outputBlocks, fseq_singles, mem_map_filter] at hf
  obtain ⟨j, -, hw, rfl⟩ := hf
  simp only [mem_touched_add, decide_eq_true_eq] at hw
  rcases hw with hw | hw
  · injection hw with hw; injection hw with hw; rw [hw]
  · cases hw

theorem fseqO_x (n : ℕ) : outputBlocks.flatMap (fseq (.inl (.x n))) = [] := by
  rw [outputBlocks, fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro j _
  simp [mem_touched_add]

theorem fseqO_tmp (c : Fin 23) : outputBlocks.flatMap (fseq (.inr c)) = [] := by
  rw [outputBlocks, fseq_singles, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro j _
  simp [mem_touched_add]

theorem fseq_stage1 (w : LW) : fseq w stage1 =
    pass1Blocks.flatMap (fseq w) ++ computeBlocks.flatMap (fseq w) ++
      centreBlocks.flatMap (fseq w) ++ outputBlocks.flatMap (fseq w) ++
        uncomputeBlocks.flatMap (fseq w) := by
  rw [stage1, fseq_flatten, blocks1]
  simp only [List.flatMap_append]

/-! ### Chains of the first stage -/

theorem pw_app {α : Type*} {R : α → α → Prop} {A B : List α} (hA : A.Pairwise R)
    (hB : B.Pairwise R) (h : ∀ a ∈ A, ∀ b ∈ B, R a b) : (A ++ B).Pairwise R :=
  List.pairwise_append.mpr ⟨hA, hB, h⟩

theorem pw_const {α : Type*} {R : α → α → Prop} {A : List α} {x : α} (hx : R x x)
    (h : ∀ a ∈ A, a = x) : A.Pairwise R :=
  List.Pairwise.imp_of_mem (fun {a b} ha hb _ => by rw [h a ha, h b hb]; exact hx)
    (List.pairwise_of_forall (fun _ _ => trivial))

theorem starFrame_idem {c : ℕ} (hc : c < 23) : starFrame c * starFrame c = starFrame c :=
  frameOf_idem (starSet_mem hc)

theorem leafTriple_isTriple {t : ℕ} (ht : t < leafCount) : IsTriple (leafTriple t) :=
  ⟨leafTriple_card ht, leafTriple_lt ht⟩

theorem centre_root_lt (c : Fin 23) : 3 * leafCount + c < rootCount := by
  have := c.2; show 3 * 1771 + (c : ℕ) < 5336; omega

theorem out_root_lt {j : ℕ} (hj : j < 3 * leafCount) : j < rootCount := by
  have : j < 3 * 1771 := hj; show j < 5336; omega

theorem rootNode_centre (c : Fin 23) :
    nodeFrame (dag.rootNode (3 * leafCount + c)) = starFrame c :=
  nodeFrame_centre c.2

theorem rootNode_out {j : ℕ} (hj : j < 3 * leafCount) :
    Le (nodeFrame (dag.rootNode j)) (hyperFrame (leafTriple (j / 3))) := by
  have ht : j / 3 < leafCount := by have : j < 3 * 1771 := hj; show j / 3 < 1771; omega
  have h := nodeFrame_out ht (show j % 3 < 3 from Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod] at h
  exact le_of_nested h

/-- **The first stage along a side slot.** -/
theorem chain1_aux (s : ℕ) : (0 :: fseq (.inl (.aux s)) stage1).Pairwise Le := by
  rw [fseq_stage1, fseqC_aux]
  have hP := fseqP_zero (.inl (.aux s))
  have hC := slot_frames_pairwise s
  have hM := fseqM_aux s
  have hO := fseqO_aux s
  have hU := fseqU_one (.inl (.aux s))
  have hCM : ∀ a ∈ (nodesOf s dag.compile.ops).map nodeFrame,
      ∀ b ∈ centreBlocks.flatMap (fseq (.inl (.aux s))), Le a b := by
    intro a ha b hb
    obtain ⟨c, hs, rfl⟩ := hM b hb
    rw [hs] at ha
    rw [← rootNode_centre]
    exact slot_frames_le_root (centre_root_lt c) a ha
  have hCO : ∀ a ∈ (nodesOf s dag.compile.ops).map nodeFrame,
      ∀ b ∈ outputBlocks.flatMap (fseq (.inl (.aux s))), Le a b := by
    intro a ha b hb
    obtain ⟨j, hj, hs, rfl⟩ := hO b hb
    rw [hs] at ha
    exact le_trans' (slot_frames_le_root (out_root_lt hj) a ha) (rootNode_out hj)
  have hMM : (centreBlocks.flatMap (fseq (.inl (.aux s)))).Pairwise Le := by
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb _ => ?_)
      (List.pairwise_of_forall (fun _ _ => trivial))
    obtain ⟨c, hc, rfl⟩ := hM a ha
    obtain ⟨c', hc', rfl⟩ := hM b hb
    have : (3 * leafCount + (c : ℕ)) = 3 * leafCount + c' :=
      dag.root_slot_inj dag_valid (centre_root_lt c) (centre_root_lt c') (hc.symm.trans hc')
    rw [show c = c' from Fin.ext (by omega)]
    exact le_refl_of_idem (starFrame_idem c'.2)
  have hOO : (outputBlocks.flatMap (fseq (.inl (.aux s)))).Pairwise Le := by
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb _ => ?_)
      (List.pairwise_of_forall (fun _ _ => trivial))
    obtain ⟨j, hj, hjs, rfl⟩ := hO a ha
    obtain ⟨j', hj', hjs', rfl⟩ := hO b hb
    rw [dag.root_slot_inj dag_valid (out_root_lt hj) (out_root_lt hj') (hjs.symm.trans hjs')]
    have ht : j' / 3 < leafCount := by have : j' < 3 * 1771 := hj'; show j' / 3 < 1771; omega
    exact le_refl_of_idem (hyperFrame_idem (leafTriple_isTriple ht))
  have hMO : ∀ a ∈ centreBlocks.flatMap (fseq (.inl (.aux s))),
      ∀ b ∈ outputBlocks.flatMap (fseq (.inl (.aux s))), Le a b := by
    intro a ha b hb
    obtain ⟨c, hc, -⟩ := hM a ha
    obtain ⟨j, hj, hjs, -⟩ := hO b hb
    have := dag.root_slot_inj dag_valid (centre_root_lt c) (out_root_lt hj) (hc.symm.trans hjs)
    omega
  refine List.pairwise_cons.mpr ⟨fun b _ => zero_le b, ?_⟩
  refine pw_app (pw_app (pw_app (pw_app (pw_const (zero_le 0) hP) hC ?_) hMM ?_) hOO ?_)
    (pw_const (le_one 1) hU) ?_
  · intro a ha b _; rw [hP a ha]; exact zero_le b
  · intro a ha b hb
    rcases List.mem_append.mp ha with ha | ha
    · rw [hP a ha]; exact zero_le b
    · exact hCM a ha b hb
  · intro a ha b hb
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · rw [hP a ha]; exact zero_le b
      · exact hCO a ha b hb
    · exact hMO a ha b hb
  · intro a _ b hb; rw [hU b hb]; exact le_one a

/-- **The first stage along a source.** -/
theorem chain1_x {n : ℕ} (hn : n < leafCount) :
    (nodeFrame n :: fseq (.inl (.x n)) stage1).Pairwise Le ∧
      ∀ f ∈ fseq (.inl (.x n)) stage1, f = nodeFrame n ∨ f = 1 := by
  rw [fseq_stage1, fseqP_x, fseqM_x, fseqO_x, List.nil_append, List.append_nil, List.append_nil]
  have hC := fseqC_x n
  have hU := fseqU_one (.inl (.x n))
  have hid := le_refl_of_idem (nodeFrame_idem (lt_trans hn leafCount_lt))
  refine ⟨List.pairwise_cons.mpr ⟨fun b hb => ?_, pw_app (pw_const hid hC)
    (pw_const (le_one 1) hU) fun a _ b hb => by rw [hU b hb]; exact le_one a⟩, fun f hf => ?_⟩
  · rcases List.mem_append.mp hb with hb | hb
    · rw [hC b hb]; exact hid
    · rw [hU b hb]; exact le_one _
  · rcases List.mem_append.mp hf with hf | hf
    · exact Or.inl (hC f hf)
    · exact Or.inr (hU f hf)

/-- **The first stage along a target.** -/
theorem chain1_y {t : ℕ} (ht : t < leafCount) :
    (0 :: fseq (.inl (.y t)) stage1).Pairwise Le ∧
      ∀ f ∈ fseq (.inl (.y t)) stage1, f = 0 ∨ f = hyperFrame (leafTriple t) := by
  rw [fseq_stage1, fseqC_y, fseqU_y, List.append_nil, List.append_nil]
  have hP := fseqP_zero (.inl (.y t))
  have hM := fseqM_y t
  have hO := fseqO_y t
  have hH := le_refl_of_idem (hyperFrame_idem (leafTriple_isTriple ht))
  have hzero : (pass1Blocks.flatMap (fseq (.inl (.y t))) ++
      centreBlocks.flatMap (fseq (.inl (.y t)))).Pairwise Le := pw_const (zero_le 0) fun a ha => by
    rcases List.mem_append.mp ha with ha | ha
    · exact hP a ha
    · exact hM a ha
  refine ⟨List.pairwise_cons.mpr ⟨fun b _ => zero_le b, ?_⟩, fun f hf => ?_⟩
  · refine pw_app hzero (pw_const hH hO) fun a ha b hb => ?_
    rcases List.mem_append.mp ha with ha | ha
    · rw [hP a ha]; exact zero_le b
    · rw [hM a ha]; exact zero_le b
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · exact Or.inl (hP f hf)
      · exact Or.inl (hM f hf)
    · exact Or.inr (hO f hf)

/-- **The first stage along a temporary.** -/
theorem fseq1_tmp (c : Fin 23) :
    fseq (.inr c) stage1 = starFrame c :: (targets (3 * leafCount + c)).map fun _ => 0 := by
  rw [fseq_stage1, fseqP_tmp, fseqC_tmp, fseqM_tmp, fseqO_tmp, fseqU_tmp, List.nil_append,
    List.nil_append, List.append_nil, List.append_nil]

/-! ### The second stage -/

theorem fseq_complB (w : LW) (B : List (FGate LW 23)) :
    fseq w (complB B) = (fseq w B).map (1 - ·) := by
  simp only [complB, fseq, List.filter_map, List.map_map]
  rfl

theorem reverse_short {α : Type*} {l : List α} (h : l.length ≤ 1) : l.reverse = l := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl

/-- Reversed blocks, each touching the wire at most once, reverse the wire's frames. -/
theorem fseq_reflect (w : LW) : ∀ Bs : List (List (FGate LW 23)),
    (∀ B ∈ Bs, (fseq w B).length ≤ 1) →
      fseq w (Bs.reverse.map complB).flatten = ((fseq w Bs.flatten).map (1 - ·)).reverse
  | [], _ => rfl
  | B :: Bs, h => by
    rw [List.reverse_cons, List.map_append, List.flatten_append, fseq_append,
      fseq_reflect w Bs fun B' hB' => h B' (List.mem_cons_of_mem _ hB'), List.flatten_cons,
      fseq_append, List.map_append, List.reverse_append, List.map_singleton, List.flatten_singleton,
      fseq_complB]
    congr 1
    rw [reverse_short (by rw [List.length_map]; exact h B (by simp))]

theorem targets_nodup (j : ℕ) : (targets j).Nodup := by
  rw [targets]
  split_ifs
  · exact List.nodup_singleton _
  · exact List.nodup_range.filter _

theorem count_le_one_of_nodup {l : List ℕ} (hl : l.Nodup) (t : ℕ) :
    (l.filter fun t' => t' = t).length ≤ 1 := by
  have := List.nodup_iff_count_le_one.mp hl t
  rwa [List.count_eq_length_filter] at this

theorem blocks1_short (r : Reg) : ∀ B ∈ blocks1, (fseq (.inl r) B).length ≤ 1 := by
  have hsingle : ∀ g F, (fseq (.inl r) (single g F)).length ≤ 1 := fun g F => by
    rw [fseq_single]; split_ifs <;> simp
  intro B hB
  simp only [blocks1, List.mem_append, pass1Blocks, computeBlocks, centreBlocks, outputBlocks,
    uncomputeBlocks, List.mem_map] at hB
  rcases hB with (((⟨g, -, rfl⟩ | ⟨op, -, rfl⟩) | ⟨c, -, rfl⟩) | ⟨j, -, rfl⟩) | ⟨op, -, rfl⟩
  · exact hsingle _ _
  · exact hsingle _ _
  · rw [fseq_centreBlock, List.length_append, List.length_map]
    by_cases hr : (.inl r : LW) = .inl (.aux (slotOf (3 * leafCount + c)))
    · rw [ite_eq_left (Or.inr hr)]
      have : ((targets (3 * leafCount + c)).filter fun t =>
          (.inl r : LW) ∈ FramedCircuit.touched (ReversibleFanout.add (.inl (.y t) : LW) (.inr c))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro t _
        rw [hr]; simp [mem_touched_add]
      rw [this]; simp
    · rw [ite_eq_right (fun h => h.elim (fun h' => by cases h') hr), List.length_nil, zero_add]
      have h1 : ((targets (3 * leafCount + c)).filter fun t =>
          decide ((.inl r : LW) ∈ FramedCircuit.touched (ReversibleFanout.add (.inl (.y t) : LW) (.inr c)))) =
          (targets (3 * leafCount + c)).filter fun t => decide (Reg.y t = r) := by
        apply List.filter_congr
        intro t _
        simp only [mem_touched_add, Sum.inl.injEq, reduceCtorEq, or_false, decide_eq_decide]
        exact eq_comm
      rw [h1]
      cases r with
      | y t => exact (count_le_one_of_nodup (targets_nodup _) t).trans_eq' (by
          congr 1; apply List.filter_congr; intro t' _; simp)
      | x n => simp
      | aux s => simp
  · exact hsingle _ _
  · exact hsingle _ _

/-- **The second stage along a register**: the first stage's frames, reversed and complemented. -/
theorem fseq2_reg (r : Reg) :
    fseq (.inl r) stage2 = ((fseq (.inl r) stage1).map (1 - ·)).reverse :=
  fseq_reflect _ _ (blocks1_short r)

theorem flatMap_nil_of {w : LW} {Bs : List (List (FGate LW 23))} (h : ∀ B ∈ Bs, fseq w B = []) :
    Bs.flatMap (fseq w) = [] := List.flatMap_eq_nil_iff.mpr h

theorem fseq_tmp_list (c : Fin 23) (l : List (Fin 23)) (hl : l.Nodup) (hc : c ∈ l) :
    (l.flatMap fun c' => fseq (.inr c) (complB (centreBlock c'))) =
      fseq (.inr c) (complB (centreBlock c)) :=
  flatMap_one hl hc fun c' _ hc' => by rw [fseq_complB, fseq_other_centre hc', List.map_nil]

/-- **The second stage along a temporary.** -/
theorem fseq2_tmp (c : Fin 23) :
    fseq (.inr c) stage2 = (1 - starFrame c) :: (targets (3 * leafCount + c)).map fun _ => 1 := by
  rw [stage2, fseq_flatten, blocks1]
  simp only [List.reverse_append, List.map_append, List.flatMap_append]
  have hnil : ∀ Bs : List (List (FGate LW 23)), (∀ B ∈ Bs, fseq (.inr c) B = []) →
      (Bs.reverse.map complB).flatMap (fseq (.inr c)) = [] := by
    intro Bs h
    apply List.flatMap_eq_nil_iff.mpr
    intro B hB
    rw [List.mem_map] at hB
    obtain ⟨B', hB', rfl⟩ := hB
    rw [fseq_complB, h B' (List.mem_reverse.mp hB'), List.map_nil]
  have hs : ∀ (l : List (Circuit.Gate LW (ZMod 2))) (F : Circuit.Gate LW (ZMod 2) → LMat),
      (∀ g ∈ l, (.inr c : LW) ∉ FramedCircuit.touched g) →
        ∀ B ∈ l.map (fun g => single g (F g)), fseq (.inr c) B = [] := by
    intro l F h B hB
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hB
    rw [fseq_single, ite_eq_right (h g hg)]
  rw [hnil uncomputeBlocks, hnil outputBlocks, hnil computeBlocks, hnil pass1Blocks]
  · rewrite [List.nil_append, List.nil_append, List.nil_append, List.append_nil, centreBlocks, ← List.map_reverse, List.map_map, Function.comp_def, List.flatMap_map,
      fseq_tmp_list c _ (List.nodup_reverse.mpr (List.nodup_finRange 23))
        (List.mem_reverse.mpr (List.mem_finRange c)),
      fseq_complB, fseq_centreBlock, ite_eq_left (Or.inl rfl), List.filter_eq_self.mpr]
    · rewrite [List.singleton_append, List.map_cons, List.map_map]
      exact congrArg _ (List.map_congr_left fun _ _ => sub_zero 1)
    · intro t _; simp [mem_touched_add]
  all_goals intro B hB
  · obtain ⟨g, -, rfl⟩ := List.mem_map.mp hB
    rw [fseq_single, ite_eq_right (inr_not_mem_gL _ c)]
  · obtain ⟨op, -, rfl⟩ := List.mem_map.mp hB
    rw [fseq_single, ite_eq_right (inr_not_mem_gL _ c)]
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hB
    rw [fseq_single, ite_eq_right (by simp [mem_touched_add])]
  · obtain ⟨op, -, rfl⟩ := List.mem_map.mp hB
    rw [fseq_single, ite_eq_right (inr_not_mem_gL _ c)]

/-! ### The gates of the stages -/

/-- The kinds of gates of the stages. -/
def StageGate (g : Circuit.Gate LW (ZMod 2)) : Prop :=
  (∃ op ∈ dag.compile.ops, g = gL (opGate op)) ∨
    (∃ j < rootCount, ∃ T ∈ targets j, g = ReversibleFanout.add (.inl (.y T)) (.inl (.aux (slotOf j)))) ∨
    (∃ c : Fin 23, g = ReversibleFanout.add (.inr c) (.inl (.aux (slotOf (3 * leafCount + c))))) ∨
    (∃ c : Fin 23, ∃ T ∈ targets (3 * leafCount + c), g = ReversibleFanout.add (.inl (.y T)) (.inr c))

theorem mem_targets_out {j : ℕ} (hj : j < 3 * leafCount) : j / 3 ∈ targets j := by
  rw [targets, ite_eq_left hj]; simp

theorem stage1_gates : ∀ v ∈ stage1, StageGate v.gate := by
  intro v hv
  rw [stage1, List.mem_flatten] at hv
  obtain ⟨B, hB, hv⟩ := hv
  simp only [blocks1, List.mem_append, pass1Blocks, computeBlocks, centreBlocks, outputBlocks,
    uncomputeBlocks, List.mem_map] at hB
  rcases hB with (((⟨g, hg, rfl⟩ | ⟨op, hop, rfl⟩) | ⟨c, -, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨op, hop, rfl⟩
  · rw [single, List.mem_singleton] at hv; subst hv
    simp only [List.mem_reverse] at hg
    have hside : g ∈ dag.sideGates → StageGate (gL g) := by
      intro h
      simp only [Dag.sideGates, List.mem_map, List.mem_filter] at h
      obtain ⟨op, ⟨hop, -⟩, rfl⟩ := h
      exact Or.inl ⟨op, hop, rfl⟩
    rcases hg with (h | h) | h
    · exact hside h
    · simp only [Dag.rootReads, List.mem_flatMap, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, T, hT, rfl⟩ := h
      exact Or.inr (Or.inl ⟨j, hj, T, hT, by rw [gL_add]⟩)
    · exact hside h
  · rw [single, List.mem_singleton] at hv; subst hv
    exact Or.inl ⟨op, hop, rfl⟩
  · rw [centreBlock, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨T, hT, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨c, T, hT, rfl⟩))
  · rw [single, List.mem_singleton] at hv; subst hv
    have hj' := List.mem_range.mp hj
    exact Or.inr (Or.inl ⟨j, out_root_lt hj', j / 3, mem_targets_out hj', rfl⟩)
  · rw [single, List.mem_singleton] at hv; subst hv
    exact Or.inl ⟨op, List.mem_reverse.mp hop, rfl⟩

theorem stage2_gates : ∀ v ∈ stage2, StageGate v.gate := by
  intro v hv
  rw [stage2, List.mem_flatten] at hv
  obtain ⟨B, hB, hv⟩ := hv
  obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hB
  obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hv
  exact stage1_gates v' (List.mem_flatten.mpr ⟨B', List.mem_reverse.mp hB', hv'⟩)

theorem stageGate_xor {g : Circuit.Gate LW (ZMod 2)} (h : StageGate g) :
    ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src := by
  rcases h with ⟨op, hop, rfl⟩ | ⟨j, -, T, -, rfl⟩ | ⟨c, rfl⟩ | ⟨c, T, -, rfl⟩
  · have hd := (dag.compile_ops_ok dag_valid op hop).1
    cases op with
    | src s n => exact ⟨.inl (.aux s), .inl (.x n), by simp, by rw [opGate, gL_add]⟩
    | add p o k =>
      exact ⟨.inl (.aux p), .inl (.aux o), by simpa [Op.Distinct] using hd, by rw [opGate, gL_add]⟩
    | copy p f k =>
      exact ⟨.inl (.aux f), .inl (.aux p), by simpa [Op.Distinct, eq_comm] using hd,
        by rw [opGate, gL_add]⟩
  · exact ⟨_, _, by simp, rfl⟩
  · exact ⟨_, _, by simp, rfl⟩
  · exact ⟨_, _, by simp, rfl⟩

/-- The local wires of the invocation's registers. -/
def InR : LW → Prop
  | .inl (.x n) => n < leafCount
  | .inl (.y t) => t < leafCount
  | .inl (.aux s) => s < dag.compile.next
  | .inr _ => True

theorem targets_lt {j T : ℕ} (h : T ∈ targets j) : T < leafCount := by
  rw [targets] at h
  split_ifs at h with hj
  · rw [List.mem_singleton] at h; subst h
    have : j < 3 * 1771 := hj; show j / 3 < 1771; omega
  · exact List.mem_range.mp (List.mem_filter.mp h).1

theorem stageGate_inR {g : Circuit.Gate LW (ZMod 2)} (h : StageGate g) :
    ∀ w ∈ FramedCircuit.touched g, InR w := by
  rcases h with ⟨op, hop, rfl⟩ | ⟨j, hj, T, hT, rfl⟩ | ⟨c, rfl⟩ | ⟨c, T, hT, rfl⟩
  · have hs := (dag.compile_ops_ok dag_valid op hop).2
    have hn := (dag.compile_ops_node op hop).2
    cases op with
    | src s n =>
      intro w hw
      rw [opGate, gL_add, mem_touched_add] at hw
      rcases hw with rfl | rfl
      · exact hs
      · exact hn s n rfl
    | add p o k =>
      intro w hw
      rw [opGate, gL_add, mem_touched_add] at hw
      rcases hw with rfl | rfl
      · exact hs.1
      · exact hs.2
    | copy p f k =>
      intro w hw
      rw [opGate, gL_add, mem_touched_add] at hw
      rcases hw with rfl | rfl
      · exact hs.2
      · exact hs.1
  · intro w hw
    rw [mem_touched_add] at hw
    rcases hw with rfl | rfl
    · exact targets_lt hT
    · exact dag.root_slot_lt dag_valid hj
  · intro w hw
    rw [mem_touched_add] at hw
    rcases hw with rfl | rfl
    · trivial
    · exact dag.root_slot_lt dag_valid (centre_root_lt c)
  · intro w hw
    rw [mem_touched_add] at hw
    rcases hw with rfl | rfl
    · exact targets_lt hT
    · trivial

/-! ### The frames of the stages -/

/-- A small local frame: an idempotent of height at most `10 ^ 201`. -/
structure SmallFrame (K : LMat) : Prop where
  idem : K * K = K
  bound : Height.Bounded K (10 ^ 201)

theorem SmallFrame.lframe {K : LMat} (h : SmallFrame K) : LFrame K :=
  ⟨h.idem, h.bound.mono (ten_pow_mono (by norm_num))⟩

theorem SmallFrame.compl {K : LMat} (h : SmallFrame K) : LFrame (1 - K) where
  idem := by simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h.idem]; abel
  bound := (bounded_one_sub h.bound).mono ((two_mul_ten_pow 201).trans (ten_pow_mono (by norm_num)))

theorem smallFrame_of {K : LMat} (hK : K * K = K) (hb : Height.Bounded K (10 ^ 200)) : SmallFrame K :=
  ⟨hK, hb.mono (ten_pow_mono (by norm_num))⟩

theorem smallFrame_zero : SmallFrame (0 : LMat) :=
  ⟨by simp, fun i j => by simp only [Matrix.zero_apply, Height.ht_zero]; exact Nat.one_le_pow _ _ (by norm_num)⟩

theorem smallFrame_one : SmallFrame (1 : LMat) :=
  ⟨by simp, fun i j => by rw [ht_one_apply]; exact Nat.one_le_pow _ _ (by norm_num)⟩

theorem smallFrame_hyper {T : Finset ℕ} (hT : IsTriple T) : SmallFrame (hyperFrame T) :=
  ⟨hyperFrame_idem hT, ((bounded_one_sub (lineFrame_bounded hT))).mono (two_mul_ten_pow 200)⟩

theorem smallFrame_star {c : ℕ} (hc : c < 23) : SmallFrame (starFrame c) :=
  smallFrame_of (starFrame_idem hc) (frameOf_bounded (starSet_mem hc))

theorem smallFrame_node {n : ℕ} (hn : n < nodeCount) : SmallFrame (nodeFrame n) :=
  smallFrame_of (nodeFrame_idem hn) (nodeFrame_bounded hn)

theorem stage1_frames : ∀ v ∈ stage1, SmallFrame v.frame := by
  intro v hv
  rw [stage1, List.mem_flatten] at hv
  obtain ⟨B, hB, hv⟩ := hv
  simp only [blocks1, List.mem_append, pass1Blocks, computeBlocks, centreBlocks, outputBlocks,
    uncomputeBlocks, List.mem_map] at hB
  rcases hB with (((⟨g, -, rfl⟩ | ⟨op, hop, rfl⟩) | ⟨c, -, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨op, -, rfl⟩
  · rw [single, List.mem_singleton] at hv; subst hv; exact smallFrame_zero
  · rw [single, List.mem_singleton] at hv; subst hv; exact smallFrame_node (ops_node_lt hop)
  · rw [centreBlock, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨T, -, rfl⟩
    · exact smallFrame_star c.2
    · exact smallFrame_zero
  · rw [single, List.mem_singleton] at hv; subst hv
    have hj' := List.mem_range.mp hj
    exact smallFrame_hyper (leafTriple_isTriple (by have : j < 3 * 1771 := hj'; show j / 3 < 1771; omega))
  · rw [single, List.mem_singleton] at hv; subst hv; exact smallFrame_one

theorem stage2_frames : ∀ v ∈ stage2, ∃ K, SmallFrame K ∧ v.frame = 1 - K := by
  intro v hv
  rw [stage2, List.mem_flatten] at hv
  obtain ⟨B, hB, hv⟩ := hv
  obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hB
  obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hv
  exact ⟨v'.frame, stage1_frames v' (List.mem_flatten.mpr ⟨B', List.mem_reverse.mp hB', hv'⟩), rfl⟩

theorem gatesOf_stage2_mem {g : Circuit.Gate LW (ZMod 2)} : g ∈ gatesOf stage2 → StageGate g := by
  intro h
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
  exact stage2_gates v hv

end

end IntegerMultBounds.MathlibTM2.M8.Global
