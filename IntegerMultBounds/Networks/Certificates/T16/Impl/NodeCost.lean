module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.DataCost
public import IntegerMultBounds.Networks.Certificates.T16.Impl.NodeProgram

/-! **The child calls of the T16 node.** The wrappers of every local invocation make no child
calls, so each invocation makes the 5586 calls of its word; the phases of the other events make
one call per odd coefficient. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh Streams Geometry

theorem initials_agree : ∀ w < 224, Trace.backwardInitial.label w = Trace.forwardInitial.label w := by
  decide +kernel

theorem entryLabel_data (rev : Bool) {w : ℕ} (hw : w < 224) :
    entryLabel rev w = Trace.forwardInitial.label w := by
  cases rev
  · rfl
  · exact initials_agree w hw

theorem exitLabel_data (rev : Bool) {w : ℕ} (hw : w < 224) :
    exitLabel rev w = Trace.forwardFinal.label w := by
  cases rev
  · rfl
  · exact finals_agree w hw

theorem childCount_dataIn {s a : ℕ} (ha : a < 112) {f : Fin 73 → ZMod 4} {l : ℕ}
    (h : Matches (dataGs (portData_check ha) s f) l) : childCount (dataIn s a f l) = 0 := by
  unfold dataIn dataGs at *
  simp only [ha, ↓reduceDIte]
  split_ifs at h ⊢ <;> exact childCount_adapterIn _ _ _ h

theorem childCount_dataOut {s a : ℕ} (ha : a < 112) {f : Fin 73 → ZMod 4} {l : ℕ}
    (h : Matches (dataGs (portData_check ha) s f) l) : childCount (dataOut s a f l) = 0 := by
  unfold dataOut dataGs at *
  simp only [ha, ↓reduceDIte]
  split_ifs at h ⊢ <;> exact childCount_adapterOut _ _ _ h

theorem childCount_callIn {s : ℕ} (hs : s < 9) (r w : ℕ) : childCount (callIn s r w) = 0 := by
  unfold callIn
  dsimp only
  split_ifs with h1 h2 h3
  · rw [entryLabel_data _ (by omega)]
    exact childCount_dataIn h1 (matches_X_entry hs h1)
  · have ha : w - 112 < 112 := by omega
    rw [entryLabel_data _ (by omega), show w = w - 112 + 112 by omega, Nat.add_sub_cancel]
    exact childCount_dataIn ha (matches_Y_entry hs ha)
  · exact childCount_helperIn _ _ _ _
  · rfl

theorem childCount_callOut {s : ℕ} (hs : s < 9) (r w : ℕ) : childCount (callOut s r w) = 0 := by
  unfold callOut
  dsimp only
  split_ifs with h1 h2 h3
  · rw [exitLabel_data _ (by omega)]
    exact childCount_dataOut h1 (matches_X_exit hs h1)
  · have ha : w - 112 < 112 := by omega
    rw [exitLabel_data _ (by omega), show w = w - 112 + 112 by omega, Nat.add_sub_cancel]
    exact childCount_dataOut ha (matches_Y_exit hs ha)
  · exact childCount_helperOut _ _ _ _
  · rfl

variable {ι κ : Type}

theorem programChildren_cons (i : TInstr ι) (p : List (TInstr ι)) :
    programChildren (i :: p) = (if i.isChild then 1 else 0) + programChildren p := by
  simp only [programChildren, List.filter_cons]
  split_ifs <;> simp [Nat.add_comm]

theorem programChildren_rename (u : ι → κ) (p : List (TInstr ι)) :
    programChildren (p.map (TInstr.rename u)) = programChildren p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    rw [List.map_cons, programChildren_cons, programChildren_cons, ih]
    cases i <;> rfl

theorem programChildren_regBlocks (reg : ℕ → κ) (rs : List ℕ) (word : ℕ → List Prim)
    (h : ∀ w ∈ rs, childCount (word w) = 0) : programChildren (regBlocks reg rs word) = 0 := by
  induction rs with
  | nil => rfl
  | cons w rs ih =>
    rw [regBlocks, List.flatMap_cons, programChildren_append, programChildren_prims,
      h w List.mem_cons_self, ← regBlocks, ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))]

/-- **Each local invocation makes the 5586 child calls of its word.** -/
theorem callProgram_children {s : ℕ} (hs : s < 9) (r : ℕ) : programChildren (callProgram s r) = 5586 := by
  rw [callProgram, invocation, programChildren_append, programChildren_append,
    programChildren_regBlocks _ _ _ (fun w _ => childCount_callIn hs r w),
    programChildren_regBlocks _ _ _ (fun w _ => childCount_callOut hs r w), programChildren_rename]
  split
  · rw [backwardWord_children]
  · rw [forwardWord_children]

/-! ### The other events -/

/-- The number of set bits among the low `n` bits. -/
def lowBits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x => x % 2 + lowBits n (x / 2)

theorem countP_testBit (n x : ℕ) :
    (List.finRange n).countP (fun k : Fin n => x.testBit k.val) = lowBits n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ, List.countP_cons, List.countP_map, lowBits, ← ih (x / 2)]
    simp only [Function.comp_def, Fin.val_succ, Nat.testBit_succ, Fin.val_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Nat.testBit_zero, h, Nat.add_comm]

/-- The number of odd coefficients of a low bit plane. -/
def odd73 (x : ℕ) : ℕ := lowBits 73 x

/-- The child calls of a unit operation: the odd coefficients of a phase. -/
def unitChildren : UnitOp → ℕ
  | .phase _ _ v => odd73 v.1
  | _ => 0

/-- The child calls of a stream event. -/
def eventOdd : Event → ℕ
  | .phase _ v => odd73 v.1
  | _ => 0

theorem unitChildren_toUnitOp (r a : ℕ) (e : Event) : unitChildren (toUnitOp r a e) = eventOdd e := by
  cases e <;> rfl

theorem coeff_odd (v : Vec) (k : ℕ) : ((v.coeff k).val % 2 == 1) = v.1.testBit k := by
  unfold Vec.coeff
  cases v.1.testBit k <;> cases v.2.testBit k <;> rfl

theorem unitProgram_children (o : UnitOp) : programChildren (unitProgram o) = unitChildren o := by
  cases o with
  | phase u a v =>
    rw [unitProgram, programChildren_prims, childCount, phasePrims, ← List.countP_eq_length_filter,
      List.countP_map, unitChildren, odd73, ← countP_testBit]
    exact List.countP_congr fun k _ => by
      simp only [Function.comp_apply, Prim.isChild, Vec.toFun, coeff_odd]
  | shear d s c => rfl
  | exchange x w => rfl

theorem programChildren_flatMap {α : Type*} (l : List α) (f : α → List (TInstr ι)) :
    programChildren (l.flatMap f) = (l.map fun x => programChildren (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, programChildren_append, ih, List.map_cons, List.sum_cons]

theorem sum_map_flatMap {α β : Type*} (l : List α) (h : α → List β) (g : β → ℕ) :
    ((l.flatMap h).map g).sum = (l.map fun x => ((h x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]

theorem sum_range_ite (n r₀ x : ℕ) :
    ((List.range n).map fun r => if r₀ = r then x else 0).sum = if r₀ < n then x else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases h1 : r₀ < n <;> by_cases h2 : r₀ = n <;> simp [h1, h2] <;> omega

theorem unitPrograms_children (os : List UnitOp) :
    programChildren (os.flatMap unitProgram) = (os.map unitChildren).sum := by
  rw [programChildren_flatMap]
  simp only [unitProgram_children]

theorem eventOps_children (te : TEvent) : ((eventOps te).map unitChildren).sum =
    ((List.range 16).map fun r => ((List.range 112).map fun a =>
      ((expand (portData a) (groupData r a) r localPair localReverse te).map eventOdd).sum).sum).sum := by
  rw [eventOps, sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  rw [sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  rw [List.map_map]
  simp only [Function.comp_def, unitChildren_toUnitOp]

/-- The child calls of the idle phases of child `c` of a replica, over all ports. -/
def idleChildren (r c : ℕ) : ℕ :=
  ((List.range 112).map fun a => odd73 (((groupData r a).idle.lookup c).getD 0)).sum

/-- The child calls of a template event. -/
def eventChildren : TEvent → ℕ
  | .local _ _ => 5586
  | .idle r _ c0 c1 => idleChildren r c0 + idleChildren r c1
  | _ => 0

theorem eventOdd_idleEvent (P : PortData) (G : GroupData) (p side c : ℕ) :
    eventOdd (idleEvent P G p side c) = odd73 ((G.idle.lookup c).getD 0) := by
  simp [idleEvent, eventOdd, Vec.add]

theorem odd73_zero : odd73 0 = 0 := by
  decide

/-- The template facts the count needs. -/
def templateBounds : TEvent → Bool
  | .local s _ => decide (s < 9)
  | .idle r _ _ _ => decide (r < 16)
  | _ => true

theorem template_bounds : template.all templateBounds = true := by decide +kernel

theorem eventProgram_children (te : TEvent) (hte : te ∈ template) :
    programChildren (eventProgram te) = eventChildren te := by
  have hb := List.all_eq_true.mp template_bounds _ hte
  cases te with
  | «local» s r =>
    exact callProgram_children (by simpa [templateBounds] using hb) r
  | idle r p c0 c1 =>
    have hr : r < 16 := by simpa [templateBounds] using hb
    rw [eventProgram, unitPrograms_children, eventOps_children]
    simp only [expand]
    have key : ∀ r', ((List.range 112).map fun a => ((if r = r' then
        [idleEvent (portData a) (groupData r' a) p 0 c0, idleEvent (portData a) (groupData r' a) p 1 c1]
        else []).map eventOdd).sum).sum = if r = r' then idleChildren r c0 + idleChildren r c1 else 0 := by
      intro r'
      by_cases h : r = r'
      · subst h
        simp only [↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          eventOdd_idleEvent, add_zero, idleChildren, ← List.sum_map_add]
      · simp [h]
    simp only [key, sum_range_ite, hr, ↓reduceIte, eventChildren]
  | bridge r d s c =>
    rw [eventProgram, unitPrograms_children, eventOps_children]
    simp only [expand]
    simp [eventOdd, eventChildren, apply_ite]
  | terminalY r ps =>
    rw [eventProgram, unitPrograms_children, eventOps_children]
    simp only [expand]
    simp [eventOdd, eventChildren, apply_ite, Function.comp_def, odd73_zero]
  | terminal r n =>
    rw [eventProgram, unitPrograms_children, eventOps_children]
    simp only [expand]
    simp [eventOdd, eventChildren, apply_ite, Function.comp_def]

/-- A sum over a list, as the sum of its chunks of width `w`. -/
theorem sum_map_chunks {α : Type*} (f : α → ℕ) (w : ℕ) : ∀ n (l : List α), l.length ≤ w * n →
    (l.map f).sum = ((List.range n).map fun k => (((l.drop (w * k)).take w).map f).sum).sum
  | 0, l, h => by cases l with
    | nil => rfl
    | cons _ _ => simp at h
  | n + 1, l, h => by
    have ih := sum_map_chunks f w n (l.drop w) (by rw [List.length_drop]; rw [Nat.mul_succ] at h; omega)
    have hshift : (List.range n).map ((fun k => (((l.drop (w * k)).take w).map f).sum) ∘ Nat.succ) =
        (List.range n).map fun k => ((((l.drop w).drop (w * k)).take w).map f).sum :=
      List.map_congr_left fun k _ => by
        simp only [Function.comp_apply, List.drop_drop, Nat.mul_succ, Nat.add_comm]
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, hshift, ← ih, Nat.mul_zero,
      List.drop_zero, ← List.sum_append, ← List.map_append, List.take_append_drop]

theorem template_length : template.length = 480 := by decide +kernel

theorem template_chunk0 : (((template.drop (30 * 0)).take 30).map eventChildren).sum = 90513 := by
  decide +kernel

theorem template_chunk1 : (((template.drop (30 * 1)).take 30).map eventChildren).sum = 61648 := by
  decide +kernel

theorem template_chunk2 : (((template.drop (30 * 2)).take 30).map eventChildren).sum = 61796 := by
  decide +kernel

theorem template_chunk3 : (((template.drop (30 * 3)).take 30).map eventChildren).sum = 86207 := by
  decide +kernel

theorem template_chunk4 : (((template.drop (30 * 4)).take 30).map eventChildren).sum = 80144 := by
  decide +kernel

theorem template_chunk5 : (((template.drop (30 * 5)).take 30).map eventChildren).sum = 70219 := by
  decide +kernel

theorem template_chunk6 : (((template.drop (30 * 6)).take 30).map eventChildren).sum = 72763 := by
  decide +kernel

theorem template_chunk7 : (((template.drop (30 * 7)).take 30).map eventChildren).sum = 62146 := by
  decide +kernel

theorem template_chunk8 : (((template.drop (30 * 8)).take 30).map eventChildren).sum = 69687 := by
  decide +kernel

theorem template_chunk9 : (((template.drop (30 * 9)).take 30).map eventChildren).sum = 39881 := by
  decide +kernel

theorem template_chunk10 : (((template.drop (30 * 10)).take 30).map eventChildren).sum = 76581 := by
  decide +kernel

theorem template_chunk11 : (((template.drop (30 * 11)).take 30).map eventChildren).sum = 62025 := by
  decide +kernel

theorem template_chunk12 : (((template.drop (30 * 12)).take 30).map eventChildren).sum = 56238 := by
  decide +kernel

theorem template_chunk13 : (((template.drop (30 * 13)).take 30).map eventChildren).sum = 70976 := by
  decide +kernel

theorem template_chunk14 : (((template.drop (30 * 14)).take 30).map eventChildren).sum = 44097 := by
  decide +kernel

theorem template_chunk15 : (((template.drop (30 * 15)).take 30).map eventChildren).sum = 36487 := by
  decide +kernel

/-- The child calls of the template, summed in chunks of thirty events so that no single kernel
check holds the whole template. -/
theorem template_children : (template.map eventChildren).sum = 1041408 := by
  rw [sum_map_chunks eventChildren 30 16 template (by rw [template_length]),
    show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, template_chunk0, template_chunk1, template_chunk2, template_chunk3, template_chunk4, template_chunk5, template_chunk6, template_chunk7, template_chunk8, template_chunk9, template_chunk10, template_chunk11, template_chunk12, template_chunk13, template_chunk14, template_chunk15]
  rfl

/-- **The T16 node makes exactly `F = 1,041,408` child calls.** -/
theorem nodeProgram_children : programChildren nodeProgram = 1041408 := by
  rw [nodeProgram, programChildren_flatMap, ← template_children]
  refine congrArg List.sum ?_
  exact List.map_congr_left fun te hte => eventProgram_children te hte

end IntegerMultBounds.Networks.Certificates.T16.Impl