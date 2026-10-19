module

public import IntegerMultBounds.MathlibTM2.M8.Global.FrameMachine

/-!
# Aligned gate lists

A framed gate (`FGate`) is an XOR gate with the frame its wires must share. `autoSteps cur L`
moves each touched wire from its current frame to the gate's frame (`move`: up if nested, down
otherwise) and then runs the gate. Validity is a property of each wire separately: the frames of
the gates touching it (`fseq`), after its starting frame, form a chain of comparable frames
(`ChainOk`). Under it the aligned list is a valid framed list (`valid_autoSteps`), its logical run
is the module run of its gates (`logicRun_autoSteps`), and each wire ends in the frame of the last
gate touching it (`finalFrames_autoSteps`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical

variable {ι : Type} [DecidableEq ι] {d : ℕ}

/-- A gate with its frame. -/
structure FGate (ι : Type) (d : ℕ) where
  gate : Circuit.Gate ι (ZMod 2)
  frame : Mat d

/-- `A` lies in `B`. -/
def Le (A B : Mat d) : Prop := A * B = A ∧ B * A = A

/-- Comparable frames. -/
def Cmp (A B : Mat d) : Prop := Le A B ∨ Le B A

/-- Move wire `i` from frame `A` to frame `B`. -/
def move (i : ι) (A B : Mat d) : List (FStep ι d) :=
  if A = B then [] else if Le A B then [.up i A B] else [.down i A B]

/-- Move the wires `ws` to frame `F`, in order. -/
def alignMoves : (ι → Mat d) → List ι → Mat d → List (FStep ι d)
  | _, [], _ => []
  | cur, w :: ws, F => move w (cur w) F ++ alignMoves (Function.update cur w F) ws F

/-- The frames after the wires `ws` move to `F`. -/
def setF (cur : ι → Mat d) (ws : List ι) (F : Mat d) : ι → Mat d :=
  fun w => if w ∈ ws then F else cur w

/-- Align and run each gate. -/
def autoSteps : (ι → Mat d) → List (FGate ι d) → List (FStep ι d)
  | _, [] => []
  | cur, v :: rest =>
    alignMoves cur (FramedCircuit.touched v.gate) v.frame ++ [.gate v.gate v.frame] ++
      autoSteps (setF cur (FramedCircuit.touched v.gate) v.frame) rest

/-- The frames of the gates touching `w`, in order. -/
def fseq (w : ι) (L : List (FGate ι d)) : List (Mat d) :=
  (L.filter fun v => w ∈ FramedCircuit.touched v.gate).map FGate.frame

/-- The gates are XOR gates with frame matrices. -/
def GatesOk (L : List (FGate ι d)) : Prop :=
  ∀ v ∈ L, IsFrame v.frame ∧ ∃ dst src, dst ≠ src ∧ v.gate = ReversibleFanout.add dst src

/-- Every wire passes through comparable frames. -/
abbrev ChainOk (cur : ι → Mat d) (L : List (FGate ι d)) : Prop :=
  ∀ w, List.IsChain Cmp (cur w :: fseq w L)

/-! ### Lists of framed steps -/

theorem valid_append : ∀ (a b : List (FStep ι d)) (fr : ι → Mat d) (z : ι → Prop),
    Valid (a ++ b) fr z ↔ Valid a fr z ∧ Valid b (finalFrames a fr) (finalZeros a z)
  | [], b, fr, z => by simp [Valid, finalFrames, finalZeros]
  | s :: a, b, fr, z => by
    simp only [List.cons_append, Valid, finalFrames, finalZeros, valid_append a b]
    tauto

theorem finalFrames_append : ∀ (a b : List (FStep ι d)) (fr : ι → Mat d),
    finalFrames (a ++ b) fr = finalFrames b (finalFrames a fr)
  | [], _, _ => rfl
  | _ :: a, b, _fr => finalFrames_append a b _

theorem finalZeros_append : ∀ (a b : List (FStep ι d)) (z : ι → Prop),
    finalZeros (a ++ b) z = finalZeros b (finalZeros a z)
  | [], _, _ => rfl
  | _ :: a, b, _z => finalZeros_append a b _

theorem logicRun_append {E : Type} [AddCommGroup E] [Module (ZMod 2) E] :
    ∀ (a b : List (FStep ι d)) (x : ι → E), logicRun (a ++ b) x = logicRun b (logicRun a x)
  | [], _, _ => rfl
  | _ :: a, b, _x => logicRun_append a b _

omit [DecidableEq ι] in
theorem edgeRanks_append : ∀ (a b : List (FStep ι d)), edgeRanks (a ++ b) = edgeRanks a + edgeRanks b
  | [], _ => by simp [edgeRanks]
  | s :: a, b => by
    cases s <;> simp [edgeRanks, edgeRanks_append a b] <;> omega

omit [DecidableEq ι] in
theorem physOf_append (a b : List (FStep ι d)) : physOf (a ++ b) = physOf a ++ physOf b := by
  simp [physOf, List.flatMap_append]

/-! ### Moves -/

theorem le_refl_of_idem {A : Mat d} (h : A * A = A) : Le A A := ⟨h, h⟩

theorem move_valid {i : ι} {A B : Mat d} (fr : ι → Mat d) (z : ι → Prop) (hi : fr i = A)
    (hB : IsFrame B) (hc : Cmp A B) :
    Valid (move i A B) fr z ∧ finalFrames (move i A B) fr = Function.update fr i B ∧
      finalZeros (move i A B) z = z := by
  unfold move
  split_ifs with h1 h2
  · subst h1
    refine ⟨trivial, ?_, rfl⟩
    rw [← hi, Function.update_eq_self]
    rfl
  · exact ⟨⟨⟨hi, hB, h2.1, h2.2⟩, trivial⟩, rfl, rfl⟩
  · have h3 : Le B A := hc.resolve_left h2
    exact ⟨⟨⟨hi, hB, h3.2, h3.1⟩, trivial⟩, rfl, rfl⟩

theorem logicRun_move {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (i : ι) (A B : Mat d)
    (x : ι → E) : logicRun (move i A B) x = x := by
  unfold move
  split_ifs <;> rfl

theorem alignMoves_valid (F : Mat d) (hF : IsFrame F) :
    ∀ (ws : List ι) (fr : ι → Mat d) (z : ι → Prop), ws.Nodup → (∀ w ∈ ws, Cmp (fr w) F) →
      Valid (alignMoves fr ws F) fr z ∧ finalFrames (alignMoves fr ws F) fr = setF fr ws F ∧
        finalZeros (alignMoves fr ws F) z = z
  | [], fr, z, _, _ => ⟨trivial, by funext w; simp [setF, alignMoves, finalFrames], rfl⟩
  | w :: ws, fr, z, hnd, hc => by
    rw [List.nodup_cons] at hnd
    obtain ⟨h1, h2, h3⟩ := move_valid (i := w) fr z rfl hF (hc w (by simp))
    have hc' : ∀ w' ∈ ws, Cmp (Function.update fr w F w') F := fun w' hw' => by
      have hne : w' ≠ w := fun h => hnd.1 (by rw [← h]; exact hw')
      rw [Function.update_of_ne hne]
      exact hc w' (List.mem_cons_of_mem _ hw')
    obtain ⟨h4, h5, h6⟩ := alignMoves_valid F hF ws (Function.update fr w F) z hnd.2 hc'
    simp only [alignMoves]
    rw [valid_append, finalFrames_append, finalZeros_append, h2, h3]
    refine ⟨⟨h1, h4⟩, ?_, h6⟩
    rw [h5]
    funext w'
    simp only [setF, List.mem_cons]
    by_cases hw : w' = w
    · subst hw; simp
    · simp [hw]

theorem logicRun_alignMoves {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (F : Mat d) :
    ∀ (ws : List ι) (fr : ι → Mat d) (x : ι → E), logicRun (alignMoves fr ws F) x = x
  | [], _, _ => rfl
  | w :: ws, fr, x => by
    simp only [alignMoves]
    rw [logicRun_append, logicRun_move, logicRun_alignMoves F ws]

/-! ### Aligned lists -/

omit [DecidableEq ι] in
theorem touched_nodup {g : Circuit.Gate ι (ZMod 2)}
    (h : ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src) :
    (FramedCircuit.touched g).Nodup := by
  obtain ⟨dst, src, hne, rfl⟩ := h
  simp [FramedCircuit.touched, ReversibleFanout.add, hne]

theorem fseq_cons (w : ι) (v : FGate ι d) (L : List (FGate ι d)) :
    fseq w (v :: L) = if w ∈ FramedCircuit.touched v.gate then v.frame :: fseq w L else fseq w L := by
  simp only [fseq, List.filter_cons]
  split_ifs with h1 h2 h2 <;> simp_all

/-- **Aligned lists are valid.** -/
theorem valid_autoSteps : ∀ (L : List (FGate ι d)) (cur : ι → Mat d) (z : ι → Prop),
    GatesOk L → ChainOk cur L →
      Valid (autoSteps cur L) cur z ∧
        finalFrames (autoSteps cur L) cur = (fun w => (fseq w L).getLast?.getD (cur w))
  | [], cur, z, _, _ => ⟨trivial, by funext w; simp [fseq, finalFrames, autoSteps]⟩
  | v :: rest, cur, z, hg, hc => by
    obtain ⟨hF, hx⟩ := hg v (by simp)
    have hnd := touched_nodup hx
    have hcv : ∀ w ∈ FramedCircuit.touched v.gate, Cmp (cur w) v.frame := by
      intro w hw
      have := hc w
      rw [fseq_cons, ite_eq_left hw, List.isChain_cons_cons] at this
      exact this.1
    obtain ⟨h1, h2, h3⟩ := alignMoves_valid v.frame hF _ cur z hnd hcv
    set cur' := setF cur (FramedCircuit.touched v.gate) v.frame
    have hg' : GatesOk rest := fun v' hv' => hg v' (List.mem_cons_of_mem _ hv')
    have hc' : ChainOk cur' rest := by
      intro w
      have := hc w
      rw [fseq_cons] at this
      simp only [cur', setF]
      split_ifs at this ⊢ with hw
      · exact (List.isChain_cons_cons.mp this).2
      · exact this
    obtain ⟨h4, h5⟩ := valid_autoSteps rest cur' (FStep.zeros (.gate v.gate v.frame) z) hg' hc'
    simp only [autoSteps, List.append_assoc]
    rw [valid_append, finalFrames_append, h2, h3, valid_append, finalFrames_append]
    have hok : (FStep.gate v.gate v.frame).Ok cur' z := ⟨fun w hw => by simp [cur', setF, hw], hx⟩
    refine ⟨⟨h1, ⟨hok, trivial⟩, h4⟩, ?_⟩
    rw [show finalFrames [FStep.gate v.gate v.frame] cur' = cur' from rfl, h5]
    funext w
    rw [fseq_cons]
    simp only [cur', setF]
    split_ifs with hw
    · cases h : fseq w rest with
      | nil => simp
      | cons a l => simp [List.getLast?_cons]
    · rfl

theorem logicRun_autoSteps {E : Type} [AddCommGroup E] [Module (ZMod 2) E] :
    ∀ (L : List (FGate ι d)) (cur : ι → Mat d) (x : ι → E),
      logicRun (autoSteps cur L) x = FramedCircuit.moduleRun (L.map FGate.gate) x
  | [], _, _ => rfl
  | v :: rest, cur, x => by
    simp only [autoSteps]
    rw [logicRun_append, logicRun_append, logicRun_alignMoves, List.map_cons,
      FramedCircuit.moduleRun_cons, logicRun_autoSteps rest]
    rfl

end

end IntegerMultBounds.MathlibTM2.M8.Global
