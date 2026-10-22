module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeB
public import IntegerMultBounds.MathlibTM2.M8.Global.SourceStageFramesB
public import IntegerMultBounds.MathlibTM2.M8.Global.AuxStageFramesB
public import IntegerMultBounds.MathlibTM2.M8.Global.TemporaryTraceB

/-! Exact placed frame traces of the gauged design-B node. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem fseq1_out {k : Wire} {T : V} (hk : ∀ w, InR w → place1 T w ≠ k) :
    fseq k (gates1 T) = [] :=
  fseq_place_out _ firstStage (fun v hv => (stage_gate_good assignment v hv).1) hk

theorem fseq2_out {k : Wire} {S : V} (hk : ∀ w, InR w → place2 S w ≠ k) :
    fseq k (gates2 S) = [] :=
  fseq_place_out _ finalStage (fun v hv => (secondStage_gate_good assignment v hv).1) hk

theorem fseq1_at (T : V) {w : LW} (hw : InR w) :
    fseq (place1 T w) (gates1 T) = (fseq w firstStage).map (lift1 (lineOf T)) :=
  fseq_place (place1_injOn T) _ firstStage (fun v hv => (stage_gate_good assignment v hv).1) hw

theorem fseq2_at (S : V) {w : LW} (hw : InR w) :
    fseq (place2 S w) (gates2 S) = (fseq w finalStage).map (lift2 (lineOf S)) :=
  fseq_place (place2_injOn S) _ finalStage (fun v hv => (secondStage_gate_good assignment v hv).1) hw

theorem fseq_allGates (k : Wire) : fseq k allGates =
    allV.flatMap (fun T => fseq k (gates1 T)) ++ allV.flatMap (fun S => fseq k (gates2 S)) ++
      allPairs.flatMap fun p => fseq k (corrGates p.1 p.2) := by
  rw [allGates_def, fseq_append, fseq_append, fseq_flatMap, fseq_flatMap, fseq_flatMap]


theorem fseq1_part {k : Wire} {T : V} {w : LW} (hw : InR w) (hk : place1 T w = k)
    (hother : ∀ T', T' ≠ T → ∀ w', InR w' → place1 T' w' ≠ k) :
    allV.flatMap (fun T' => fseq k (gates1 T')) = (fseq w firstStage).map (lift1 (lineOf T)) := by
  rw [flatMap_one allV_nodup (mem_allV T) fun T' _ hT' => fseq1_out (hother T' hT'), ← hk,
    fseq1_at T hw]

theorem fseq1_none {k : Wire} (hother : ∀ T w, InR w → place1 T w ≠ k) :
    allV.flatMap (fun T' => fseq k (gates1 T')) = [] :=
  List.flatMap_eq_nil_iff.mpr fun T _ => fseq1_out (hother T)

theorem fseq2_part {k : Wire} {S : V} {w : LW} (hw : InR w) (hk : place2 S w = k)
    (hother : ∀ S', S' ≠ S → ∀ w', InR w' → place2 S' w' ≠ k) :
    allV.flatMap (fun S' => fseq k (gates2 S')) = (fseq w finalStage).map (lift2 (lineOf S)) := by
  rw [flatMap_one allV_nodup (mem_allV S) fun S' _ hS' => fseq2_out (hother S' hS'), ← hk,
    fseq2_at S hw]

theorem fseq2_none {k : Wire} (hother : ∀ S w, InR w → place2 S w ≠ k) :
    allV.flatMap (fun S' => fseq k (gates2 S')) = [] :=
  List.flatMap_eq_nil_iff.mpr fun S _ => fseq2_out (hother S)


/-- The frames along `X S T`. -/
theorem fseq_wX (S T : V) : fseq (wX S T) allGates =
    (fseq (.inl (.x S)) firstStage).map (lift1 (lineOf T)) ++
      (fseq (.inl (.y T)) finalStage).map (lift2 (lineOf S)) ++ [1] := by
  rw [fseq_allGates, fseq1_part (show InR (.inl (.x S)) from S.2) (place1_x T S),
    fseq2_part (show InR (.inl (.y T)) from T.2) (place2_y S T),
    fseqc_part S T, fseq_corr]
  · rw [ite_eq_left (Or.inr rfl), ite_eq_right (by rintro (h | h) <;> simp [wX, wY, wCorr] at h),
      List.append_nil]
  · rintro ⟨S', T'⟩ - hp
    rw [fseq_corr]
    have : ¬ (wX S T = wCorr S' T' ∨ wX S T = wX S' T') := by
      rintro (h | h)
      · simp [wX, wCorr] at h
      · exact hp (by obtain ⟨rfl, rfl⟩ := wX_inj h; rfl)
    rw [ite_eq_right this, ite_eq_right (by rintro (h | h) <;> simp [wX, wY, wCorr] at h)]
    rfl
  · intro S' hS' w hw h
    rcases place2_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
    exact hS' e.1.symm
  · intro T' hT' w hw h
    rcases place1_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
    exact hT' e.2.symm

/-- The frames along `Y S T`. -/
theorem fseq_wY (S T : V) : fseq (wY S T) allGates =
    (fseq (.inl (.y S)) firstStage).map (lift1 (lineOf T)) ++
      (fseq (.inl (.x T)) finalStage).map (lift2 (lineOf S)) ++ [1 - uFrame S T] := by
  rw [fseq_allGates, fseq1_part (show InR (.inl (.y S)) from S.2) (place1_y T S),
    fseq2_part (show InR (.inl (.x T)) from T.2) (place2_x S T),
    fseqc_part S T, fseq_corr]
  · rw [ite_eq_right (by rintro (h | h) <;> simp [wX, wY, wCorr] at h), ite_eq_left (Or.inl rfl),
      List.nil_append]
  · rintro ⟨S', T'⟩ - hp
    rw [fseq_corr]
    have : ¬ (wY S T = wY S' T' ∨ wY S T = wCorr S' T') := by
      rintro (h | h)
      · exact hp (by obtain ⟨rfl, rfl⟩ := wY_inj h; rfl)
      · simp [wY, wCorr] at h
    rw [ite_eq_right (by rintro (h | h) <;> simp [wX, wY, wCorr] at h), ite_eq_right this]
    rfl
  · intro S' hS' w hw h
    rcases place2_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
    exact hS' e.1.symm
  · intro T' hT' w hw h
    rcases place1_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
    exact hT' e.2.symm


/-- The frames along a side slot of stage one. -/
theorem fseq_side1 (T : V) (s : Slot) : fseq (wSide false T s) allGates =
    (fseq (.inl (.aux s)) firstStage).map (lift1 (lineOf T)) := by
  rw [fseq_allGates, fseq1_part (show InR (.inl (.aux s)) from s.2) (place1_aux T s),
    fseq2_none, fseqc_none (corr_none_world fun S T => by simp [wSide, wX, wY, wCorr]),
    List.append_nil, List.append_nil]
  · intro S w hw h
    rcases place2_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
  · intro T' hT' w hw h
    rcases place1_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
    exact hT' e.1.symm

/-- The frames along a side slot of stage two. -/
theorem fseq_side2 (S : V) (s : Slot) : fseq (wSide true S s) allGates =
    (fseq (.inl (.aux s)) finalStage).map (lift2 (lineOf S)) := by
  rw [fseq_allGates, fseq1_none, fseq2_part (show InR (.inl (.aux s)) from s.2) (place2_aux S s),
    fseqc_none (corr_none_world fun S T => by simp [wSide, wX, wY, wCorr]), List.nil_append,
    List.append_nil]
  · intro S' hS' w hw h
    rcases place2_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
    exact hS' e.1.symm
  · intro T w hw h
    rcases place1_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e

theorem fseq_centre1 (T : V) (c : Fin 23) : fseq (wCentre false T c) allGates =
    (fseq (.inr c) firstStage).map (lift1 (lineOf T)) := by
  rw [fseq_allGates, fseq1_part (show InR (.inr c) from trivial)
      (show place1 T (.inr c) = wCentre false T c from rfl),
    fseq2_none, fseqc_none (corr_none_world fun S T => by simp [wCentre, wX, wY, wCorr]),
    List.append_nil, List.append_nil]
  · intro S w hw h
    rcases place2_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
  · intro T' hT' w hw h
    rcases place1_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
    exact hT' e.1.symm

theorem fseq_centre2 (S : V) (c : Fin 23) : fseq (wCentre true S c) allGates =
    (fseq (.inr c) finalStage).map (lift2 (lineOf S)) := by
  rw [fseq_allGates, fseq1_none, fseq2_part (show InR (.inr c) from trivial)
      (show place2 S (.inr c) = wCentre true S c from rfl),
    fseqc_none (corr_none_world fun S T => by simp [wCentre, wX, wY, wCorr]), List.nil_append,
    List.append_nil]
  · intro S' hS' w hw h
    rcases place2_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e
    exact hS' e.1.symm
  · intro T w hw h
    rcases place1_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre] at e

theorem fseq_wCorr (S T : V) : fseq (wCorr S T) allGates = [1, 1 - uFrame S T] := by
  rw [fseq_allGates, fseq1_none, fseq2_none, fseqc_part S T, fseq_corr]
  · simp
  · rintro ⟨S', T'⟩ - hp
    rw [fseq_corr]
    have h1 : ¬ (wCorr S T = wCorr S' T' ∨ wCorr S T = wX S' T') := by
      rintro (h | h)
      · exact hp (by simp [wCorr] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      · simp [wX, wCorr] at h
    have h2 : ¬ (wCorr S T = wY S' T' ∨ wCorr S T = wCorr S' T') := by
      rintro (h | h)
      · simp [wY, wCorr] at h
      · exact hp (by simp [wCorr] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rw [ite_eq_right h1, ite_eq_right h2]
    rfl
  · intro S w hw h
    rcases place2_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre, wCorr] at e
  · intro T w hw h
    rcases place1_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wX, wY, wSide, wCentre, wCorr] at e

theorem fseq_wJunk : fseq wJunk allGates = [] := by
  rw [fseq_allGates, fseq1_none, fseq2_none, fseqc_none (corr_none_world fun S T => by
    simp [wJunk, wX, wY, wCorr])]
  · rfl
  · intro S w hw h
    rcases place2_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wJunk, wX, wY, wSide, wCentre] at e
  · intro T w hw h
    rcases place1_eq hw h with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
      simp [wJunk, wX, wY, wSide, wCentre] at e


end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
