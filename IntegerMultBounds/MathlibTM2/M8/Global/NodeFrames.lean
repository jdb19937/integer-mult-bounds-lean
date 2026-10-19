module

public import IntegerMultBounds.MathlibTM2.M8.Global.Node

/-!
# The frames along each node wire

Every node wire meets at most one invocation of each stage and at most one correction, so its
frame sequence is the placed sequence of one local wire per part (`fseq_wX`, `fseq_wY`, …). The
data and side slots pass through increasing frames (`pairwise_wX`, `pairwise_wY`, `pairwise_side1`,
`pairwise_side2`); the temporaries make one move each. So the node's gate list is aligned
(`chainOk_node`, `gatesOk_node`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

theorem fseq_flatMap {ι β : Type} [DecidableEq ι] (w : ι) (l : List β) (f : β → List (FGate ι d)) :
    fseq w (l.flatMap f) = l.flatMap fun b => fseq w (f b) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, fseq_append, ih, List.flatMap_cons]

theorem lineOf_idem (k : V) : lineOf k * lineOf k = lineOf k :=
  lineFrame_idem (leafTriple_isTriple k.2)

theorem lframe_lineOf (k : V) : LFrame (lineOf k) :=
  lframe_of (lineOf_idem k) (lineFrame_bounded (leafTriple_isTriple k.2))

theorem nodeFrame_V (k : V) : nodeFrame k = lineOf k := nodeFrame_leaf k.2

theorem hyper_V (k : V) : hyperFrame (leafTriple k) = 1 - lineOf k := rfl

/-- The stage-one parts away from invocation `T`. -/
theorem fseq1_out {k : Wire} {T : V} (hk : ∀ w, InR w → place1 T w ≠ k) :
    fseq k (gates1 T) = [] :=
  fseq_place_out _ stage1 (fun v hv w hw => stageGate_inR (stage1_gates v hv) w hw) hk

theorem fseq2_out {k : Wire} {S : V} (hk : ∀ w, InR w → place2 S w ≠ k) :
    fseq k (gates2 S) = [] :=
  fseq_place_out _ stage2 (fun v hv w hw => stageGate_inR (stage2_gates v hv) w hw) hk

theorem fseq1_at (T : V) {w : LW} (hw : InR w) :
    fseq (place1 T w) (gates1 T) = (fseq w stage1).map (lift1 (lineOf T)) :=
  fseq_place (place1_injOn T) _ stage1 (fun v hv w hw => stageGate_inR (stage1_gates v hv) w hw) hw

theorem fseq2_at (S : V) {w : LW} (hw : InR w) :
    fseq (place2 S w) (gates2 S) = (fseq w stage2).map (lift2 (lineOf S)) :=
  fseq_place (place2_injOn S) _ stage2 (fun v hv w hw => stageGate_inR (stage2_gates v hv) w hw) hw

theorem fseq_allGates (k : Wire) : fseq k allGates =
    allV.flatMap (fun T => fseq k (gates1 T)) ++ allV.flatMap (fun S => fseq k (gates2 S)) ++
      allPairs.flatMap fun p => fseq k (corrGates p.1 p.2) := by
  rw [allGates_def, fseq_append, fseq_append, fseq_flatMap, fseq_flatMap, fseq_flatMap]

/-- The correction of pair `p` along a wire. -/
theorem fseq_corr (k : Wire) (S T : V) : fseq k (corrGates S T) =
    (if k = wCorr S T ∨ k = wX S T then [1] else []) ++
      (if k = wY S T ∨ k = wCorr S T then [1 - uFrame S T] else []) := by
  rw [corrGates, fseq_cons, fseq_cons]
  simp only [mem_touched_add]
  split_ifs <;> rfl

/-! ### Which invocation meets a wire -/

theorem place1_eq {T : V} {w : LW} (hw : InR w) {k : Wire} (h : place1 T w = k) :
    (∃ S : V, w = .inl (.x S) ∧ k = wX S T) ∨ (∃ S : V, w = .inl (.y S) ∧ k = wY S T) ∨
    (∃ s : Slot, w = .inl (.aux s) ∧ k = wSide false T s) ∨ (∃ c, w = .inr c ∧ k = wCentre false T c) := by
  rcases place1_cases T w hw with ⟨S, rfl, e⟩ | ⟨S, rfl, e⟩ | ⟨s, rfl, e⟩ | ⟨c, rfl, e⟩ <;>
    rw [e] at h <;> subst h
  · exact Or.inl ⟨S, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨S, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨c, rfl, rfl⟩))

theorem place2_eq {S : V} {w : LW} (hw : InR w) {k : Wire} (h : place2 S w = k) :
    (∃ T : V, w = .inl (.x T) ∧ k = wY S T) ∨ (∃ T : V, w = .inl (.y T) ∧ k = wX S T) ∨
    (∃ s : Slot, w = .inl (.aux s) ∧ k = wSide true S s) ∨ (∃ c, w = .inr c ∧ k = wCentre true S c) := by
  rcases place2_cases S w hw with ⟨T, rfl, e⟩ | ⟨T, rfl, e⟩ | ⟨s, rfl, e⟩ | ⟨c, rfl, e⟩ <;>
    rw [e] at h <;> subst h
  · exact Or.inl ⟨T, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨T, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨c, rfl, rfl⟩))

/-- Stage one along a wire it meets in invocation `T` only. -/
theorem fseq1_part {k : Wire} {T : V} {w : LW} (hw : InR w) (hk : place1 T w = k)
    (hother : ∀ T', T' ≠ T → ∀ w', InR w' → place1 T' w' ≠ k) :
    allV.flatMap (fun T' => fseq k (gates1 T')) = (fseq w stage1).map (lift1 (lineOf T)) := by
  rw [flatMap_one allV_nodup (mem_allV T) fun T' _ hT' => fseq1_out (hother T' hT'), ← hk,
    fseq1_at T hw]

theorem fseq1_none {k : Wire} (hother : ∀ T w, InR w → place1 T w ≠ k) :
    allV.flatMap (fun T' => fseq k (gates1 T')) = [] :=
  List.flatMap_eq_nil_iff.mpr fun T _ => fseq1_out (hother T)

theorem fseq2_part {k : Wire} {S : V} {w : LW} (hw : InR w) (hk : place2 S w = k)
    (hother : ∀ S', S' ≠ S → ∀ w', InR w' → place2 S' w' ≠ k) :
    allV.flatMap (fun S' => fseq k (gates2 S')) = (fseq w stage2).map (lift2 (lineOf S)) := by
  rw [flatMap_one allV_nodup (mem_allV S) fun S' _ hS' => fseq2_out (hother S' hS'), ← hk,
    fseq2_at S hw]

theorem fseq2_none {k : Wire} (hother : ∀ S w, InR w → place2 S w ≠ k) :
    allV.flatMap (fun S' => fseq k (gates2 S')) = [] :=
  List.flatMap_eq_nil_iff.mpr fun S _ => fseq2_out (hother S)

theorem fseqc_part {k : Wire} (S T : V) (hother : ∀ p ∈ allPairs, p ≠ (S, T) →
    fseq k (corrGates p.1 p.2) = []) :
    allPairs.flatMap (fun p => fseq k (corrGates p.1 p.2)) = fseq k (corrGates S T) :=
  flatMap_one allPairs_nodup (mem_allPairs S T) hother

theorem fseqc_none {k : Wire} (hother : ∀ S T, fseq k (corrGates S T) = []) :
    allPairs.flatMap (fun p => fseq k (corrGates p.1 p.2)) = [] :=
  List.flatMap_eq_nil_iff.mpr fun p _ => hother p.1 p.2

theorem wX_inj {S T S' T' : V} (h : wX S T = wX S' T') : S = S' ∧ T = T' := by
  simpa [wX] using h

theorem wY_inj {S T S' T' : V} (h : wY S T = wY S' T') : S = S' ∧ T = T' := by
  simpa [wY] using h

/-- The frames along `X S T`. -/
theorem fseq_wX (S T : V) : fseq (wX S T) allGates =
    (fseq (.inl (.x S)) stage1).map (lift1 (lineOf T)) ++
      (fseq (.inl (.y T)) stage2).map (lift2 (lineOf S)) ++ [1] := by
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
    (fseq (.inl (.y S)) stage1).map (lift1 (lineOf T)) ++
      (fseq (.inl (.x T)) stage2).map (lift2 (lineOf S)) ++ [1 - uFrame S T] := by
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

theorem corr_none_world {k : Wire} (hk : ∀ S T, k ≠ wX S T ∧ k ≠ wY S T ∧ k ≠ wCorr S T) :
    ∀ S T, fseq k (corrGates S T) = [] := by
  intro S T
  obtain ⟨h1, h2, h3⟩ := hk S T
  rw [fseq_corr, ite_eq_right (by rintro (h | h) <;> contradiction),
    ite_eq_right (by rintro (h | h) <;> contradiction)]
  rfl

/-- The frames along a side slot of stage one. -/
theorem fseq_side1 (T : V) (s : Slot) : fseq (wSide false T s) allGates =
    (fseq (.inl (.aux s)) stage1).map (lift1 (lineOf T)) := by
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
    (fseq (.inl (.aux s)) stage2).map (lift2 (lineOf S)) := by
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
    (fseq (.inr c) stage1).map (lift1 (lineOf T)) := by
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
    (fseq (.inr c) stage2).map (lift2 (lineOf S)) := by
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

/-! ### Increasing frames along the contract roles -/

theorem connector_x {P Q : LMat} (hQ : Q * Q = Q) : Le (lift1 Q 1) (lift2 P Q) := by
  have h : kron (1 - P) Q + kron P Q = kron 1 Q := by rw [← kron_add_left, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · rw [lift1, lift2, Matrix.mul_add, kron_mul, kron_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hQ, h]
  · rw [lift1, lift2, Matrix.add_mul, kron_mul, kron_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, hQ, h]

theorem connector_y {P Q : LMat} (hP : P * P = P) : Le (lift1 Q (1 - P)) (lift2 P 0) := by
  have h1 : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP]; abel
  rw [lift2_zero]
  exact ⟨by rw [lift1, kron_mul, h1, Matrix.mul_one], by rw [lift1, kron_mul, h1, Matrix.one_mul]⟩

theorem pairwise_map_lift {f : LMat → Mat 529} (hf : ∀ {A B}, Le A B → Le (f A) (f B))
    {l : List LMat} (h : l.Pairwise Le) : (l.map f).Pairwise Le :=
  List.pairwise_map.mpr (h.imp hf)

theorem pairwise_reflect {l : List LMat} (h : l.Pairwise Le) :
    ((l.map (1 - ·)).reverse).Pairwise Le := by
  rw [List.pairwise_reverse, List.pairwise_map]
  exact h.imp le_compl

theorem le_one' {d : ℕ} (A : Mat d) : Le A 1 := le_one A

/-- **Along `X S T`** the frames increase from `P_S ⊗ Q_T` to `1`. -/
theorem pairwise_wX (S T : V) : (gInit (wX S T) :: fseq (wX S T) allGates).Pairwise Le := by
  have hQ := lineOf_idem T
  have hP := lineOf_idem S
  obtain ⟨hc1, hel1⟩ := chain1_x S.2
  obtain ⟨hc2, hel2⟩ := chain1_y T.2
  rw [nodeFrame_V] at hc1 hel1
  rw [fseq_wX, show gInit (wX S T) = lift1 (lineOf T) (lineOf S) from rfl, fseq2_reg]
  have hA1 : (lift1 (lineOf T) (lineOf S) :: (fseq (.inl (.x S)) stage1).map (lift1 (lineOf T))).Pairwise Le := by
    rw [← List.map_cons]; exact pairwise_map_lift (le_lift1 hQ) hc1
  have hA2 := pairwise_map_lift (le_lift2 hP) (pairwise_reflect (List.Pairwise.of_cons hc2))
  have hE1 : ∀ a ∈ lift1 (lineOf T) (lineOf S) :: (fseq (.inl (.x S)) stage1).map (lift1 (lineOf T)),
      Le a (lift1 (lineOf T) 1) := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_lift1 hQ (le_one _)
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
      exact le_lift1 hQ (le_one _)
  have hE2 : ∀ b ∈ (((fseq (.inl (.y T)) stage1).map (1 - ·)).reverse).map (lift2 (lineOf S)),
      Le (lift2 (lineOf S) (lineOf T)) b := by
    intro b hb
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
    rcases hel2 g hg with rfl | rfl
    · rw [sub_zero, lift2_one]; exact le_one _
    · rw [hyper_V, sub_sub_cancel]; exact le_refl_of_idem (isFrame_lift2 (lframe_lineOf S) (lframe_lineOf T)).idem
  rw [← List.cons_append, ← List.cons_append]
  refine pw_app (pw_app hA1 hA2 fun a ha b hb => ?_) (List.pairwise_singleton _ _)
    fun a _ b hb => by rw [List.mem_singleton.mp hb]; exact le_one a
  exact le_trans' (le_trans' (hE1 a ha) (connector_x hQ)) (hE2 b hb)

/-- **Along `Y S T`** the frames increase from `0` to `1 − P_S ⊗ Q_T`. -/
theorem pairwise_wY (S T : V) : (gInit (wY S T) :: fseq (wY S T) allGates).Pairwise Le := by
  have hQ := lineOf_idem T
  have hP := lineOf_idem S
  obtain ⟨hc1, hel1⟩ := chain1_y S.2
  obtain ⟨hc2, hel2⟩ := chain1_x T.2
  rw [nodeFrame_V] at hc2 hel2
  rw [fseq_wY, show gInit (wY S T) = 0 from rfl, fseq2_reg]
  have hB1 : (0 :: (fseq (.inl (.y S)) stage1).map (lift1 (lineOf T))).Pairwise Le := by
    rw [← lift1_zero (lineOf T), ← List.map_cons]; exact pairwise_map_lift (le_lift1 hQ) hc1
  have hB2 := pairwise_map_lift (le_lift2 hP) (pairwise_reflect (List.Pairwise.of_cons hc2))
  have hU : 1 - uFrame S T = lift2 (lineOf S) (1 - lineOf T) := (lift2_compl _ _).symm
  have hE1 : ∀ a ∈ 0 :: (fseq (.inl (.y S)) stage1).map (lift1 (lineOf T)),
      Le a (lift1 (lineOf T) (1 - lineOf S)) := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact zero_le _
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
      rcases hel1 f hf with rfl | rfl
      · rw [lift1_zero]; exact zero_le _
      · rw [hyper_V]
        exact le_refl_of_idem (isFrame_lift1 (lframe_lineOf T) (SmallFrame.compl
          ⟨hP, (lineFrame_bounded (leafTriple_isTriple S.2)).mono (ten_pow_mono (by norm_num))⟩)).idem
  have hE2 : ∀ b ∈ (((fseq (.inl (.x T)) stage1).map (1 - ·)).reverse).map (lift2 (lineOf S)),
      Le (lift2 (lineOf S) 0) b ∧ Le b (1 - uFrame S T) := by
    intro b hb
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
    rw [hU]
    rcases hel2 g hg with rfl | rfl
    · exact ⟨le_lift2 hP (zero_le _),
        le_refl_of_idem (isFrame_lift2 (lframe_lineOf S) (SmallFrame.compl
          ⟨hQ, (lineFrame_bounded (leafTriple_isTriple T.2)).mono (ten_pow_mono (by norm_num))⟩)).idem⟩
    · rw [sub_self]
      exact ⟨le_refl_of_idem (isFrame_lift2 (lframe_lineOf S) lframe_zero).idem,
        le_lift2 hP (zero_le _)⟩
  have hlast : Le (lift2 (lineOf S) 0) (1 - uFrame S T) := by rw [hU]; exact le_lift2 hP (zero_le _)
  rw [← List.cons_append, ← List.cons_append]
  refine pw_app (pw_app hB1 hB2 fun a ha b hb => ?_) (List.pairwise_singleton _ _)
    fun a ha b hb => ?_
  · exact le_trans' (le_trans' (hE1 a ha) (connector_y hP)) (hE2 b hb).1
  · rw [List.mem_singleton.mp hb]
    rcases List.mem_append.mp ha with ha | ha
    · exact le_trans' (le_trans' (hE1 a ha) (connector_y hP)) hlast
    · exact (hE2 a ha).2

theorem pairwise_side1 (T : V) (s : Slot) :
    (gInit (wSide false T s) :: fseq (wSide false T s) allGates).Pairwise Le := by
  rw [fseq_side1, show gInit (wSide false T s) = 0 from rfl, ← lift1_zero (lineOf T), ← List.map_cons]
  exact pairwise_map_lift (le_lift1 (lineOf_idem T)) (chain1_aux s)

theorem pairwise_side2 (S : V) (s : Slot) :
    (gInit (wSide true S s) :: fseq (wSide true S s) allGates).Pairwise Le := by
  rw [fseq_side2, show gInit (wSide true S s) = 0 from rfl, fseq2_reg]
  refine List.pairwise_cons.mpr ⟨fun b _ => zero_le b, ?_⟩
  exact pairwise_map_lift (le_lift2 (lineOf_idem S))
    (pairwise_reflect (List.Pairwise.of_cons (chain1_aux s)))

/-! ### The node is aligned -/

theorem cmp_of_le {d : ℕ} {A B : Mat d} (h : Le A B) : Cmp A B := Or.inl h

theorem chain_of_pairwise {d : ℕ} {l : List (Mat d)} (h : l.Pairwise Le) : l.IsChain Cmp :=
  (List.Pairwise.isChain h).imp fun _ _ h => cmp_of_le h

/-- A temporary's frames: one frame, then another. -/
theorem chain_temp {d : ℕ} {a b : Mat d} (ha : a * a = a) (hb : b * b = b) (hab : Cmp a b)
    (l : List ℕ) : (a :: a :: l.map fun _ => b).IsChain Cmp := by
  rw [List.isChain_cons_cons]
  refine ⟨Or.inl (le_refl_of_idem ha), ?_⟩
  induction l with
  | nil => exact List.isChain_singleton _
  | cons x l ih =>
    rw [List.map_cons, List.isChain_cons_cons]
    refine ⟨hab, ?_⟩
    clear ih
    induction l with
    | nil => exact List.isChain_singleton _
    | cons y l ih' =>
      rw [List.map_cons, List.isChain_cons_cons]
      exact ⟨Or.inl (le_refl_of_idem hb), ih'⟩

theorem lframe_lift1 (T : V) {K : LMat} (hK : LFrame K) : IsFrame (lift1 (lineOf T) K) :=
  isFrame_lift1 (lframe_lineOf T) hK

theorem lframe_lift2 (S : V) {K : LMat} (hK : LFrame K) : IsFrame (lift2 (lineOf S) K) :=
  isFrame_lift2 (lframe_lineOf S) hK

/-- **Every node wire passes through comparable frames.** -/
theorem chainOk_node : ChainOk gInit allGates := by
  intro k
  rcases k with ((⟨S, T⟩ | ⟨S, T⟩ | ⟨b, k, s⟩) | (⟨b, k, c⟩ | ⟨S, T⟩ | ⟨⟩))
  · exact chain_of_pairwise (pairwise_wX S T)
  · exact chain_of_pairwise (pairwise_wY S T)
  · cases b
    · exact chain_of_pairwise (pairwise_side1 k s)
    · exact chain_of_pairwise (pairwise_side2 k s)
  · cases b
    · show (gInit (wCentre false k c) :: fseq (wCentre false k c) allGates).IsChain Cmp
      rw [fseq_centre1, fseq1_tmp, show gInit (wCentre false k c) = lift1 (lineOf k) (starFrame c)
        from rfl, List.map_cons, List.map_map]
      have hF := lframe_lift1 k (smallFrame_star c.2).lframe
      have h0 := lframe_lift1 k lframe_zero
      have : (lift1 (lineOf k) ∘ fun _ : ℕ => (0 : LMat)) = fun _ => lift1 (lineOf k) 0 := rfl
      rw [this]
      exact chain_temp hF.idem h0.idem (Or.inr (le_lift1 (lineOf_idem k) (zero_le _))) _
    · show (gInit (wCentre true k c) :: fseq (wCentre true k c) allGates).IsChain Cmp
      rw [fseq_centre2, fseq2_tmp, show gInit (wCentre true k c) = lift2 (lineOf k) (1 - starFrame c)
        from rfl, List.map_cons, List.map_map]
      have hF := lframe_lift2 k (smallFrame_star c.2).compl
      have h1 := lframe_lift2 k lframe_one
      have : (lift2 (lineOf k) ∘ fun _ : ℕ => (1 : LMat)) = fun _ => lift2 (lineOf k) 1 := rfl
      rw [this]
      exact chain_temp hF.idem h1.idem (Or.inl (le_lift2 (lineOf_idem k) (le_one _))) _
  · show (gInit (wCorr S T) :: fseq (wCorr S T) allGates).IsChain Cmp
    rw [fseq_wCorr, show gInit (wCorr S T) = 1 from rfl, List.isChain_cons_cons,
      List.isChain_cons_cons]
    have hU : 1 - uFrame S T = lift2 (lineOf S) (1 - lineOf T) := (lift2_compl _ _).symm
    refine ⟨Or.inl (le_refl_of_idem (by simp)), Or.inr (le_one _), List.isChain_singleton _⟩
  · show (gInit wJunk :: fseq wJunk allGates).IsChain Cmp
    rw [fseq_wJunk]
    exact List.isChain_singleton _

theorem isFrame_one {d : ℕ} : IsFrame (1 : Mat d) :=
  ⟨by simp, fun i j => by
    rw [Matrix.one_apply]; split_ifs <;> simp [-Nat.reducePow] <;>
      exact Nat.one_le_pow 4000 10 (by norm_num)⟩

theorem isFrame_corr (S T : V) : IsFrame (1 - uFrame S T) := by
  rw [uFrame, ← lift2_compl]
  exact lframe_lift2 S (SmallFrame.compl
    ⟨lineOf_idem T, (lineFrame_bounded (leafTriple_isTriple T.2)).mono (ten_pow_mono (by norm_num))⟩)

/-- **The node's gates are XOR gates on frames.** -/
theorem gatesOk_node : GatesOk allGates := by
  intro v hv
  rw [allGates_def, List.mem_append, List.mem_append, List.mem_flatMap, List.mem_flatMap,
    List.mem_flatMap] at hv
  rcases hv with (⟨T, -, hv⟩ | ⟨S, -, hv⟩) | ⟨⟨S, T⟩, -, hv⟩
  · rw [gates1] at hv
    exact gatesOk_place (place1_injOn T) (lift1 (lineOf T)) stage1
      (fun v hv w hw => stageGate_inR (stage1_gates v hv) w hw)
      (fun v hv => stageGate_xor (stage1_gates v hv))
      (fun v hv => lframe_lift1 T (stage1_frames v hv).lframe) v hv
  · rw [gates2] at hv
    refine gatesOk_place (place2_injOn S) (lift2 (lineOf S)) stage2
      (fun v hv w hw => stageGate_inR (stage2_gates v hv) w hw)
      (fun v hv => stageGate_xor (stage2_gates v hv))
      (fun v hv => ?_) v hv
    obtain ⟨K, hK, he⟩ := stage2_frames v hv
    rw [he]
    exact lframe_lift2 S hK.compl
  · simp only [corrGates, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨isFrame_one, _, _, by simp [wCorr, wX], rfl⟩
    · exact ⟨isFrame_corr S T, _, _, by simp [wCorr, wY], rfl⟩

theorem isFrame_gInit : ∀ k, IsFrame (gInit k) := by
  intro k
  rcases k with ((⟨S, T⟩ | ⟨S, T⟩ | ⟨b, k, s⟩) | (⟨b, k, c⟩ | ⟨S, T⟩ | ⟨⟩))
  · exact lframe_lift1 T (lframe_lineOf S)
  · show IsFrame 0
    exact ⟨by simp, fun i j => by simp [-Nat.reducePow]; exact Nat.one_le_pow 4000 10 (by norm_num)⟩
  · show IsFrame 0
    exact ⟨by simp, fun i j => by simp [-Nat.reducePow]; exact Nat.one_le_pow 4000 10 (by norm_num)⟩
  · cases b
    · exact lframe_lift1 k (smallFrame_star c.2).lframe
    · exact lframe_lift2 k (smallFrame_star c.2).compl
  · exact isFrame_one
  · show IsFrame 0
    exact ⟨by simp, fun i j => by simp [-Nat.reducePow]; exact Nat.one_le_pow 4000 10 (by norm_num)⟩

end

end IntegerMultBounds.MathlibTM2.M8.Global
