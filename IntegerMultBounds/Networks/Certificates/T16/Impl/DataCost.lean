module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.AllCalls

/-! The data adapters make no child calls. Through the data chart, the local list of a stream
frame always runs over the nine low port basis vectors; its odd vectors are `B_0` (a source at
entry), all nine (a source at exit), none (a target at entry) or `B_1, …, B_8` (a target at
exit). These span exactly the native entry and exit labels of the data registers, so every
data adapter is a rank-zero lowering. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh Streams Pauli Geometry

variable {P : PortData}

/-- The local list of a stage-zero split. -/
theorem split0_gs (hP : portCheck P = true) (f : Fin 73 → ZMod 4) :
    (split0 hP f).gs = lowIndices.map fun k => (f k, lowPart (portBasis P k)) := rfl

/-- The local list of a later split, with the chart removed. -/
theorem splitStage_gs (hP : portCheck P = true) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) (f : Fin 73 → ZMod 4) :
    (splitStage hP s hs f).gs = (f 0, lowPart (portBasis P 0)) ::
      (List.finRange 8).map fun i => (f (entering s hs i), lowPart (portBasis P ⟨i.val + 1, by omega⟩)) := by
  change ((0 :: (List.finRange 8).map (entering s hs)).map fun k =>
    (f k, lowPart ((stageChart hP s hs).symm (portBasis P k)))) = _
  rw [List.map_cons, stageChart_low0, List.map_map]
  refine congrArg (List.cons _) ?_
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, stageChart_entering]

/-- The nine low basis vectors of a port, as nine-bit vectors. -/
def lowBasis (P : PortData) : List (Address 9) :=
  (List.finRange 9).map fun i => lowPart (portBasis P ⟨i.val, by omega⟩)

/-- The local list of the data split of a frame, at any stage. -/
noncomputable def dataGs (hP : portCheck P = true) (s : ℕ) (f : Fin 73 → ZMod 4) :
    List (ZMod 4 × Address 9) :=
  if hs : 1 ≤ s ∧ s ≤ 8 then (splitStage hP s hs f).gs else (split0 hP f).gs

theorem lowIndices_eq : lowIndices = (List.finRange 9).map fun i => (⟨i.val, by omega⟩ : Fin 73) := by
  decide

theorem dataGs_eq (hP : portCheck P = true) (s : ℕ) (f : Fin 73 → ZMod 4) :
    dataGs hP s f = ((dataIndices s).map f).zip (lowBasis P) := by
  unfold dataGs dataIndices
  by_cases hs : 1 ≤ s ∧ s ≤ 8
  · simp only [hs, and_self, dite_true]
    rw [splitStage_gs]
    simp only [stageIndices, List.map_cons, lowBasis, List.finRange_succ, List.map_map]
    rfl
  · simp only [hs, dite_false]
    rw [split0_gs, lowIndices_eq, lowBasis, List.map_map, List.map_map, List.zip_map']
    rfl

/-! ### Orthonormal odd vectors -/

/-- An orthonormal list of nine-bit vectors. -/
def OrthoList (l : List (Address 9)) : Prop :=
  l.Pairwise (fun u v => Tableau.dot u v = 0) ∧ ∀ v ∈ l, Tableau.dot v v = 1

theorem OrthoList.sublist {l l' : List (Address 9)} (h : OrthoList l) (hs : l'.Sublist l) :
    OrthoList l' := ⟨h.1.sublist hs, fun v hv => h.2 v (hs.subset hv)⟩

theorem oddSum_eq (gs : List (ZMod 4 × Address 9)) (b : Address 9) :
    oddSum gs b = ((oddVecs gs).map fun v => Tableau.dot v b • v).sum := by
  simp [oddSum, oddVecs, List.map_map, Function.comp_def]

theorem proj_of_ortho (l : List (Address 9)) (h : OrthoList l) :
    ∀ v ∈ l, (l.map fun u => Tableau.dot u v • u).sum = v := by
  induction l with
  | nil => intro v hv; simp at hv
  | cons a l ih =>
    intro v hv
    have hpw := List.pairwise_cons.mp h.1
    have hl : OrthoList l := ⟨hpw.2, fun u hu => h.2 u (List.mem_cons_of_mem _ hu)⟩
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · rw [h.2 v List.mem_cons_self, one_smul]
      have hz : (l.map fun u => Tableau.dot u v • u).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
        rw [Tableau.dot_symm, hpw.1 u hu, zero_smul]
      rw [hz, add_zero]
    · rw [show Tableau.dot a v = 0 from hpw.1 v hv, zero_smul, zero_add, ih hl v hv]

/-- **Matching from orthonormality and span.** -/
theorem matches_of {gs : List (ZMod 4 × Address 9)} {i : ℕ} (ho : OrthoList (oddVecs gs))
    (hspan : Submodule.span Geometry.F {v | v ∈ oddVecs gs} = (Geometry.catalog i).space) :
    Matches gs i := ⟨fun v hv => by rw [oddSum_eq]; exact proj_of_ortho _ ho v hv, hspan⟩

theorem OrthoList.nodup {l : List (Address 9)} (h : OrthoList l) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    have hpw := List.pairwise_cons.mp h.1
    refine List.nodup_cons.mpr ⟨fun ha => ?_, ih ⟨hpw.2, fun v hv => h.2 v (List.mem_cons_of_mem _ hv)⟩⟩
    have h1 := h.2 a List.mem_cons_self
    rw [hpw.1 a ha] at h1
    exact zero_ne_one h1

theorem OrthoList.finrank_span {l : List (Address 9)} (h : OrthoList l) :
    Module.finrank Geometry.F (Submodule.span Geometry.F {v | v ∈ l}) = l.length := by
  have hli : LinearIndependent Geometry.F (fun i : Fin l.length => l.get i) := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun i => Tableau.dot (l.get i))
    · intro i j hij
      have hne : l.get i ≠ l.get j := fun e => hij (h.nodup.get_inj_iff.mp e)
      rcases lt_or_gt_of_ne (fun e : i.val = j.val => hij (Fin.ext e)) with hlt | hlt
      · exact List.pairwise_iff_get.mp h.1 i j hlt
      · rw [Tableau.dot_symm]; exact List.pairwise_iff_get.mp h.1 j i hlt
    · intro i
      exact h.2 _ (List.get_mem l i)
  have hr : Set.range (fun i : Fin l.length => l.get i) = {v | v ∈ l} := by
    ext v
    simp [List.mem_iff_get]
  rw [← hr, finrank_span_eq_card hli, Fintype.card_fin]

/-! ### Odd vectors by parity pattern -/

theorem oddVecs_zip (cs : List (ZMod 4)) (bs : List (Address 9)) (hl : cs.length = bs.length) :
    oddVecs (cs.zip bs) = ((bs.zip (cs.map isOdd)).filter (·.2)).map (·.1) := by
  induction cs generalizing bs with
  | nil => simp [oddVecs]
  | cons c cs ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.length_cons, add_left_inj] at hl
      simp only [List.zip_cons_cons, List.map_cons, oddVecs, List.filter_cons] at ih ⊢
      split_ifs <;> simp [ih bs hl]

/-! ### Spans of the four cases -/

theorem space_rank_zero {i : ℕ} (h : (Geometry.catalog i).data.rank = 0) :
    (Geometry.catalog i).space = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [Geometry.catalog_dimension, h]

theorem space_rank_nine {i : ℕ} (h : (Geometry.catalog i).data.rank = 9) :
    (Geometry.catalog i).space = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [Geometry.catalog_dimension, h]
  simp

theorem span_ortho_nine {l : List (Address 9)} (h : OrthoList l) (hl : l.length = 9) :
    Submodule.span Geometry.F {v | v ∈ l} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [h.finrank_span, hl]
  simp

theorem space_rank_one {i : ℕ} (h : (Geometry.catalog i).data.rank = 1) :
    (Geometry.catalog i).space = Submodule.span Geometry.F
      {v | v ∈ [(Geometry.catalog i).data.vectors ⟨0, by omega⟩]} := by
  change Submodule.span _ (Set.range _) = _
  congr 1
  ext v
  simp only [Set.mem_range, List.mem_singleton, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, rfl⟩
    congr 1
    ext
    have := j.isLt
    simp only [h] at this
    simp
    omega
  · rintro rfl
    exact ⟨_, rfl⟩

/-- Both sides of the target exit lie in the complement of `q` with dimension eight. -/
theorem span_eq_of_complement {U V : Submodule Geometry.F (Address 9)} {q : Address 9}
    (hq : Tableau.dot q q = 1) (hU : U ≤ Geometry.binaryOrthogonal (Submodule.span Geometry.F {q}))
    (hV : V ≤ Geometry.binaryOrthogonal (Submodule.span Geometry.F {q}))
    (hUr : Module.finrank Geometry.F U = 8) (hVr : Module.finrank Geometry.F V = 8) : U = V := by
  have hq0 : q ≠ 0 := by
    intro e
    rw [e, map_zero] at hq
    exact zero_ne_one hq
  have hW : Module.finrank Geometry.F (Geometry.binaryOrthogonal (Submodule.span Geometry.F {q})) = 8 := by
    rw [Geometry.binaryOrthogonal_finrank, finrank_span_singleton hq0]
  have e1 := Submodule.eq_of_le_of_finrank_eq hU (hUr.trans hW.symm)
  have e2 := Submodule.eq_of_le_of_finrank_eq hV (hVr.trans hW.symm)
  rw [e1, e2]

theorem le_complement {l : List (Address 9)} {q : Address 9} (h : ∀ v ∈ l, Tableau.dot q v = 0) :
    Submodule.span Geometry.F {v | v ∈ l} ≤ Geometry.binaryOrthogonal (Submodule.span Geometry.F {q}) := by
  rw [Submodule.span_le]
  intro v hv
  rw [SetLike.mem_coe, Geometry.binaryOrthogonal, LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  change Tableau.dot (c • q) v = 0
  rw [map_smul, LinearMap.smul_apply, h v hv, smul_zero]

/-! ### The data checks -/

theorem lowBasis_ortho (hP : portCheck P = true) : OrthoList (lowBasis P) := by
  have hloc : ∀ i : Fin 9, portBasis P ⟨i.val, by omega⟩ =
      padLow (lowPart (portBasis P ⟨i.val, by omega⟩)) := fun i => portBasis_local hP _ (by simp)
  have hdot : ∀ i j : Fin 9, Tableau.dot (lowPart (portBasis P ⟨i.val, by omega⟩))
      (lowPart (portBasis P ⟨j.val, by omega⟩)) = if i = j then 1 else 0 := by
    intro i j
    have h := portBasis_orthonormal hP ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    rw [hloc i, hloc j, padLow, padLow, binary_join] at h
    simp only [map_zero, add_zero] at h
    change Labels.binary 9 _ _ = _
    rw [h]
    simp [Fin.ext_iff]
  constructor
  · rw [lowBasis, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (R := fun i j : Fin 9 => i ≠ j) ?_ ?_
    · intro i j _ _ hij
      rw [hdot]; simp [hij]
    · exact (List.nodup_finRange 9)
  · intro v hv
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
    rw [hdot]; simp

/-- The parity patterns of the four data frames on the chart. -/
def dataPatternCheck (s a : ℕ) : Bool :=
  (((dataIndices s).map (frameX s a)).map isOdd ==
      [true, false, false, false, false, false, false, false, false]) &&
    (((dataIndices s).map (frameX (s + 1) a)).map isOdd == List.replicate 9 true) &&
    (((dataIndices s).map (frameY s a)).map isOdd == List.replicate 9 false) &&
    (((dataIndices s).map (frameY (s + 1) a)).map isOdd == false :: List.replicate 8 true)

theorem dataPatterns : (List.range 9).all (fun s => (List.range 112).all (dataPatternCheck s)) = true := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.T16.Impl
