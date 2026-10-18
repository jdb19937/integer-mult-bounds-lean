module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.NodeCost
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Machine

/-! **The T16 node on the machine.** Every primitive of the node program is ready: the edge words
and adapters lower dyadic realizations, whose scalars are fourth roots of unity, and the helper
wrappers invert ready monomial words. So the node program lowers to a machine program of odd
factors, translations, slot XORs, slot phases, unit scalars and rational gates, which applies
`C_all` to every family for every representation and makes exactly `1,041,408` child calls. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Pauli

/-! ### Inverses -/

theorem phase_inv (j : ZMod 4) : (phase j)⁻¹ = phase (-j) :=
  (eq_inv_of_mul_eq_one_left (phase_neg_mul j)).symm

theorem Prim.Ready.inv {p : Prim} (h : p.Ready) : p.inv.Ready := by
  cases p with
  | kernel q v => trivial
  | perm G => trivial
  | diag φ =>
    obtain ⟨k, c, d, hφ⟩ := (show Quadratic φ from h)
    refine ⟨-k, -c, -d, fun x => ?_⟩
    change -φ x = _
    rw [hφ]
    simp only [Pi.neg_apply, neg_mul, mul_neg, Finset.sum_neg_distrib]
    ring
  | scale c =>
    obtain ⟨j, rfl⟩ := (show ∃ j : ZMod 4, c = phase j from h)
    exact ⟨-j, phase_inv j⟩

theorem ready_invPrims {ws : List Prim} (h : ∀ p ∈ ws, p.Ready) : ∀ p ∈ invPrims ws, p.Ready := by
  intro p hp
  simp only [invPrims, List.mem_reverse, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact (h q hq).inv

/-! ### Dyadic adapters -/

theorem dyadic_pauli (c : Label) : (pauliRealization c).Dyadic :=
  ⟨good_operator c, good_operator c.inv⟩

theorem dyadic_kernelRealization (q : ZMod 4) (v : Geometry.Address) :
    (kernelRealization q v).Dyadic := by
  unfold kernelRealization
  split_ifs
  · exact dyadic_c v
  · exact (dyadic_c v).symm
  · exact dyadic_pauli _
  · exact dyadic_identity

theorem dyadic_kernelList (gs : List (ZMod 4 × Geometry.Address)) :
    (kernelListRealization gs).Dyadic := by
  apply dyadic_realizeWord
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨g', -, rfl⟩ := hg
  exact dyadic_kernelRealization _ _

theorem dyadic_preAdapter (gs : List (ZMod 4 × Geometry.Address)) (i : ℕ) :
    (preAdapter gs i).Dyadic :=
  (dyadic_kernelList gs).symm.then (dyadic_native i)

theorem dyadic_postAdapter (gs : List (ZMod 4 × Geometry.Address)) (i : ℕ) :
    (postAdapter gs i).Dyadic :=
  (dyadic_native i).symm.then (dyadic_kernelList gs)

/-! ### Ready words -/

theorem ready_edgePrims (a b : ℕ) : ∀ p ∈ edgePrims a b, p.Ready :=
  (Classical.choose_spec (Realization.exists_prims (edgeRealization a b))).2.2 (dyadic_edge a b)

theorem ready_adapterIn (χ : Addr ≃ₗ[ZMod 2] Addr) (gs : List (ZMod 4 × Address 9)) (a : ℕ) :
    ∀ p ∈ adapterIn χ gs a, p.Ready := by
  intro p hp
  rw [adapterIn, List.mem_cons] at hp
  rcases hp with rfl | hp
  · trivial
  · exact (Classical.choose_spec (Realization.exists_prims (preAdapter gs a))).2.2
      (dyadic_preAdapter gs a) p hp

theorem ready_adapterOut (χ : Addr ≃ₗ[ZMod 2] Addr) (gs : List (ZMod 4 × Address 9)) (b : ℕ) :
    ∀ p ∈ adapterOut χ gs b, p.Ready := by
  intro p hp
  rw [adapterOut, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact (Classical.choose_spec (Realization.exists_prims (postAdapter gs b))).2.2
      (dyadic_postAdapter gs b) p hp
  · trivial

theorem ready_dataIn (s a : ℕ) (f : Fin 73 → ZMod 4) (l : ℕ) : ∀ p ∈ dataIn s a f l, p.Ready := by
  unfold dataIn
  split_ifs
  · exact ready_adapterIn _ _ _
  · exact ready_adapterIn _ _ _
  · simp

theorem ready_dataOut (s a : ℕ) (f : Fin 73 → ZMod 4) (l : ℕ) : ∀ p ∈ dataOut s a f l, p.Ready := by
  unfold dataOut
  split_ifs
  · exact ready_adapterOut _ _ _
  · exact ready_adapterOut _ _ _
  · simp

theorem ready_helperIn {P : PortData} (hP : portCheck P = true) (m a b : ℕ) :
    ∀ p ∈ helperIn hP m a b, p.Ready := by
  intro p hp
  rw [helperIn, List.mem_cons] at hp
  rcases hp with rfl | hp
  · trivial
  · exact ready_invPrims (fun q hq => split_ready a b q (List.mem_append_left _ hq)) p hp

theorem ready_helperOut {P : PortData} (hP : portCheck P = true) (m a b : ℕ) :
    ∀ p ∈ helperOut hP m a b, p.Ready := by
  intro p hp
  rw [helperOut, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact ready_invPrims (fun q hq => split_ready a b q (List.mem_append_right _ hq)) p hp
  · trivial

theorem ready_callIn (s r w : ℕ) : ∀ p ∈ callIn s r w, p.Ready := by
  unfold callIn
  dsimp only
  split_ifs
  · exact ready_dataIn _ _ _ _
  · exact ready_dataIn _ _ _ _
  · exact ready_helperIn _ _ _ _
  · simp

theorem ready_callOut (s r w : ℕ) : ∀ p ∈ callOut s r w, p.Ready := by
  unfold callOut
  dsimp only
  split_ifs
  · exact ready_dataOut _ _ _ _
  · exact ready_dataOut _ _ _ _
  · exact ready_helperOut _ _ _ _
  · simp

/-! ### Ready programs -/

variable {ι κ : Type}

theorem ready_prims (w : ι) {ps : List Prim} (h : ∀ p ∈ ps, p.Ready) :
    ∀ i ∈ ps.map (TInstr.prim w), i.Ready := by
  intro i hi
  rw [List.mem_map] at hi
  obtain ⟨p, hp, rfl⟩ := hi
  exact h p hp

theorem ready_rename (u : ι → κ) {prog : List (TInstr ι)} (h : ∀ i ∈ prog, i.Ready) :
    ∀ i ∈ prog.map (TInstr.rename u), i.Ready := by
  intro i hi
  rw [List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  cases j with
  | gate g => trivial
  | prim w p => exact h _ hj

theorem ready_regBlocks (reg : ℕ → κ) (rs : List ℕ) (word : ℕ → List Prim)
    (h : ∀ w, ∀ p ∈ word w, p.Ready) : ∀ i ∈ regBlocks reg rs word, i.Ready := by
  intro i hi
  rw [regBlocks, List.mem_flatMap] at hi
  obtain ⟨w, -, hw⟩ := hi
  exact ready_prims _ (h w) i hw

theorem ready_implEvents (es : List (FramedEventTrace.Event ℕ ℕ ℚ)) :
    ∀ i ∈ es.flatMap implEvent, i.Ready := by
  intro i hi
  rw [List.mem_flatMap] at hi
  obtain ⟨e, -, he⟩ := hi
  cases e with
  | edge w old next => exact ready_prims _ (ready_edgePrims old next) i he
  | gate g _ => rw [implEvent, List.mem_singleton] at he; subst he; trivial
  | clear w _ => rw [implEvent, List.mem_singleton] at he; subst he; trivial
  | copy s t _ => rw [implEvent, List.mem_singleton] at he; subst he; trivial

theorem ready_callProgram (s r : ℕ) : ∀ i ∈ callProgram s r, i.Ready := by
  intro i hi
  rw [callProgram, invocation, List.mem_append, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact ready_regBlocks _ _ _ (ready_callIn s r) i hi
  · refine ready_rename _ ?_ i hi
    split
    · exact ready_implEvents _
    · exact ready_implEvents _
  · exact ready_regBlocks _ _ _ (ready_callOut s r) i hi

theorem ready_unitProgram (o : UnitOp) : ∀ i ∈ unitProgram o, i.Ready := by
  cases o with
  | phase u a v =>
    refine ready_prims _ fun p hp => ?_
    simp only [phasePrims, List.mem_map] at hp
    obtain ⟨k, -, rfl⟩ := hp
    trivial
  | shear d s c => intro i hi; rw [unitProgram, List.mem_singleton] at hi; subst hi; trivial
  | exchange x w =>
    intro i hi
    simp only [unitProgram, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> trivial

theorem ready_unitPrograms (os : List UnitOp) : ∀ i ∈ os.flatMap unitProgram, i.Ready := by
  intro i hi
  rw [List.mem_flatMap] at hi
  obtain ⟨o, -, ho⟩ := hi
  exact ready_unitProgram o i ho

/-- **Every primitive of the node program is ready.** -/
theorem nodeProgram_ready : ∀ i ∈ nodeProgram, i.Ready := by
  intro i hi
  rw [nodeProgram, List.mem_flatMap] at hi
  obtain ⟨te, -, hte⟩ := hi
  cases te with
  | «local» s r => exact ready_callProgram s r i hte
  | idle r p c0 c1 => exact ready_unitPrograms _ i hte
  | bridge r d s c => exact ready_unitPrograms _ i hte
  | terminalY r ps => exact ready_unitPrograms _ i hte
  | terminal r n => exact ready_unitPrograms _ i hte

/-! ### The machine program -/

/-- **The T16 node as a machine program.** -/
noncomputable def machineProgram : List (MInstr NodeUnit) := lowerProgram nodeProgram

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

omit [IsScalarTower ℚ ℂ S] in
theorem machineProgram_run (y : NodeUnit → S) : runM ρ machineProgram y = runT ρ nodeProgram y :=
  (lowerProgram_spec ρ nodeProgram nodeProgram_ready).1 y

/-- **The machine program applies `C_all` to every family.** -/
theorem machineProgram_cAll (y : NodeUnit → S) {r a : ℕ} (hr : r < 16) (ha : a < 112) (i : Fin 8) :
    runM ρ machineProgram y (streamUnit r a i) = ρ cAll (y (streamUnit r a i)) := by
  rw [machineProgram_run, nodeProgram_cAll ρ y hr ha i]

/-- **The machine program makes exactly `F = 1,041,408` child calls.** -/
theorem machineProgram_children : mprogramChildren machineProgram = 1041408 := by
  rw [machineProgram, (lowerProgram_spec (S := Arrays 73) (MonoidHom.id _) nodeProgram
    nodeProgram_ready).2, nodeProgram_children]

end IntegerMultBounds.Networks.Certificates.T16.Impl
