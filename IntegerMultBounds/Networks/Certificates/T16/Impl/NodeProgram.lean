module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.UnitProgram

/-! **The T16 node program.** Every local template event is its invocation program and every
other template event is the programs of its unit operations. On every data family the node
program acts exactly as the node's unit operations, so it applies `C_all` to every family, for
every representation of the 73-bit operators. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh Streams Multiplicative

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

/-- The program of one template event. -/
noncomputable def eventProgram : TEvent → List (TInstr NodeUnit)
  | .local s r => callProgram s r
  | .idle r p c0 c1 => (eventOps (.idle r p c0 c1)).flatMap unitProgram
  | .bridge r d s c => (eventOps (.bridge r d s c)).flatMap unitProgram
  | .terminalY r ps => (eventOps (.terminalY r ps)).flatMap unitProgram
  | .terminal r n => (eventOps (.terminal r n)).flatMap unitProgram

/-- **The T16 node program.** -/
noncomputable def nodeProgram : List (TInstr NodeUnit) := template.flatMap eventProgram

/-- Arrays agree on every family. -/
def FamEq (y y' : NodeUnit → S) : Prop := ∀ j, y (.inl j) = y' (.inl j)

/-- A unit operation acting on families only. -/
def OnFamilies : UnitOp → Prop
  | .phase u _ _ => ∃ j, u = .inl j
  | .shear d s _ => (∃ j, d = .inl j) ∧ ∃ j, s = .inl j
  | .exchange x w => (∃ j, x = .inl j) ∧ ∃ j, w = .inl j

theorem streamUnit_inl (r a : ℕ) (i : Fin 8) : ∃ j, streamUnit r a i = .inl j := ⟨_, rfl⟩

theorem onFamilies_toUnitOp (r a : ℕ) (e : Event) : OnFamilies (toUnitOp r a e) := by
  cases e <;> simp only [toUnitOp, OnFamilies] <;>
    first | exact streamUnit_inl _ _ _ | exact ⟨streamUnit_inl _ _ _, streamUnit_inl _ _ _⟩

theorem onFamilies_eventOps (te : TEvent) : ∀ o ∈ eventOps te, OnFamilies o := by
  intro o ho
  simp only [eventOps, List.mem_flatMap, List.mem_map] at ho
  obtain ⟨r, -, a, -, e, -, rfl⟩ := ho
  exact onFamilies_toUnitOp r a e

omit [Module ℚ S] [IsScalarTower ℚ ℂ S] in
theorem famEq_run (M : ℕ → Op S) (o : UnitOp) (ho : OnFamilies o) {y y' : NodeUnit → S}
    (h : FamEq y y') : FamEq (o.run M y) (o.run M y') := by
  intro j
  cases o with
  | phase u a v =>
    obtain ⟨k, rfl⟩ := ho
    simp only [UnitOp.run]
    by_cases hj : j = k
    · subst hj; simp [h j]
    · simp [Function.update_of_ne (fun e => hj (Sum.inl_injective e)), h j]
  | shear d s c =>
    obtain ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩ := ho
    simp only [UnitOp.run]
    by_cases hj : j = k
    · subst hj; simp [h j, h l]
    · simp [Function.update_of_ne (fun e => hj (Sum.inl_injective e)), h j]
  | exchange x w =>
    obtain ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩ := ho
    simp only [UnitOp.run]
    by_cases hj : j = l
    · subst hj; simp [h k]
    · rw [Function.update_of_ne (fun e => hj (Sum.inl_injective e)),
        Function.update_of_ne (fun e => hj (Sum.inl_injective e))]
      by_cases hk : j = k
      · subst hk; simp [h l]
      · rw [Function.update_of_ne (fun e => hk (Sum.inl_injective e)),
          Function.update_of_ne (fun e => hk (Sum.inl_injective e)), h j]

omit [Module ℚ S] [IsScalarTower ℚ ℂ S] in
theorem famEq_runUnits (M : ℕ → Op S) (os : List UnitOp) (hos : ∀ o ∈ os, OnFamilies o)
    {y y' : NodeUnit → S} (h : FamEq y y') : FamEq (runUnits M os y) (runUnits M os y') := by
  induction os generalizing y y' with
  | nil => exact h
  | cons o os ih =>
    exact ih (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho'))
      (famEq_run M o (hos o List.mem_cons_self) h)

theorem unitProper_eventOps (te : TEvent) : ∀ o ∈ eventOps te, unitProper o := by
  intro o ho
  simp only [eventOps, List.mem_flatMap, List.mem_map, List.mem_range] at ho
  obtain ⟨r, hr, a, ha, e, -, rfl⟩ := ho
  cases e with
  | phase _ _ => trivial
  | shear _ _ _ => trivial
  | exchange p =>
    intro he
    exact pairX_ne_pairY p (streamUnit_inj hr ha hr ha he).2.2

omit [IsScalarTower ℚ ℂ S] in
theorem runT_unitPrograms (os : List UnitOp) (hos : ∀ o ∈ os, unitProper o) (y : NodeUnit → S) :
    runT ρ (os.flatMap unitProgram) y = runUnits (portRep ρ) os y := by
  induction os generalizing y with
  | nil => rfl
  | cons o os ih =>
    rw [List.flatMap_cons, runT_append, unitProgram_run ρ o (hos o List.mem_cons_self),
      ih (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho'))]
    rfl

/-- One template event. -/
theorem eventProgram_correct (te : TEvent) (hte : te ∈ template) (y : NodeUnit → S) :
    FamEq (runT ρ (eventProgram te) y) (runUnits (portRep ρ) (eventOps te) y) := by
  cases te with
  | «local» s r =>
    have hsr : s < 9 ∧ r < 16 := by
      have := List.all_eq_true.mp (show template.all (fun te => match te with
        | .local s r => decide (s < 9 ∧ r < 16) | _ => true) = true by decide +kernel) _ hte
      simpa using this
    exact local_correct ρ hsr.1 hsr.2 y
  | idle r p c0 c1 => intro j; rw [eventProgram, runT_unitPrograms ρ _ (unitProper_eventOps _)]
  | bridge r d s c => intro j; rw [eventProgram, runT_unitPrograms ρ _ (unitProper_eventOps _)]
  | terminalY r ps => intro j; rw [eventProgram, runT_unitPrograms ρ _ (unitProper_eventOps _)]
  | terminal r n => intro j; rw [eventProgram, runT_unitPrograms ρ _ (unitProper_eventOps _)]

/-- **The node program acts as the node's unit operations on every family.** -/
theorem nodeProgram_correct (y : NodeUnit → S) :
    FamEq (runT ρ nodeProgram y) (runUnits (portRep ρ) nodeOps y) := by
  unfold nodeProgram nodeOps
  have key : ∀ tes : List TEvent, (∀ te ∈ tes, te ∈ template) → ∀ y y' : NodeUnit → S,
      FamEq y y' → FamEq (runT ρ (tes.flatMap eventProgram) y)
        (runUnits (portRep ρ) (tes.flatMap eventOps) y') := by
    intro tes htes
    induction tes with
    | nil => intro y y' h; exact h
    | cons te tes ih =>
      intro y y' h
      rw [List.flatMap_cons, runT_append, List.flatMap_cons, runUnits_append]
      apply ih (fun te' h' => htes te' (List.mem_cons_of_mem _ h'))
      intro j
      rw [eventProgram_correct ρ te (htes te List.mem_cons_self) y j]
      exact famEq_runUnits _ _ (onFamilies_eventOps te) h j
  exact key template (fun _ h => h) y y (fun _ => rfl)

/-- **The T16 node.** Every family ends with `C_all` applied to its input. -/
theorem nodeProgram_cAll (y : NodeUnit → S) {r a : ℕ} (hr : r < 16) (ha : a < 112) (i : Fin 8) :
    runT ρ nodeProgram y (streamUnit r a i) = ρ cAll (y (streamUnit r a i)) := by
  obtain ⟨j, hj⟩ := streamUnit_inl r a i
  rw [hj, nodeProgram_correct ρ y j, ← hj]
  have h1 := congrFun (view_nodeOps (portRep ρ) hr ha y) i
  rw [h1, run_of_accepts (portRep ρ a) (node_accepts hr ha)]
  change portRep ρ a (ofAdd (fullFrame (portData a)).toFun) (y (streamUnit r a i)) = _
  rw [portRep_apply, show basisOp (portBasis (portData a)) (ofAdd (fullFrame (portData a)).toFun) =
    cAll from portOp_full ha]

end IntegerMultBounds.Networks.Certificates.T16.Impl
