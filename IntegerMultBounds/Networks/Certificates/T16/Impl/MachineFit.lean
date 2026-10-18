module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.NodeReady
public import IntegerMultBounds.Networks.Certificates.T16.Impl.HalfGates

/-! **The fitted T16 machine program.** Every gate of the T16 machine program has dyadic
coefficients: the native words' scalar rows have power-of-two denominators (a kernel check over
both traces), their clears and copies and the shears and exchanges of the unit operations are
integral. So the fitted machine program has only half-integral gates, applies `C_all` to every
family and makes exactly `1,041,408` child calls. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh Streams

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- A power of two below `2^64`. -/
def isPow2 (n : ℕ) : Bool := (List.range 64).any fun k => n == 2 ^ k

theorem isPow2_spec {n : ℕ} (h : isPow2 n = true) : ∃ k, n = 2 ^ k := by
  simp only [isPow2, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨k, -, hk⟩ := h
  exact ⟨k, hk⟩

/-- The dyadic check of a gate. -/
def dyadicB (g : Circuit.Gate ι ℚ) : Bool :=
  g.terms.all (fun p => isPow2 p.2.den) &&
    (g.terms.length == 1 || g.terms.all fun p => (2 * p.2).den == 1)

theorem dyadicB_spec {g : Circuit.Gate ι ℚ} (h : dyadicB g = true) : DyadicGate g := by
  simp only [dyadicB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨fun p hp => isPow2_spec (h.1 p hp), h.2⟩

/-- The scalar rows of a framed trace pass the dyadic check. -/
def framedDyadic (es : List (FramedEventTrace.Event ℕ ℕ ℚ)) : Bool :=
  es.all fun e => match e with
    | .gate g _ => dyadicB g
    | _ => true

theorem forward_dyadic : framedDyadic (Trace.framed Trace.forwardEvents) = true := by decide +kernel

theorem backward_dyadic : framedDyadic (Trace.framed Trace.backwardEvents) = true := by
  decide +kernel

theorem dyadic_implEvents (es : List (FramedEventTrace.Event ℕ ℕ ℚ)) (h : framedDyadic es = true) :
    ∀ g, TInstr.gate g ∈ es.flatMap implEvent → DyadicGate g := by
  intro g hg
  rw [List.mem_flatMap] at hg
  obtain ⟨e, he, hg⟩ := hg
  have hc := List.all_eq_true.mp h e he
  cases e with
  | edge w old next => simp [implEvent] at hg
  | gate g' _ =>
    simp only [implEvent, List.mem_singleton, TInstr.gate.injEq] at hg
    subst hg
    exact dyadicB_spec hc
  | clear w _ =>
    simp only [implEvent, List.mem_singleton, TInstr.gate.injEq] at hg
    subst hg
    refine ⟨fun p hp => ⟨0, ?_⟩, Or.inl rfl⟩
    simp only [FramedEventTrace.clearGate, List.mem_singleton] at hp
    subst hp; rfl
  | copy s t _ =>
    simp only [implEvent, List.mem_singleton, TInstr.gate.injEq] at hg
    subst hg
    refine ⟨fun p hp => ⟨0, ?_⟩, Or.inr fun p hp => ?_⟩ <;>
      simp only [FramedEventTrace.copyGate, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl <;> norm_num

theorem dyadic_rename (u : ι → κ) {prog : List (TInstr ι)}
    (h : ∀ g, TInstr.gate g ∈ prog → DyadicGate g) :
    ∀ g, TInstr.gate g ∈ prog.map (TInstr.rename u) → DyadicGate g := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨i, hi, he⟩ := hg
  cases i with
  | gate g₀ =>
    simp only [TInstr.rename, TInstr.gate.injEq] at he
    subst he
    obtain ⟨hd, hl⟩ := h g₀ hi
    refine ⟨fun p hp => ?_, ?_⟩
    · simp only [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact hd q hq
    · rcases hl with hl | hl
      · left; simpa using hl
      · right
        intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        exact hl q hq
  | prim w p => simp [TInstr.rename] at he

theorem no_gate_prims (w : ι) (ps : List Prim) (g : Circuit.Gate ι ℚ) :
    TInstr.gate g ∉ ps.map (TInstr.prim w) := by
  simp

theorem dyadic_callProgram (s r : ℕ) : ∀ g, TInstr.gate g ∈ callProgram s r → DyadicGate g := by
  intro g hg
  rw [callProgram, invocation, List.mem_append, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · rw [regBlocks, List.mem_flatMap] at hg
    obtain ⟨w, -, hw⟩ := hg
    exact absurd hw (no_gate_prims _ _ g)
  · refine dyadic_rename _ ?_ g hg
    split
    · exact dyadic_implEvents _ backward_dyadic
    · exact dyadic_implEvents _ forward_dyadic
  · rw [regBlocks, List.mem_flatMap] at hg
    obtain ⟨w, -, hw⟩ := hg
    exact absurd hw (no_gate_prims _ _ g)

theorem dyadic_unitProgram (o : UnitOp) : ∀ g, TInstr.gate g ∈ unitProgram o → DyadicGate g := by
  intro g hg
  cases o with
  | phase u a v => exact absurd hg (no_gate_prims _ _ g)
  | shear d s c =>
    simp only [unitProgram, List.mem_singleton, TInstr.gate.injEq] at hg
    subst hg
    refine ⟨fun p hp => ⟨0, ?_⟩, Or.inl rfl⟩
    simp only [List.mem_singleton] at hp
    subst hp
    simp
  | exchange x w =>
    simp only [unitProgram, List.mem_cons, List.not_mem_nil, or_false, TInstr.gate.injEq] at hg
    rcases hg with rfl | rfl | rfl <;>
      refine ⟨fun p hp => ⟨0, ?_⟩, Or.inl rfl⟩ <;>
      simp only [List.mem_singleton] at hp <;> subst hp <;> rfl

theorem dyadic_nodeProgram : ∀ g, TInstr.gate g ∈ nodeProgram → DyadicGate g := by
  intro g hg
  rw [nodeProgram, List.mem_flatMap] at hg
  obtain ⟨te, -, hte⟩ := hg
  have hu : ∀ os : List UnitOp, TInstr.gate g ∈ os.flatMap unitProgram → DyadicGate g := by
    intro os h
    rw [List.mem_flatMap] at h
    obtain ⟨o, -, ho⟩ := h
    exact dyadic_unitProgram o g ho
  cases te with
  | «local» s r => exact dyadic_callProgram s r g hte
  | idle r p c0 c1 => exact hu _ hte
  | bridge r d s c => exact hu _ hte
  | terminalY r ps => exact hu _ hte
  | terminal r n => exact hu _ hte

theorem dyadic_machineProgram : ∀ g, MInstr.gate g ∈ machineProgram → DyadicGate g := by
  intro g hg
  rw [machineProgram, lowerProgram, List.mem_flatMap] at hg
  obtain ⟨i, hi, hg⟩ := hg
  cases i with
  | gate g₀ =>
    simp only [lowerInstr, List.mem_singleton, MInstr.gate.injEq] at hg
    subst hg
    exact dyadic_nodeProgram _ hi
  | prim w p => simp [lowerInstr] at hg

/-! ### The fitted program -/

/-- **The T16 node as a fitted machine program.** -/
noncomputable def fittedProgram : List (MInstr NodeUnit) := fitProgram machineProgram

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

/-- **The fitted program applies `C_all` to every family.** -/
theorem fittedProgram_cAll (y : NodeUnit → S) {r a : ℕ} (hr : r < 16) (ha : a < 112) (i : Fin 8) :
    runM ρ fittedProgram y (streamUnit r a i) = ρ cAll (y (streamUnit r a i)) := by
  rw [fittedProgram, (fitProgram_spec ρ machineProgram).1, machineProgram_cAll ρ y hr ha i]

/-- **The fitted program makes exactly `F = 1,041,408` child calls.** -/
theorem fittedProgram_children : mprogramChildren fittedProgram = 1041408 := by
  rw [fittedProgram, (fitProgram_spec (S := Arrays 73) (MonoidHom.id _) machineProgram).2,
    machineProgram_children]

/-- **Every gate of the fitted program is half-integral.** -/
theorem fittedProgram_half : ∀ g, MInstr.gate g ∈ fittedProgram → HalfGate g :=
  fitProgram_half _ dyadic_machineProgram

end IntegerMultBounds.Networks.Certificates.T16.Impl
