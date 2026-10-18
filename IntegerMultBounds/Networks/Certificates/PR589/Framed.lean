module

public import IntegerMultBounds.Networks.Certificates.PR589.Copy.Boundary
public import IntegerMultBounds.Networks.Certificates.PR589.Frames.Boundary
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Model
public import IntegerMultBounds.Networks.Certificates.PR589.Bounds
public import IntegerMultBounds.Networks.Certificates.PR589.Word

/-!
# Framed execution of the selected PR589 word

`execute frameOf` runs the complete physical word on frame-encoded registers:
* the compiled D/A phases (`Frames.before_scatter_compiled`);
* the nine distinct-frame COPY/ADD/ERASE windows through the temporary register 661
  (`Copy.decoded_scatter`);
* the compiled B/C phases (`Frames.after_scatter_compiled`);
* the final alignment edges to the full frames (`Frames.final_alignment_compiled`).

`execute_endpoint` composes these on arbitrary dirty streams. Every register is decoded from
its initial frame, the literal scalar word acts on the decoded values, and the result is encoded
in its final frame. `FramedDirty` combines this with the scalar dirty endpoint.

These are exact operator identities. Tape costs and the physical hosting of the nine stages
are separate.
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Framed

open Frames (initialRefs finalRefs beforeScatter after234 framedGate scatterFinish)

section Generic

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The physical framed execution of the complete word. -/
def execute (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E) (x : ℕ → E) : ℕ → E :=
  FramedCircuit.run (FramedCircuit.edges (fun i => frameOf (Frames.snapshot after234 i))
      (fun i => frameOf (finalRefs i)) (List.range 661))
    (FramedCircuit.run (FramedCircuit.compile (fun i => frameOf (scatterFinish beforeScatter i))
        ((sectionB ++ sectionC).map (framedGate frameOf)))
      (Copy.run frameOf Copy.lifecycles
        (FramedCircuit.run (FramedCircuit.compile (fun i => frameOf (Frames.snapshot initialRefs i))
            ((sectionD ++ sectionA).map (framedGate frameOf))) x)))

theorem moduleRun_append (p q : List (Circuit.Gate ℕ (ZMod 2))) (x : ℕ → E) :
    FramedCircuit.moduleRun (p ++ q) x = FramedCircuit.moduleRun q (FramedCircuit.moduleRun p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

/-- Gates whose targets lie below `661` leave every higher register unchanged. -/
theorem moduleRun_high (gs : List RawGate) (hgs : ∀ g ∈ gs, g.target < 661) (x : ℕ → E) (j : ℕ)
    (hj : 661 ≤ j) : FramedCircuit.moduleRun (gs.map RawGate.toCircuit) x j = x j := by
  apply FramedCircuit.moduleRun_preserves
  intro g hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
  have := hgs r hr
  simp only [RawGate.toCircuit]
  omega

theorem program_target_lt (g : RawGate) (hg : g ∈ program) : g.target < 661 := by
  have h := List.all_eq_true.mp program_bounded g hg
  simp only [RawGate.bounded, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem sectionDA_target_lt (g : RawGate) (hg : g ∈ sectionD ++ sectionA) : g.target < 661 :=
  program_target_lt g (by
    simp only [program, List.mem_append] at hg ⊢
    tauto)

theorem sectionScatter_target_lt (g : RawGate) (hg : g ∈ sectionscatter) : g.target < 661 :=
  program_target_lt g (by
    simp only [program, List.mem_append]
    tauto)

/-- One COPY window changes only the temporary register and its targets. -/
theorem copy_execute_other (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E) (life : Copy.Lifecycle)
    (hn : life.targets.Nodup) (ht : 661 ∉ life.targets) (stored : ℕ → E) (j : ℕ) (hj : j ≠ 661)
    (hjt : j ∉ life.targets) : Copy.execute frameOf life stored j = stored j := by
  rw [Copy.execute, Function.update_of_ne hj, Copy.addTargets_eq _ hn ht]
  simp [hjt, Function.update_of_ne hj]

theorem copy_run_high (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E) (stored : ℕ → E) (j : ℕ)
    (hj : 661 < j) : Copy.run frameOf Copy.lifecycles stored j = stored j := by
  have key : ∀ lives : List Copy.Lifecycle, (∀ life ∈ lives, life ∈ Copy.lifecycles) →
      ∀ stored : ℕ → E, Copy.run frameOf lives stored j = stored j := by
    intro lives
    induction lives with
    | nil => intro _ _; rfl
    | cons life rest ih =>
      intro hsub stored
      have hl := hsub life (List.mem_cons_self)
      obtain ⟨hn, ht, _, _⟩ := Copy.wellformed life hl
      have hjt : j ∉ life.targets := fun hm => by
        have := Copy.target_bounds life hl j hm
        omega
      rw [Copy.run, ih (fun l hm => hsub l (List.mem_cons_of_mem _ hm)),
        copy_execute_other frameOf life hn ht stored j (by omega) hjt]
  exact key _ (fun _ h => h) stored

end Generic

section Streams

variable {Ω : Type*}

/-- The decoded values after D/A vanish above the retained registers. -/
theorem stored_of_high (stored : Fin 661 → Ω → ZMod 2) :
    FramedCircuit.moduleRun ((sectionD ++ sectionA).map RawGate.toCircuit) (Copy.extendStored stored) =
      Copy.extendStored (fun i : Fin 661 =>
        FramedCircuit.moduleRun ((sectionD ++ sectionA).map RawGate.toCircuit)
          (Copy.extendStored stored) i.val) := by
  funext j
  by_cases hj : j < 661
  · simp [Copy.extendStored, hj]
  · rw [moduleRun_high _ sectionDA_target_lt _ j (by omega)]
    simp [Copy.extendStored, hj]

/-- The nine COPY windows act on the D/A output as the logical scatter, in the same frames. -/
theorem copy_phase (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) :
    Copy.run frameOf Copy.lifecycles (FramedCircuit.encode (fun i => frameOf (beforeScatter i))
        (FramedCircuit.moduleRun ((sectionD ++ sectionA).map RawGate.toCircuit)
          (Copy.extendStored stored))) =
      FramedCircuit.encode (fun i => frameOf (scatterFinish beforeScatter i))
        (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit)
          (FramedCircuit.moduleRun ((sectionD ++ sectionA).map RawGate.toCircuit)
            (Copy.extendStored stored))) := by
  rw [stored_of_high stored]
  generalize (fun i : Fin 661 => FramedCircuit.moduleRun ((sectionD ++ sectionA).map RawGate.toCircuit)
    (Copy.extendStored stored) i.val) = z
  funext j
  rcases lt_trichotomy j 661 with hj | hj | hj
  · exact Copy.decoded_scatter frameOf z ⟨j, hj⟩
  · subst hj
    rw [Copy.temporary_cleared]
    simp only [FramedCircuit.encode]
    rw [moduleRun_high _ sectionScatter_target_lt _ 661 le_rfl]
    simp [Copy.extendStored]
  · rw [copy_run_high frameOf _ j hj]
    simp only [FramedCircuit.encode, scatterFinish]
    rw [moduleRun_high _ sectionScatter_target_lt _ j hj.le]

/-- The complete framed word decodes every register from its initial frame, applies the literal
scalar word, and encodes the result in its final frame. -/
theorem execute_endpoint (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) :
    execute frameOf (FramedCircuit.encode (fun i => frameOf (Frames.snapshot initialRefs i))
        (Copy.extendStored stored)) =
      FramedCircuit.encode (fun i => frameOf (Frames.snapshot finalRefs i))
        (FramedCircuit.moduleRun (program.map RawGate.toCircuit) (Copy.extendStored stored)) := by
  rw [execute, Frames.before_scatter_compiled, copy_phase, Frames.after_scatter_compiled,
    Frames.final_alignment_compiled]
  simp only [program, List.map_append, moduleRun_append]

/-- Every register above the retained ones, including the temporary, ends at zero. -/
theorem execute_high (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) (j : ℕ) (hj : 661 ≤ j) :
    execute frameOf (FramedCircuit.encode (fun i => frameOf (Frames.snapshot initialRefs i))
        (Copy.extendStored stored)) j = 0 := by
  rw [execute_endpoint]
  simp only [FramedCircuit.encode]
  rw [moduleRun_high _ program_target_lt _ j hj]
  simp [Copy.extendStored, show ¬j < 661 by omega]

end Streams

end IntegerMultBounds.Networks.Certificates.PR589.Framed
