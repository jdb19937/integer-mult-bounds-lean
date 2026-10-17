module

public import IntegerMultBounds.Networks.Certificates.T16.Trace.Certificate

/-! The checked native traces as framed event traces. Scalar rows keep their declared frame,
climbs and centres become frame edges, and adapters, residual wrappers and phase markers carry
no operator. A checked native run is a valid framed trace with the same final labels, so for any
choice of frame operators its physical execution acts on logical values by exactly the erased
rational word. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Trace

open FramedEventTrace

/-- The framed event of a native event, if it has one. -/
def Event.framed : Event → Option (FramedEventTrace.Event ℕ ℕ ℚ)
  | .scalar (.add t r n d f) => some (.gate (Scalar.gate (.add t r n d f)) f)
  | .scalar (.scale t n d f) => some (.gate (Scalar.gate (.scale t n d f)) f)
  | .scalar (.clear t f) => some (.clear t f)
  | .scalar (.copy t r f) => some (.copy r t f)
  | .climb _ r old next _ => some (.edge r old next)
  | .center i old next _ => some (.edge (704 + i) old next)
  | _ => none

def framed (es : List Event) : List (FramedEventTrace.Event ℕ ℕ ℚ) :=
  es.filterMap Event.framed

theorem erase_framed (es : List Event) : FramedEventTrace.erase (framed es) = erase es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | scalar s =>
      cases s <;> simp only [framed, List.filterMap_cons, Event.framed, erase] at ih ⊢ <;>
        rw [FramedEventTrace.erase, ih] <;> rfl
    | climb _ _ _ _ _ => simpa [framed, Event.framed, erase, FramedEventTrace.erase] using ih
    | center _ _ _ _ => simpa [framed, Event.framed, erase, FramedEventTrace.erase] using ih
    | adapter _ _ _ => simpa [framed, List.filterMap_cons, Event.framed, erase] using ih
    | residual _ _ _ _ => simpa [framed, List.filterMap_cons, Event.framed, erase] using ih
    | phase _ => simpa [framed, List.filterMap_cons, Event.framed, erase] using ih

/-- Every native register is present in the label trie. -/
def Contains (s : State) : Prop := ∀ i < 712, s.labels.contains i = true

theorem Contains.put {s : State} (h : Contains s) (r f : ℕ) : Contains (s.put r f) :=
  fun i hi => by rw [State.put, Labels.contains_put]; exact h i hi

theorem label_put {s : State} {r f : ℕ} (hc : Contains s) (hr : r < 712) :
    (s.put r f).label = Function.update s.label r f := by
  funext i
  by_cases h : i = r
  · subst h
    simp [State.label, State.put, Labels.get_put_self _ _ _ (hc i hr)]
  · rw [Function.update_of_ne h]
    exact Labels.get_put_other _ _ _ _ h

/-- One checked native step is one checked framed step with the same label update. -/
theorem step_framed {s t : State} {e : Event} (hc : Contains s) (h : step s e = some t) :
    Contains t ∧ match e.framed with
      | some fe => StepValid s.label fe ∧ t.label = after s.label fe
      | none => t.label = s.label := by
  cases e with
  | scalar g =>
    cases g with
    | add tg r n d f =>
      simp only [step, scalarStep] at h
      split at h
      · rename_i hg
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at hg
        refine ⟨hc, ?_, rfl⟩
        intro i hi
        simp only [FramedCircuit.touched, Scalar.gate, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hi
        rcases hi with h1 | h1 <;> subst h1
        · exact hg.2
        · exact hg.1.2
      · simp at h
    | scale tg n d f =>
      simp only [step, scalarStep] at h
      split at h
      · rename_i hg
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at hg
        refine ⟨hc, ?_, rfl⟩
        intro i hi
        simp only [FramedCircuit.touched, Scalar.gate, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false, or_self] at hi
        rw [hi]
        exact hg.2
      · simp at h
    | clear tg f =>
      simp only [step, scalarStep] at h
      split at h
      · rename_i hg
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        exact ⟨hc.put _ _, trivial, label_put hc (by omega)⟩
      · simp at h
    | copy tg r f =>
      simp only [step, scalarStep] at h
      split at h
      · rename_i hg
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
        exact ⟨hc.put _ _, hg.2, label_put hc (by omega)⟩
      · simp at h
  | climb ph r old next rank =>
    simp only [step] at h
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
      refine ⟨hc.put _ _, hg.2.symm, label_put hc (by omega)⟩
    · simp at h
  | center i old next rank =>
    simp only [step] at h
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
      refine ⟨hc.put _ _, hg.2.symm, label_put hc (by omega)⟩
    · simp at h
  | adapter entry r f =>
    simp only [step, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hc, rfl⟩
  | residual pre r start terminal =>
    simp only [step, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hc, rfl⟩
  | phase i =>
    simp only [step, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hc, rfl⟩

/-- A checked native run is a valid framed trace ending at the native final labels. -/
theorem run_framed {s t : State} {es : List Event} (hc : Contains s) (h : run s es = some t) :
    FramedEventTrace.Valid s.label (framed es) ∧
      finalProfile s.label (framed es) = t.label := by
  induction es generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst h
    exact ⟨trivial, rfl⟩
  | cons e es ih =>
    simp only [run] at h
    cases hs : step s e with
    | none => simp [hs] at h
    | some u =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨hcu, hstep⟩ := step_framed hc hs
      obtain ⟨hv, hf⟩ := ih hcu h
      cases hfe : e.framed with
      | none =>
        rw [hfe] at hstep
        simp only [framed, List.filterMap_cons, hfe]
        rw [← hstep]
        exact ⟨hv, hf⟩
      | some fe =>
        rw [hfe] at hstep
        simp only [framed, List.filterMap_cons, hfe]
        refine ⟨⟨hstep.1, ?_⟩, ?_⟩
        · rw [← hstep.2]; exact hv
        · change finalProfile (after s.label fe) (framed es) = _
          rw [← hstep.2]
          exact hf

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- **Forward local word.** For any frame operators, executing the forward native trace acts
on arbitrary stored values, dirty scratch included, by the erased rational word between the
native initial and final frame profiles. -/
theorem forward_run (frameOf : ℕ → FramedCircuit.Frame ℚ E) (stored : ℕ → E) :
    FramedCircuit.run (lower frameOf (framed forwardEvents)) stored =
      FramedCircuit.encode (fun i => frameOf (forwardFinal.label i))
        (FramedCircuit.moduleRun forwardProgram
          (FramedCircuit.decode (fun i => frameOf (forwardInitial.label i)) stored)) := by
  obtain ⟨hv, hf⟩ := run_framed (fun i hi => initial_contains i hi) forward_checked
  rw [valid_run frameOf _ _ hv stored, hf, erase_framed]
  rfl

/-- **Backward local word**, as `forward_run`. -/
theorem backward_run (frameOf : ℕ → FramedCircuit.Frame ℚ E) (stored : ℕ → E) :
    FramedCircuit.run (lower frameOf (framed backwardEvents)) stored =
      FramedCircuit.encode (fun i => frameOf (backwardFinal.label i))
        (FramedCircuit.moduleRun backwardProgram
          (FramedCircuit.decode (fun i => frameOf (backwardInitial.label i)) stored)) := by
  obtain ⟨hv, hf⟩ := run_framed (fun i hi => by rw [← same_initial_state]; exact initial_contains i hi)
    backward_checked
  rw [valid_run frameOf _ _ hv stored, hf, erase_framed]
  rfl

end IntegerMultBounds.Networks.Certificates.T16.Trace
