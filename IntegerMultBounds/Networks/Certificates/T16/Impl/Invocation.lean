module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Call
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Action

/-! One local invocation: wrap every register, run a local word on the registers' arrays, and
unwrap every register. Both words touch only the 712 native registers, so on the wrapped
registers the invocation is the framed run of the word, and every other array is unchanged. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh FramedCircuit

/-! ### The words stay among the native registers -/

/-- Every register an event names is a native register. -/
def eventInRange : Trace.Event → Bool
  | .scalar (.add t s _ _ _) => t < 712 && s < 712
  | .scalar (.scale t _ _ _) => t < 712
  | .scalar (.clear t _) => t < 712
  | .scalar (.copy t s _) => t < 712 && s < 712
  | .climb _ r _ _ _ => r < 712
  | .center i _ _ _ => i < 8
  | _ => true

theorem forward_inRange : Trace.forwardEvents.all eventInRange = true := by decide +kernel

theorem backward_inRange : Trace.backwardEvents.all eventInRange = true := by decide +kernel

theorem implEvent_wires (e : Trace.Event) (he : eventInRange e = true) :
    ∀ fe, e.framed = some fe → ∀ i ∈ implEvent fe, ∀ w ∈ i.wires, w < 712 := by
  intro fe hfe i hi w hw
  cases e with
  | scalar g =>
    cases g with
    | add t s n d f =>
      simp only [Trace.Event.framed, Option.some.injEq] at hfe
      subst hfe
      simp only [eventInRange, Bool.and_eq_true, decide_eq_true_eq] at he
      simp only [implEvent, List.mem_singleton] at hi
      subst hi
      simp only [TInstr.wires, Trace.Scalar.gate, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    | scale t n d f =>
      simp only [Trace.Event.framed, Option.some.injEq] at hfe
      subst hfe
      simp only [eventInRange, decide_eq_true_eq] at he
      simp only [implEvent, List.mem_singleton] at hi
      subst hi
      simp only [TInstr.wires, Trace.Scalar.gate, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    | clear t f =>
      simp only [Trace.Event.framed, Option.some.injEq] at hfe
      subst hfe
      simp only [eventInRange, decide_eq_true_eq] at he
      simp only [implEvent, List.mem_singleton] at hi
      subst hi
      simp only [TInstr.wires, FramedEventTrace.clearGate, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    | copy t s f =>
      simp only [Trace.Event.framed, Option.some.injEq] at hfe
      subst hfe
      simp only [eventInRange, Bool.and_eq_true, decide_eq_true_eq] at he
      simp only [implEvent, List.mem_singleton] at hi
      subst hi
      simp only [TInstr.wires, FramedEventTrace.copyGate, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> omega
  | climb ph r old next rank =>
    simp only [Trace.Event.framed, Option.some.injEq] at hfe
    subst hfe
    simp only [eventInRange, decide_eq_true_eq] at he
    simp only [implEvent, List.mem_map] at hi
    obtain ⟨p, _, rfl⟩ := hi
    simp only [TInstr.wires, List.mem_singleton] at hw
    omega
  | center c old next rank =>
    simp only [Trace.Event.framed, Option.some.injEq] at hfe
    subst hfe
    simp only [eventInRange, decide_eq_true_eq] at he
    simp only [implEvent, List.mem_map] at hi
    obtain ⟨p, _, rfl⟩ := hi
    simp only [TInstr.wires, List.mem_singleton] at hw
    omega
  | adapter _ _ _ => simp [Trace.Event.framed] at hfe
  | residual _ _ _ _ => simp [Trace.Event.framed] at hfe
  | phase _ => simp [Trace.Event.framed] at hfe

theorem framed_wires (es : List Trace.Event) (h : es.all eventInRange = true) :
    ∀ i ∈ (Trace.framed es).flatMap implEvent, ∀ w ∈ i.wires, w < 712 := by
  intro i hi
  simp only [List.mem_flatMap, Trace.framed, List.mem_filterMap] at hi
  obtain ⟨fe, ⟨e, he, hfe⟩, hi⟩ := hi
  exact implEvent_wires e (List.all_eq_true.mp h e he) fe hfe i hi

theorem forwardWord_wires : ∀ i ∈ forwardWord, ∀ w ∈ i.wires, w < 712 :=
  framed_wires _ forward_inRange

theorem backwardWord_wires : ∀ i ∈ backwardWord, ∀ w ∈ i.wires, w < 712 :=
  framed_wires _ backward_inRange

/-! ### Invocations -/

variable {κ : Type} [DecidableEq κ]
variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

/-- Apply a word to the wire of each listed register. -/
def regBlocks (reg : ℕ → κ) (rs : List ℕ) (word : ℕ → List Prim) : List (TInstr κ) :=
  rs.flatMap fun w => (word w).map (TInstr.prim (reg w))

theorem runT_regBlocks (reg : ℕ → κ) (rs : List ℕ) (hnd : rs.Nodup)
    (hinj : ∀ w ∈ rs, ∀ w' ∈ rs, reg w = reg w' → w = w') (word : ℕ → List Prim) (y : κ → S) :
    (∀ w ∈ rs, runT ρ (regBlocks reg rs word) y (reg w) = ρ (wordLin (word w)) (y (reg w))) ∧
      ∀ v, (∀ w ∈ rs, reg w ≠ v) → runT ρ (regBlocks reg rs word) y v = y v := by
  induction rs generalizing y with
  | nil => exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | cons w0 rs ih =>
    have hnd' := List.nodup_cons.mp hnd
    have hinj' : ∀ w ∈ rs, ∀ w' ∈ rs, reg w = reg w' → w = w' := fun w hw w' hw' =>
      hinj w (List.mem_cons_of_mem _ hw) w' (List.mem_cons_of_mem _ hw')
    have hne : ∀ w ∈ rs, reg w ≠ reg w0 := fun w hw e =>
      hnd'.1 ((hinj w (List.mem_cons_of_mem _ hw) w0 List.mem_cons_self e) ▸ hw)
    have hstep : runT ρ (regBlocks reg (w0 :: rs) word) y = runT ρ (regBlocks reg rs word)
        (Function.update y (reg w0) (ρ (wordLin (word w0)) (y (reg w0)))) := by
      rw [regBlocks, List.flatMap_cons, runT_append, runT_prims]
      rfl
    obtain ⟨h1, h2⟩ := ih hnd'.2 hinj'
      (Function.update y (reg w0) (ρ (wordLin (word w0)) (y (reg w0))))
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · rw [hstep]
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [h2 _ hne, Function.update_self]
      · rw [h1 w hw, Function.update_of_ne (hne w hw)]
    · rw [hstep, h2 v (fun w hw => hv w (List.mem_cons_of_mem _ hw)),
        Function.update_of_ne (fun e => hv w0 List.mem_cons_self e.symm)]

/-- An invocation: wrap every native register, run the word, unwrap every native register. -/
noncomputable def invocation (reg : ℕ → κ) (pre post : ℕ → List Prim) (word : List (TInstr ℕ)) :
    List (TInstr κ) :=
  regBlocks reg (List.range 712) pre ++ word.map (TInstr.rename reg) ++
    regBlocks reg (List.range 712) post

/-- **Invocation.** On the native registers an invocation is the word run on the wrapped
arrays, then unwrapped; every other wire is unchanged. -/
theorem invocation_run (reg : ℕ → κ) (hinj : ∀ w < 712, ∀ w' < 712, reg w = reg w' → w = w')
    (pre post : ℕ → List Prim) (word : List (TInstr ℕ))
    (hword : ∀ i ∈ word, ∀ w ∈ i.wires, w < 712) (y : κ → S) :
    (∀ w < 712, runT ρ (invocation reg pre post word) y (reg w) =
        ρ (wordLin (post w)) (runT ρ word (fun w => ρ (wordLin (pre w)) (y (reg w))) w)) ∧
      ∀ v, (∀ w < 712, reg w ≠ v) → runT ρ (invocation reg pre post word) y v = y v := by
  have hnd := List.nodup_range (n := 712)
  have hinj' : ∀ w ∈ List.range 712, ∀ w' ∈ List.range 712, reg w = reg w' → w = w' :=
    fun w hw w' hw' => hinj w (List.mem_range.mp hw) w' (List.mem_range.mp hw')
  obtain ⟨p1, p2⟩ := runT_regBlocks ρ reg _ hnd hinj' pre y
  set y1 := runT ρ (regBlocks reg (List.range 712) pre) y
  set x : ℕ → S := fun w => ρ (wordLin (pre w)) (y (reg w))
  have hag : Agrees reg {w | w < 712} y1 x := fun w hw => p1 w (List.mem_range.mpr hw)
  obtain ⟨q1, q2⟩ := runT_rename ρ reg {w | w < 712}
    (fun w hw w' hw' e => hinj w hw w' hw' e) word (fun i hi w hw => hword i hi w hw) hag
  set y2 := runT ρ (word.map (TInstr.rename reg)) y1
  obtain ⟨r1, r2⟩ := runT_regBlocks ρ reg _ hnd hinj' post y2
  have hrun : runT ρ (invocation reg pre post word) y =
      runT ρ (regBlocks reg (List.range 712) post) y2 := by
    rw [invocation, runT_append, runT_append]
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · rw [hrun, r1 w (List.mem_range.mpr hw), q1 w hw]
  · have hv' : ∀ w ∈ List.range 712, reg w ≠ v := fun w hw => hv w (List.mem_range.mp hw)
    rw [hrun, r2 v hv', q2 v (fun w hw => hv w hw), p2 v hv']

end IntegerMultBounds.Networks.Certificates.T16.Impl
