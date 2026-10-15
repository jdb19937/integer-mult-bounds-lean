module

public import IntegerMultBounds.Networks.Certificates.PR589.Frames.Boundary
public import IntegerMultBounds.Networks.Certificates.PR589.EndpointSemantics

/-! Nine source-ordered COPY/ADD/ERASE lifecycles use a fresh register 661.
These definitions preserve the source and clear the temporary after each fanout.
No geometric rank or tape cost is assigned to a COPY. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Copy

structure Lifecycle where
  source : ℕ
  sourceFrame : ℕ
  targets : List ℕ
  deriving DecidableEq, Repr

variable {E : Type*} [AddCommGroup E]

def addTargets : List ℕ → (ℕ → E) → (ℕ → E)
  | [], stored => stored
  | i :: rest, stored => addTargets rest (Function.update stored i (stored i + stored 661))

theorem addTargets_eq (targets : List ℕ) (hn : targets.Nodup) (ht : 661 ∉ targets)
    (stored : ℕ → E) (i : ℕ) :
    addTargets targets stored i = if i ∈ targets then stored i + stored 661 else stored i := by
  induction targets generalizing stored with
  | nil => simp [addTargets]
  | cons t ts ih =>
    have hne : 661 ≠ t := by intro h; exact ht (by simp [h])
    rw [addTargets, ih hn.tail (fun h => ht (List.mem_cons_of_mem _ h))]
    by_cases hi : i = t
    · subst i
      simp [(List.nodup_cons.mp hn).1]
    · simp [hi, Function.update_of_ne hne]

def logicalStep (life : Lifecycle) (stored : ℕ → E) : ℕ → E :=
  fun i => if i ∈ life.targets then stored i + stored life.source else stored i

def logicalRun : List Lifecycle → (ℕ → E) → (ℕ → E)
  | [], stored => stored
  | life :: rest, stored => logicalRun rest (logicalStep life stored)

/-- COPY converts the retained source frame to frame zero in the temporary;
ADDs then operate at their actual common zero frame, and ERASE clears it. -/
def execute [Module (ZMod 2) E] (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E)
    (life : Lifecycle) (stored : ℕ → E) : ℕ → E :=
  Function.update
    (addTargets life.targets
      (Function.update stored 661 (frameOf 0 ((frameOf life.sourceFrame).symm (stored life.source)))))
    661 0

def run [Module (ZMod 2) E] (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E) :
    List Lifecycle → (ℕ → E) → (ℕ → E)
  | [], stored => stored
  | life :: rest, stored => run frameOf rest (execute frameOf life stored)

/-- The temporary has zero logical content before and after the complete fanout. -/
theorem execute_invariant [Module (ZMod 2) E]
    (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E) (profile : ℕ → ℕ)
    (life : Lifecycle) (hn : life.targets.Nodup) (ht : 661 ∉ life.targets)
    (hs : profile life.source = life.sourceFrame)
    (hz : ∀ i ∈ life.targets, profile i = 0)
    (stored : ℕ → E) (hzero : stored 661 = 0) :
    execute frameOf life (FramedCircuit.encode (fun i => frameOf (profile i)) stored) =
    FramedCircuit.encode (fun i => frameOf (profile i)) (logicalStep life stored) := by
  funext i
  by_cases hi : i = 661
  · subst i
    simp [execute, FramedCircuit.encode, logicalStep, ht, hzero]
  · rw [execute, Function.update_of_ne hi, addTargets_eq _ hn ht]
    by_cases hm : i ∈ life.targets
    · simp [hm, Function.update_of_ne hi, FramedCircuit.encode, hs, hz i hm,
        logicalStep, map_add]
    · simp [hm, Function.update_of_ne hi, FramedCircuit.encode, logicalStep]

theorem logicalStep_temp (life : Lifecycle) (ht : 661 ∉ life.targets) (stored : ℕ → E) :
    logicalStep life stored 661 = stored 661 := by simp [logicalStep, ht]

theorem run_invariant [Module (ZMod 2) E]
    (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E) (profile : ℕ → ℕ)
    (lives : List Lifecycle)
    (h : ∀ life ∈ lives, life.targets.Nodup ∧ 661 ∉ life.targets ∧
      profile life.source = life.sourceFrame ∧ ∀ i ∈ life.targets, profile i = 0)
    (stored : ℕ → E) (hzero : stored 661 = 0) :
    run frameOf lives (FramedCircuit.encode (fun i => frameOf (profile i)) stored) =
    FramedCircuit.encode (fun i => frameOf (profile i)) (logicalRun lives stored) := by
  induction lives generalizing stored with
  | nil => rfl
  | cons life rest ih =>
    obtain ⟨hn, ht, hs, hz⟩ := h life (List.mem_cons_self)
    rw [run, execute_invariant frameOf profile life hn ht hs hz stored hzero]
    exact ih (fun l hl => h l (List.mem_cons_of_mem _ hl)) _
      ((logicalStep_temp life ht stored).trans hzero)

end IntegerMultBounds.Networks.Certificates.PR589.Copy
