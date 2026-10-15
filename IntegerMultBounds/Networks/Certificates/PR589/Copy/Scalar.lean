module

public import IntegerMultBounds.Networks.Certificates.PR589.Copy.Data

/-! Kernel-checked equivalence of source-major fanout and the literal target-major
scatter, for every dirty input on the661 retained physical registers. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Copy
open BinaryScalarReplay

def inputMasks (i : ℕ) : BitVec 661 := if i < 661 then initial i else 0

def symbolicStep (life : Lifecycle) (stored : ℕ → BitVec 661) : ℕ → BitVec 661 :=
  fun i => if i ∈ life.targets then stored i ^^^ stored life.source else stored i

def symbolicRun : List Lifecycle → (ℕ → BitVec 661) → (ℕ → BitVec 661)
  | [], stored => stored
  | life :: rest, stored => symbolicRun rest (symbolicStep life stored)

theorem eval_inputMasks (stored : Fin 661 → ZMod 2) :
    (fun i => eval (inputMasks i) stored) = extendInput stored := by
  funext i
  by_cases hi : i < 661
  · simpa [inputMasks, extendInput, hi] using eval_initial stored ⟨i, hi⟩
  · simp only [inputMasks, ite_eq_right hi, extendInput, dite_eq_right hi]
    exact BinaryScalarReplay.eval_zero stored

theorem eval_symbolicStep (life : Lifecycle) (state : ℕ → BitVec 661)
    (stored : Fin 661 → ZMod 2) :
    (fun i => eval (symbolicStep life state i) stored) =
    logicalStep life (fun i => eval (state i) stored) := by
  funext i
  by_cases hi : i ∈ life.targets <;> simp [symbolicStep, logicalStep, hi, eval_xor]

theorem eval_symbolicRun (lives : List Lifecycle) (state : ℕ → BitVec 661)
    (stored : Fin 661 → ZMod 2) :
    (fun i => eval (symbolicRun lives state i) stored) =
    logicalRun lives (fun i => eval (state i) stored) := by
  induction lives generalizing state with
  | nil => rfl
  | cons life rest ih =>
    rw [symbolicRun, ih, eval_symbolicStep]
    rfl

theorem symbolic_scatter : ∀ i : Fin 661,
    symbolicRun lifecycles inputMasks i.val = replay sectionscatter inputMasks i.val := by
  decide +kernel

/-- No zero-input assumption on any of the661 retained registers. -/
theorem logical_scatter (stored : Fin 661 → ZMod 2) (i : Fin 661) :
    logicalRun lifecycles (extendInput stored) i.val =
    Circuit.run (sectionscatter.map RawGate.toCircuit) (extendInput stored) i.val := by
  have h := congrArg (fun row => eval row stored) (symbolic_scatter i)
  have hl := congrFun (eval_symbolicRun lifecycles inputMasks stored) i.val
  have hr := congrFun (PR589.eval_replay sectionscatter inputMasks stored) i.val
  rw [eval_inputMasks] at hl hr
  exact hl.symm.trans (h.trans hr)

end IntegerMultBounds.Networks.Certificates.PR589.Copy
