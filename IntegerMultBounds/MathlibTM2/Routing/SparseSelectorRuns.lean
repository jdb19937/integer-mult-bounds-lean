module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorSelectorFrames

/-! A compact sparse selector stream records a gap and one live selector per
entry. Expansion includes every absent position. Run order is explicit because
the executing emitter prepends each run to the accumulated output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

structure SparseSelectorRun (W : ℕ) where
  gap : ℕ
  selector : Fin (W + 1)

namespace SparseSelectorRun

variable {W A : ℕ}

def indices (run : SparseSelectorRun W) : List (Fin (W + 1)) :=
  List.replicate run.gap 0 ++ [run.selector]

def expand : List (SparseSelectorRun W) → List (Fin (W + 1))
  | [] => []
  | run :: runs => run.indices ++ expand runs

theorem indices_length (run : SparseSelectorRun W) : run.indices.length = run.gap + 1 := by
  simp [indices]

theorem expand_append (runs rest : List (SparseSelectorRun W)) :
    expand (runs ++ rest) = expand runs ++ expand rest := by
  induction runs with
  | nil => rfl
  | cons run runs ih => simp [expand, ih, List.append_assoc]

theorem expand_length (runs : List (SparseSelectorRun W)) :
    (expand runs).length = (runs.map (fun run => run.gap + 1)).sum := by
  induction runs with
  | nil => rfl
  | cons run runs ih => simp [expand, indices_length, ih]

theorem frames_cons (L : ℕ) (run : SparseSelectorRun W) (runs : List (SparseSelectorRun W)) :
    descriptorSelectorFrames (A := A) L (expand (run :: runs)) =
      descriptorSelectorFrames L run.indices ++ descriptorSelectorFrames L (expand runs) :=
  descriptorSelectorFrames_append L _ _

/-- Consuming reverse run order produces the forward dense stream by prepending.
Selectors within each run retain their original order, including gap zeros. -/
def prepend (runs : List (SparseSelectorRun W)) (out : List (Fin (W + 1))) : List (Fin (W + 1)) :=
  match runs with
  | [] => out
  | run :: rest => prepend rest (run.indices ++ out)

theorem prepend_eq (runs : List (SparseSelectorRun W)) (out : List (Fin (W + 1))) :
    prepend runs out = expand runs.reverse ++ out := by
  induction runs generalizing out with
  | nil => rfl
  | cons run runs ih =>
    simp [prepend, ih, List.reverse_cons, expand_append, expand, List.append_assoc]

theorem prepend_reverse (runs : List (SparseSelectorRun W)) (out : List (Fin (W + 1))) :
    prepend runs.reverse out = expand runs ++ out := by
  rw [prepend_eq, List.reverse_reverse]

theorem frames_length (L : ℕ) (runs : List (SparseSelectorRun W)) :
    (descriptorSelectorFrames (A := A) L (expand runs)).length =
      (runs.map (fun run => run.gap + 1)).sum * (L + 1) := by
  rw [descriptorSelectorFrames_length, expand_length]

end SparseSelectorRun
end IntegerMultBounds.MathlibTM2.Routing
