module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateGenerate
public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoopData

/-! The stream computed from absolute coordinates is exactly the compact-run
compiler input in reverse run order. Bounds follow from coordinate readiness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {A W : ℕ}

def sparseCoordinateValues (entries : List (ℕ × Fin (W + 1))) : List (ℕ × ℕ) :=
  entries.map (fun e => (e.1, e.2.val))

def sparseCoordinateRuns (cursor : ℕ) : List (ℕ × Fin (W + 1)) → List (SparseSelectorRun W)
  | [] => []
  | (x, q) :: rest => ⟨x - cursor, q⟩ :: sparseCoordinateRuns (x + 1) rest

theorem selectorRunFrames_append (L Ls : ℕ) (runs rest : List (SparseSelectorRun W)) :
    selectorRunFrames (A := A) L Ls (runs ++ rest) =
      selectorRunFrames L Ls runs ++ selectorRunFrames L Ls rest := by
  induction runs with
  | nil => rfl
  | cons run runs ih => simp [selectorRunFrames, ih, List.append_assoc]

theorem sparseCoordinateOutput_runs (L Ls cursor : ℕ) (entries : List (ℕ × Fin (W + 1))) :
    sparseCoordinateOutput (A := A) L Ls cursor (sparseCoordinateValues entries) =
      selectorRunFrames L Ls (sparseCoordinateRuns cursor entries).reverse := by
  induction entries generalizing cursor with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    simp [sparseCoordinateValues, sparseCoordinateOutput, sparseCoordinateRuns,
      List.reverse_cons, selectorRunFrames_append, selectorRunFrames]
    simpa only [sparseCoordinateValues] using ih (x + 1)

theorem sparseCoordinateRuns_length (cursor : ℕ) (entries : List (ℕ × Fin (W + 1))) :
    (sparseCoordinateRuns cursor entries).length = entries.length := by
  induction entries generalizing cursor with
  | nil => rfl
  | cons pair rest ih => cases pair; simp [sparseCoordinateRuns, ih]

theorem sparseCoordinateRuns_fit (L cursor : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (hready : SparseCoordinatesReady L cursor (sparseCoordinateValues entries)) :
    ∀ run ∈ sparseCoordinateRuns cursor entries, run.gap < 2 ^ L := by
  induction entries generalizing cursor with
  | nil => simp [sparseCoordinateRuns]
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    obtain ⟨hx, hyx, hr⟩ := hready
    intro run hm
    simp only [sparseCoordinateRuns, List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp only; omega
    · exact ih (x + 1) hr run hm

end IntegerMultBounds.MathlibTM2.Routing
