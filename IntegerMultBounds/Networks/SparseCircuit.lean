module

public import IntegerMultBounds.Networks.ReversibleFanout

/-! Literal one-source XOR lists between disjoint register banks. Sources are
stable, so repeated targets accumulate and repeated source labels are allowed. -/

@[expose] public section

namespace IntegerMultBounds.Networks.SparseCircuit

open Circuit
variable {α β ι : Type*} [DecidableEq ι]

/-- Each pair records one destination and one source, with coefficient one. -/
def copies (dst : α → ι) (src : β → ι) (entries : List (α × β)) : Program ι (ZMod 2) :=
  entries.map (fun entry => ReversibleFanout.add (dst entry.1) (src entry.2))

omit [DecidableEq ι] in
@[simp] theorem copies_length (dst : α → ι) (src : β → ι) (entries : List (α × β)) :
    (copies dst src entries).length = entries.length := List.length_map _

/-- Exact effect of the actual copy list, including repeated targets. -/
theorem copies_run (dst : α → ι) (src : β → ι) (entries : List (α × β))
    (separate : ∀ a b, dst a ≠ src b) (state : ι → ZMod 2) (k : ι) :
    run (copies dst src entries) state k = state k +
      (entries.map (fun entry => if dst entry.1 = k then state (src entry.2) else 0)).sum := by
  induction entries generalizing state with
  | nil => simp [copies]
  | cons entry entries ih =>
    simp only [copies, List.map_cons, run_cons] at *
    rw [ih]
    have hs (b : β) : (ReversibleFanout.add (dst entry.1) (src entry.2)).run state (src b) = state (src b) := by
      rw [ReversibleFanout.add_run, Function.update_of_ne (separate entry.1 b).symm]
    simp only [hs, List.sum_cons]
    by_cases hk : dst entry.1 = k
    · subst k
      simp only [ReversibleFanout.add_run, Function.update_self, ↓reduceIte]
      abel
    · simp [ReversibleFanout.add_run, Function.update_of_ne (Ne.symm hk), hk]

end IntegerMultBounds.Networks.SparseCircuit
