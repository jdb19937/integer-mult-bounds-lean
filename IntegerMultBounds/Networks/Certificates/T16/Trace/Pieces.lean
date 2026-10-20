module

public import IntegerMultBounds.Networks.Certificates.T16.Trace.Model

/-! Event chunks regrouped into pieces. The symbolic checks run one piece at a time: light
chunks are joined and heavy chunks are cut, so that no check needs much kernel memory, and a
piece only ever reads its own chunks. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Trace

/-- Cut `c` into pieces of the listed lengths, the rest as the last piece. -/
def parts {α : Type} : List ℕ → List α → List (List α)
  | [], c => [c]
  | n :: ns, c => c.take n :: parts ns (c.drop n)

theorem parts_flatten {α : Type} : ∀ (ns : List ℕ) (c : List α), (parts ns c).flatten = c
  | [], c => by simp [parts]
  | n :: ns, c => by rw [parts, List.flatten_cons, parts_flatten ns, List.take_append_drop]

/-- Cut each chunk by its own lengths, then join consecutive cuts in groups of the listed sizes. -/
def pieces (cuts : List (List ℕ)) (sizes : List ℕ) (cs : List (List Event)) : List (List Event) :=
  (parts sizes (List.zipWith parts cuts cs).flatten).map List.flatten

theorem zipWith_parts_flatten : ∀ {cuts : List (List ℕ)} {cs : List (List Event)},
    cuts.length = cs.length → (List.zipWith parts cuts cs).flatten.flatten = cs.flatten
  | [], [], _ => rfl
  | ns :: cuts, c :: cs, h => by
    rw [List.zipWith_cons_cons, List.flatten_cons, List.flatten_append, parts_flatten,
      zipWith_parts_flatten (by simpa using h), List.flatten_cons]

theorem pieces_flatten {cuts : List (List ℕ)} {sizes : List ℕ} {cs : List (List Event)}
    (h : cuts.length = cs.length) : (pieces cuts sizes cs).flatten = cs.flatten := by
  rw [pieces, ← List.flatten_flatten, parts_flatten, zipWith_parts_flatten h]

end IntegerMultBounds.Networks.Certificates.T16.Trace
