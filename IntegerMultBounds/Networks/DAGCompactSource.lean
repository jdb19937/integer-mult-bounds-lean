module

public import IntegerMultBounds.Networks.DAGCompact

/-! Every node of a compacted DAG copies an active source node: it carries
the same support, and it is an addition only if the source node is. -/

@[expose] public section

namespace IntegerMultBounds.Networks.DAGCompact

open DisjointCircuit DisjointBuilder DisjointPruning DAGReplay

variable {ι : Type*} [DecidableEq ι]

theorem intern_mem (target : List (Node ι)) (node : Node ι) (n : Node ι)
    (hn : n ∈ (intern target node).1) : n ∈ target ∨ n = node := by
  unfold intern at hn
  split at hn
  · exact Or.inl hn
  · rcases List.mem_append.mp hn with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)

theorem compactFrom_source (active : Finset ℕ) (target : List (Node ι)) (refs : List ℕ)
    (source : List (Node ι)) :
    ∀ n ∈ (compactFrom active target refs source).1, n ∈ target ∨
      ∃ j, ∃ hj : j < source.length, refs.length + j ∈ active ∧ source[j].support = n.support ∧
        ((∃ l r, n.kind = .add l r) → ∃ l r, source[j].kind = .add l r) := by
  induction source generalizing target refs with
  | nil => intro n hn; exact Or.inl hn
  | cons node source ih =>
    intro n hn
    have shift : ∀ j, (hj : j < source.length) → (refs ++ [0]).length + j ∈ active ∨
        (refs ++ [(intern target (translated (Function.Embedding.refl ι) refs node)).2]).length + j ∈ active →
        refs.length + (j + 1) ∈ active := by
      intro j _ h
      simp only [List.length_append, List.length_singleton] at h
      rw [show refs.length + (j + 1) = refs.length + 1 + j by omega]
      rcases h with h | h <;> exact h
    by_cases hm : refs.length ∈ active
    · simp only [compactFrom, hm, ↓reduceIte] at hn
      rcases ih _ _ n hn with h | ⟨j, hj, ha, hs, hk⟩
      · rcases intern_mem _ _ n h with h | rfl
        · exact Or.inl h
        · right
          refine ⟨0, by simp, by simpa using hm, by simp, ?_⟩
          rintro ⟨l, r, hk⟩
          cases hnk : node.kind with
          | input p => simp [translated, hnk] at hk
          | add l' r' => exact ⟨l', r', by simp [hnk]⟩
      · exact Or.inr ⟨j + 1, by simp; omega, shift j hj (Or.inr ha), by simpa using hs, by simpa using hk⟩
    · simp only [compactFrom, hm, ↓reduceIte] at hn
      rcases ih _ _ n hn with h | ⟨j, hj, ha, hs, hk⟩
      · exact Or.inl h
      · exact Or.inr ⟨j + 1, by simp; omega, shift j hj (Or.inl ha), by simpa using hs, by simpa using hk⟩

/-- Each compacted node copies an active source node of the same kind and support. -/
theorem compact_source (active : Finset ℕ) (nodes : List (Node ι)) (k : ℕ)
    (hk : k < (compact active nodes).1.length) :
    ∃ j, ∃ hj : j < nodes.length, j ∈ active ∧ nodes[j].support = (compact active nodes).1[k].support ∧
      ((∃ l r, (compact active nodes).1[k].kind = .add l r) → ∃ l r, nodes[j].kind = .add l r) := by
  rcases compactFrom_source active [] [] nodes _ (List.getElem_mem hk) with h | ⟨j, hj, ha, hs, hkd⟩
  · simp at h
  · exact ⟨j, hj, by simpa using ha, hs, hkd⟩

end IntegerMultBounds.Networks.DAGCompact
