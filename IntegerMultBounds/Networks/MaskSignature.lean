module

public import IntegerMultBounds.Networks.MaskDAG

/-! Vertex summaries of a source support: the vertices common to every source
payload and the vertices covered by some payload. An addition intersects
common vertices and unions covered vertices. -/

@[expose] public section

namespace IntegerMultBounds.Networks.MaskSignature

open DisjointCircuit MaskDAG

variable {width vertices : ℕ}

/-- Vertices shared by every source payload; the empty intersection is full. -/
def core (payload : Fin width → Finset (Fin vertices)) (support : Finset (Fin width)) :
    Finset (Fin vertices) := Finset.univ.filter (fun v => ∀ i ∈ support, v ∈ payload i)

/-- Vertices appearing in at least one source payload. -/
def union (payload : Fin width → Finset (Fin vertices)) (support : Finset (Fin width)) :
    Finset (Fin vertices) := support.biUnion payload

@[simp] theorem core_singleton (payload : Fin width → Finset (Fin vertices)) (i : Fin width) :
    core payload {i} = payload i := by ext v; simp [core]

@[simp] theorem union_singleton (payload : Fin width → Finset (Fin vertices)) (i : Fin width) :
    union payload {i} = payload i := by simp [union]

@[simp] theorem core_union (payload : Fin width → Finset (Fin vertices))
    (left right : Finset (Fin width)) :
    core payload (left ∪ right) = core payload left ∩ core payload right := by
  ext v
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_inter]
  aesop

@[simp] theorem union_union (payload : Fin width → Finset (Fin vertices))
    (left right : Finset (Fin width)) :
    union payload (left ∪ right) = union payload left ∪ union payload right := by
  ext v
  simp [union]
  aesop

end IntegerMultBounds.Networks.MaskSignature
