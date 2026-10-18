module

public import IntegerMultBounds.Networks.GlobalLabels
public import IntegerMultBounds.Networks.Mixer.Motif
public import IntegerMultBounds.Networks.Mixer.Global

/-! Tensor labels on the physical three-stage mixer network. Each invocation
carries the labels of its stage geometry, lifted by its future line and
transported to the common cube; the rectangle enclosures `U` (forward) and `U'`
(inverse) are subspaces of the current factor and are shared by all stages. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Labels

open scoped TensorProduct
open GroupedCircuit GroupedFrames MotifLabels StageLabels GlobalLabels Scalar

variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R]
  {n a c M : ℕ}

variable (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (kind : Fin a → Kind n M) (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- Each invocation with the labels of its stage geometry. -/
def invocation (j : Fin 3) (q : B × B) :
    List (Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R) :=
  if j = 0 then
    placeList (GlobalCircuit.localEmbedding eB eA eC j q) (firstLabel t q)
      (Motif.forward (firstGeometry D hs hn) (t ∘ eB) kind U G J H)
  else if j = 1 then
    placeList (GlobalCircuit.localEmbedding eB eA eC j q) (secondLabel t q)
      (Motif.opposite (secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) kind U' G J H)
  else
    placeList (GlobalCircuit.localEmbedding eB eA eC j q) (thirdLabel (K := K) (F := F) q)
      (Motif.forward (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2))
        (t ∘ eB) kind U G J H)

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
/-- Forgetting labels returns the scalar invocation. -/
theorem invocation_groups (j : Fin 3) (q : B × B) :
    (invocation D hs hn t ht eB eA eC kind U U' G J H j q).map Vertex.group =
      Global.invocationGroups eB eA eC kind G J H j q := by
  fin_cases j <;>
    simp [invocation, Global.invocationGroups, Global.localGroups, placeList_groups,
      Motif.forward_groups, Motif.opposite_groups]

def stage (j : Fin 3) :
    List (Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R) :=
  (GlobalCircuit.keys eB).flatMap (invocation D hs hn t ht eB eA eC kind U U' G J H j)

def program : List (Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R) :=
  stage D hs hn t ht eB eA eC kind U U' G J H 0 ++
    stage D hs hn t ht eB eA eC kind U U' G J H 1 ++
    stage D hs hn t ht eB eA eC kind U U' G J H 2

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem stage_groups (j : Fin 3) :
    (stage D hs hn t ht eB eA eC kind U U' G J H j).map Vertex.group =
      Global.stage eB eA eC kind G J H j := by
  simp only [stage, List.map_flatMap, invocation_groups, Global.stage, Global.partialStage]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
/-- The labeled vertex list erases to the scalar mixer network. -/
theorem program_groups :
    (program D hs hn t ht eB eA eC kind U U' G J H).map Vertex.group =
      Global.program eB eA eC kind G J H := by
  simp only [program, List.map_append, stage_groups, Global.program]

end IntegerMultBounds.Networks.Mixer.Labels
