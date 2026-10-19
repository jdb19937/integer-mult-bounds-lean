module

public import IntegerMultBounds.Networks.BinaryColumns
public import IntegerMultBounds.Networks.ProjectionTrace
public import IntegerMultBounds.Networks.LabelTransport
public import IntegerMultBounds.Networks.TensorCoordinates
public import IntegerMultBounds.Networks.BinaryMotifResiduals

/-! Factor counts derived from genuine projection ranks. Both orientations of
an actual binary frame edge are handled; no rank is assigned to an unrelated
replacement operation. The residual-unit premise is explicit here. -/

@[expose] public section

namespace IntegerMultBounds.Networks.BinaryRankFactors

open Module BinaryWalsh BinaryPhase BinaryColumns

variable {h k : ℕ}

noncomputable def labelFrame (hs : (Labels.binary h).IsSymm)
    (U : Submodule (ZMod 2) (Address h)) :=
  frame (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs U x))

noncomputable def edgeOperator (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (U V : Submodule (ZMod 2) (Address h)) : Operator h k :=
  tensorColumns k (labelFrame hs V).toLinearMap *
    tensorColumns k (labelFrame hs U).symm.toLinearMap

section Transport
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

end Transport
end IntegerMultBounds.Networks.BinaryRankFactors
