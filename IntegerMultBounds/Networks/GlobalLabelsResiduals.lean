module

public import IntegerMultBounds.Networks.BinaryMotifResiduals

/-! Extra residual witnesses for sparse physical histories that skip intermediate
motif labels. These are actual tensor vectors, not inferred dimension claims. -/

@[expose] public section

namespace IntegerMultBounds.Networks.GlobalLabelsResiduals

open scoped TensorProduct
open TensorSubspace MotifLabels BinaryMotifResiduals

variable {h : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  (g : Geometry (ZMod 2) E (Fin h → ZMod 2))

section Future
variable [FiniteDimensional (ZMod 2) E]
variable {H : Type*} [AddCommGroup H] [Module (ZMod 2) H] [FiniteDimensional (ZMod 2) H]

end Future
end IntegerMultBounds.Networks.GlobalLabelsResiduals
