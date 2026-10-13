module

public import IntegerMultBounds.Schoenhage.ScriptGenCost

/-! §6, `lem:synthetic-transform-cost` from `prop:simultaneous-layer`: with the script writers
discharged (`ScriptGenCost.scriptWriters_of_compatible`), the transform target follows from the
layer target for compatible fixed constants. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct

/-- `transformTarget_of_compatible`: `prop:simultaneous-layer` gives `lem:synthetic-transform-cost`
for compatible fixed constants. -/
theorem transformTarget_of_compatible {LP : LayerParams} {P : TransformParams} (hc : Compatible LP P)
    (hlayer : layerTarget LP) : transformTarget P :=
  transformTarget_of_layer hc hlayer (ScriptGenCost.scriptWriters_of_compatible hc)

end IntegerMultBounds.Schoenhage
