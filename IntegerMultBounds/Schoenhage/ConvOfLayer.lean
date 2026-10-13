module

public import IntegerMultBounds.Schoenhage.ConvCost
public import IntegerMultBounds.Schoenhage.TransformTarget

/-! The synthetic convolution from the simultaneous layer (§A): with compatible layer parameters,
`layerTarget` and the §6 script writers give `convolutionTarget` (`convolution_of_layer`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct

/-- `convolution_of_layer`: the convolution target from the layer target and the script writers. -/
theorem convolution_of_layer {LP : LayerParams} {P : TransformParams} (hc : Compatible LP P)
    (hε0 : 0 < P.ε) (hε1 : P.ε < 1) (hlam : 0 < P.lam') (had : 0 < P.ad) (har : 0 < P.ar) (hbd : 0 < P.bd)
    (hlayer : layerTarget LP) (hwriters : ScriptWriters P) : convolutionTarget P :=
  convolution_of_transform P hε0 hε1 hlam had har hbd (transformTarget_of_layer hc hlayer hwriters)

end IntegerMultBounds.Schoenhage
