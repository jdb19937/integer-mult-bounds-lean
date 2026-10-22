module

public import IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB.HintData
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.RootKernel

/-! Target traces reuse existing signed chains. Zero readouts are handled structurally. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB
noncomputable section
open Local

/-- The concrete readout labels seen by one target, in their actual order. -/
def readoutLabels (t : Nat) : List Signed.Frame := fastLabels hints t

/-- Existing chain edges and a checked root complement bound the whole target trace. -/
@[irreducible] def targetOk (t endpoint : Nat) : Bool :=
  ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt (28866 + t))
    (.zero :: readoutLabels t ++ [.negative endpoint]) &&
      (SignedFull.bankEntry endpoint).basis.contains (GeometryB.rootCode (3 * t))

end
end IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB
