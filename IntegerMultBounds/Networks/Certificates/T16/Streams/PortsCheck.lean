module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Frames
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Ports

/-! Every selected port basis is orthonormal and its packed full frame is the basis weight
vector, so every port's full frame is `C_all`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

open Multiplicative

theorem ports_check : ports.all portCheck = true := by
  decide +kernel

theorem port_fullFrame (P : PortData) (hP : P ∈ ports) :
    basisOp (portBasis P) (ofAdd (fullFrame P).toFun) = cAll :=
  fullFrame_cAll (List.all_eq_true.mp ports_check P hP)

end IntegerMultBounds.Networks.Certificates.T16.Streams
