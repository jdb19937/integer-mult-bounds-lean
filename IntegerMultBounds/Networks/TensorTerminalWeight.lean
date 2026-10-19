module

public import IntegerMultBounds.Networks.TensorCoordinates
public import IntegerMultBounds.Networks.BinaryPhase
public import IntegerMultBounds.Networks.NeighborCounts

/-! Exact coordinate support and Hamming weight of the actual tensor terminal
vectors. The coordinate permutation is retained; cardinality is invariant
under that permutation. -/

@[expose] public section

namespace IntegerMultBounds.Networks.TensorTerminalWeight

open Module Labels TensorCoordinates
open scoped TensorProduct

variable {h : ℕ}

end IntegerMultBounds.Networks.TensorTerminalWeight
