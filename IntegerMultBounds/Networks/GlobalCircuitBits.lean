module

public import IntegerMultBounds.Networks.GlobalCircuit
public import IntegerMultBounds.Networks.CircuitBits

/-! The full three-coordinate bit network on the actual physical wire layout.
This establishes scalar routing and dirty-scratch restoration. Like the generic
global circuit, it does not establish grouped incidence topology or tape costs. -/

@[expose] public section

namespace IntegerMultBounds.Networks.GlobalCircuit

open Circuit NeighborCounts

/-- Enumerate local neighboring pairs using the actual global side-wire names. -/
def bitLocalPairs {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ BitPairs h) :
    Fin a ≃ BitPair (fun i => (eB i).val) :=
  eA.trans (pairsEquiv eB (@BitNeighbor h)).symm

end IntegerMultBounds.Networks.GlobalCircuit
