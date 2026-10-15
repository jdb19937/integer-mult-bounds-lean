module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Certificate
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Lagrangian

/-! Bind the doubled-space intersection deficit to retained native event widths.
This is not a Clifford tableau or operator-rank certificate. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

theorem edge_lagrangian_deficit {old next rank : ℕ}
    (h : EdgeGood catalog old next rank) :
    9 - Module.finrank F
      (frameLagrangian (catalog old).space ⊓ frameLagrangian (catalog next).space : Submodule F PhaseAddress) = rank := by
  rw [frameLagrangian_inf_deficit h.1]
  exact h.2.1

theorem forward_climb_lagrangian {phase register old next rank : ℕ}
    (h : Trace.Event.climb phase register old next rank ∈ Trace.forwardEvents) :
    9 - Module.finrank F
      (frameLagrangian (catalog old).space ⊓ frameLagrangian (catalog next).space : Submodule F PhaseAddress) = rank :=
  edge_lagrangian_deficit (forward_climb h)

theorem backward_climb_lagrangian {phase register old next rank : ℕ}
    (h : Trace.Event.climb phase register old next rank ∈ Trace.backwardEvents) :
    9 - Module.finrank F
      (frameLagrangian (catalog old).space ⊓ frameLagrangian (catalog next).space : Submodule F PhaseAddress) = rank :=
  edge_lagrangian_deficit (backward_climb h)

theorem forward_center_lagrangian {index old next rank : ℕ}
    (h : Trace.Event.center index old next rank ∈ Trace.forwardEvents) :
    9 - Module.finrank F
      (frameLagrangian (catalog next).space ⊓ frameLagrangian (catalog old).space : Submodule F PhaseAddress) = rank :=
  edge_lagrangian_deficit (forward_center h)

theorem backward_center_lagrangian {index old next rank : ℕ}
    (h : Trace.Event.center index old next rank ∈ Trace.backwardEvents) :
    9 - Module.finrank F
      (frameLagrangian (catalog old).space ⊓ frameLagrangian (catalog next).space : Submodule F PhaseAddress) = rank :=
  edge_lagrangian_deficit (backward_center h)

end IntegerMultBounds.Networks.Certificates.T16.Geometry
