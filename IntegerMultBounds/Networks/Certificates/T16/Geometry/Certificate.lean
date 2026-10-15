module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward
public import Mathlib.LinearAlgebra.Basis.Basic

/-! The exact selected catalog as actual binary subspaces, with its literal
native climb and center rank declarations justified geometrically. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

/-- The original ordered mask vectors form a basis of their actual span. -/
noncomputable def catalogBasis (id : ℕ) :
    Module.Basis (Fin (catalog id).data.rank) F (catalog id).space :=
  Module.Basis.span (catalog id).independent

theorem catalogBasis_retains (id : ℕ) (i : Fin (catalog id).data.rank) :
    (catalogBasis id i : Address) = (catalog id).data.vectors i :=
  Module.Basis.coe_span_apply _ _

theorem forward_climb {phase register old next rank : ℕ}
    (h : Trace.Event.climb phase register old next rank ∈ Trace.forwardEvents) :
    EdgeGood catalog old next rank := forward_geometry _ h

theorem backward_climb {phase register old next rank : ℕ}
    (h : Trace.Event.climb phase register old next rank ∈ Trace.backwardEvents) :
    EdgeGood catalog old next rank := backward_geometry _ h

theorem forward_center {index old next rank : ℕ}
    (h : Trace.Event.center index old next rank ∈ Trace.forwardEvents) :
    EdgeGood catalog next old rank := forward_geometry _ h

theorem backward_center {index old next rank : ℕ}
    (h : Trace.Event.center index old next rank ∈ Trace.backwardEvents) :
    EdgeGood catalog old next rank := backward_geometry _ h

/-- This selected nonzero direction is isotropic for the existing binary form.
Independence must not be confused with restricted nondegeneracy. -/
theorem selected_isotropic_direction :
    30#9 ≠ (0 : Mask) ∧ Labels.binary 9 (decode 30#9) (decode 30#9) = 0 := by decide

end IntegerMultBounds.Networks.Certificates.T16.Geometry
