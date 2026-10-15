module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesCatalog

/-! Unconditional binary X-block ranks for the exact source extension matrices
and the retained native forward/backward events. Phases remain out of scope. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

/-- The checked dual masks are exactly the rows of the inverse address map. -/
theorem MatrixWitness.equiv_symm (m : MatrixWitness) (h : m.DualCheck) (x : Address) :
    (m.equiv h).symm x = m.backward x := by
  have hi := LinearMap.congr_fun (m.left_inverse h) ((m.equiv h).symm x)
  change m.backward (m.equiv h ((m.equiv h).symm x)) = (m.equiv h).symm x at hi
  rw [LinearEquiv.apply_symm_apply] at hi
  exact hi.symm

theorem nativeTableau_inverse_Z (id : ℕ) :
    inverseZ (nativeTableau id) = frameLagrangian (catalog id).space := by
  rw [nativeTableau, sourceCanonical_inverse_Z, (catalogExtension id).space]

theorem native_forward_climb {phase register old next rank : ℕ}
    (h : Trace.Event.climb phase register old next rank ∈ Trace.forwardEvents) :
    Module.finrank F (LinearMap.range (bBlock (nativeTableau old) (nativeTableau next))) = rank :=
  forward_climb_rank (catalogExtension old) (catalogExtension next) h

theorem native_backward_climb {phase register old next rank : ℕ}
    (h : Trace.Event.climb phase register old next rank ∈ Trace.backwardEvents) :
    Module.finrank F (LinearMap.range (bBlock (nativeTableau old) (nativeTableau next))) = rank :=
  backward_climb_rank (catalogExtension old) (catalogExtension next) h

theorem native_forward_center {index old next rank : ℕ}
    (h : Trace.Event.center index old next rank ∈ Trace.forwardEvents) :
    Module.finrank F (LinearMap.range (bBlock (nativeTableau old) (nativeTableau next))) = rank :=
  forward_center_rank (catalogExtension old) (catalogExtension next) h

theorem native_backward_center {index old next rank : ℕ}
    (h : Trace.Event.center index old next rank ∈ Trace.backwardEvents) :
    Module.finrank F (LinearMap.range (bBlock (nativeTableau old) (nativeTableau next))) = rank :=
  backward_center_rank (catalogExtension old) (catalogExtension next) h

/-- Actual relative X-block rank for climb/center events; other events add no claim. -/
def NativeRankGood : Trace.Event → Prop
  | .climb _ _ old next rank =>
      Module.finrank F (LinearMap.range (bBlock (nativeTableau old) (nativeTableau next))) = rank
  | .center _ old next rank =>
      Module.finrank F (LinearMap.range (bBlock (nativeTableau old) (nativeTableau next))) = rank
  | _ => True

theorem native_forward_ranks (event : Trace.Event) (h : event ∈ Trace.forwardEvents) :
    NativeRankGood event := by
  cases event <;> simp only [NativeRankGood]
  · exact native_forward_climb h
  · exact native_forward_center h

theorem native_backward_ranks (event : Trace.Event) (h : event ∈ Trace.backwardEvents) :
    NativeRankGood event := by
  cases event <;> simp only [NativeRankGood]
  · exact native_backward_climb h
  · exact native_backward_center h

end IntegerMultBounds.Networks.Certificates.T16.Tableau
