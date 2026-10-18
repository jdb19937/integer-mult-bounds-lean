module

public import IntegerMultBounds.Networks.Certificates.T16.TableauExtension

/-! Unconditional binary X-block ranks for the completed frame extensions
and the retained native forward/backward events. Phases remain out of scope. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

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
