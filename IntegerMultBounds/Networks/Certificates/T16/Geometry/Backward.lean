module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Backward

/-! Backward geometry from the forward certificate: the backward trace is the forward one with
center moves reversed, which the orientation flip in `EventGood` cancels. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

theorem eventGood_dual (catalog : ℕ → CertifiedFrame) (e : Trace.Event) :
    EventGood catalog true e.dual ↔ EventGood catalog false e := by
  cases e <;> simp [Trace.Event.dual, EventGood]

theorem eventGood_transpose (catalog : ℕ → CertifiedFrame) (e : Trace.Event) :
    EventGood catalog true e.transpose ↔ EventGood catalog false e := by
  cases e with
  | scalar g => cases g <;> simp [Trace.Event.transpose, Trace.Event.dual, EventGood]
  | _ => simp [Trace.Event.transpose, Trace.Event.dual, EventGood]

theorem backward_geometry (event : Trace.Event) (h : event ∈ Trace.backwardEvents) :
    EventGood catalog true event := by
  rcases Trace.mem_backwardEvents h with ⟨e, he, rfl | rfl⟩ | ⟨g, rfl⟩
  · exact (eventGood_dual catalog e).mpr (forward_geometry e he)
  · exact (eventGood_transpose catalog e).mpr (forward_geometry e he)
  · trivial

end IntegerMultBounds.Networks.Certificates.T16.Geometry
