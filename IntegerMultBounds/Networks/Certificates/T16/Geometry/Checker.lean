module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

/-- Actual binary subspace inclusion and actual finite-dimensional rank difference. -/
def EdgeGood (catalog : ℕ → CertifiedFrame) (old next rank : ℕ) : Prop :=
  (catalog old).space ≤ (catalog next).space ∧
  Module.finrank F (catalog next).space - Module.finrank F (catalog old).space = rank ∧
  0 < rank

structure CertifiedEdge (catalog : ℕ → CertifiedFrame) where
  old : ℕ
  next : ℕ
  rank : ℕ
  good : EdgeGood catalog old next rank

def edgeKey (old next : ℕ) : ℕ := old * 1004 + next

def checkEdge {catalog : ℕ → CertifiedFrame} (bank : ℕ → CertifiedEdge catalog)
    (old next rank : ℕ) : Bool :=
  let e := bank (edgeKey old next)
  e.old == old && e.next == next && e.rank == rank

theorem checkEdge_sound {catalog : ℕ → CertifiedFrame} (bank : ℕ → CertifiedEdge catalog)
    {old next rank : ℕ} (h : checkEdge bank old next rank = true) :
    EdgeGood catalog old next rank := by
  simp only [checkEdge, Bool.and_eq_true_iff, beq_iff_eq] at h
  obtain ⟨⟨ho, hn⟩, hr⟩ := h
  simpa only [ho, hn, hr] using (bank (edgeKey old next)).good

/-- Forward centers descend; backward centers ascend. All climbs ascend. -/
def EventGood (catalog : ℕ → CertifiedFrame) (backward : Bool) : Trace.Event → Prop
  | .climb _ _ old next rank => EdgeGood catalog old next rank
  | .center _ old next rank =>
      if backward then EdgeGood catalog old next rank else EdgeGood catalog next old rank
  | _ => True

def checkEvent {catalog : ℕ → CertifiedFrame} (bank : ℕ → CertifiedEdge catalog)
    (backward : Bool) : Trace.Event → Bool
  | .climb _ _ old next rank => checkEdge bank old next rank
  | .center _ old next rank =>
      if backward then checkEdge bank old next rank else checkEdge bank next old rank
  | _ => true

theorem checkEvent_sound {catalog : ℕ → CertifiedFrame} (bank : ℕ → CertifiedEdge catalog)
    (backward : Bool) (event : Trace.Event) (h : checkEvent bank backward event = true) :
    EventGood catalog backward event := by
  cases event <;> simp only [checkEvent, EventGood] at *
  · exact checkEdge_sound bank h
  · cases backward <;> exact checkEdge_sound bank h

def checkEvents {catalog : ℕ → CertifiedFrame} (bank : ℕ → CertifiedEdge catalog)
    (backward : Bool) (events : List Trace.Event) : Bool := events.all (checkEvent bank backward)

theorem checkEvents_flatten {catalog : ℕ → CertifiedFrame} (bank : ℕ → CertifiedEdge catalog)
    (backward : Bool) (chunks : List (List Trace.Event)) :
    checkEvents bank backward chunks.flatten = chunks.all (checkEvents bank backward) :=
  List.all_flatten

theorem checkEvents_sound {catalog : ℕ → CertifiedFrame} (bank : ℕ → CertifiedEdge catalog)
    (backward : Bool) {events : List Trace.Event} (h : checkEvents bank backward events = true)
    (event : Trace.Event) (he : event ∈ events) : EventGood catalog backward event :=
  checkEvent_sound bank backward event (List.all_eq_true.mp h event he)

end IntegerMultBounds.Networks.Certificates.T16.Geometry
