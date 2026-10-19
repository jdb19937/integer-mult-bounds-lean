module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

/-- Actual binary subspace inclusion and actual finite-dimensional rank difference. -/
def EdgeGood (catalog : ℕ → CertifiedFrame) (old next rank : ℕ) : Prop :=
  (catalog old).space ≤ (catalog next).space ∧
  Module.finrank F (catalog next).space - Module.finrank F (catalog old).space = rank ∧
  0 < rank

/-- Reduce `v` by each mask in turn, keeping an XOR when it lowers the value, i.e. when the mask's
leading bit is set in `v`. -/
def reduceBy (v : Mask) : List Mask → Mask
  | [] => v
  | e :: es => reduceBy (if (v ^^^ e).toNat < v.toNat then v ^^^ e else v) es

/-- Insert into a list sorted by decreasing value. -/
def insertDesc (r : Mask) : List Mask → List Mask
  | [] => [r]
  | e :: es => if e.toNat < r.toNat then r :: e :: es else e :: insertDesc r es

def insertReduced (m : Mask) (E : List Mask) : List Mask :=
  if reduceBy m E == 0 then E else insertDesc (reduceBy m E) E

/-- An echelon basis of the masks' span: distinct leading bits, in decreasing order. -/
def echelon : List Mask → List Mask
  | [] => []
  | m :: ms => insertReduced m (echelon ms)

theorem reduceBy_mem_iff (W : Submodule F Address) :
    ∀ (E : List Mask), (∀ e ∈ E, decode e ∈ W) → ∀ v, decode (reduceBy v E) ∈ W ↔ decode v ∈ W
  | [], _, v => Iff.rfl
  | e :: es, hE, v => by
    rw [reduceBy, reduceBy_mem_iff W es fun e' h => hE e' (List.mem_cons_of_mem _ h)]
    split_ifs
    · rw [decode_xor]
      exact W.add_mem_iff_left (hE e (List.mem_cons_self ..))
    · rfl

theorem mem_insertDesc {r x : Mask} : ∀ {E : List Mask}, x ∈ insertDesc r E → x = r ∨ x ∈ E
  | [], h => by simpa [insertDesc] using h
  | e :: es, h => by
    unfold insertDesc at h
    split_ifs at h
    · simpa using h
    · rcases List.mem_cons.mp h with h | h
      · exact .inr (h ▸ List.mem_cons_self ..)
      · rcases mem_insertDesc h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)

theorem echelon_mem (W : Submodule F Address) :
    ∀ ms : List Mask, (∀ m ∈ ms, decode m ∈ W) → ∀ e ∈ echelon ms, decode e ∈ W
  | [], _, e, he => by simp [echelon] at he
  | m :: ms, hm, e, he => by
    have hE := echelon_mem W ms fun m' h => hm m' (List.mem_cons_of_mem _ h)
    unfold echelon insertReduced at he
    split_ifs at he
    · exact hE e he
    · rcases mem_insertDesc he with rfl | he
      · exact (reduceBy_mem_iff W _ hE m).mpr (hm m (List.mem_cons_self ..))
      · exact hE e he

/-- Every mask of `a` reduces to zero against an echelon basis of the masks of `b`. -/
def Frame.covers (b a : Frame) : Bool :=
  (List.ofFn a.masks).all fun m => reduceBy m (echelon (List.ofFn b.masks)) == 0

theorem Frame.covers_sound {a b : Frame} (h : b.covers a = true) : a.space ≤ b.space := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hi := List.all_eq_true.mp h (a.masks i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hb : ∀ m ∈ List.ofFn b.masks, decode m ∈ b.space := by
    intro m hm
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
    exact Submodule.subset_span ⟨j, rfl⟩
  change decode (a.masks i) ∈ b.space
  rw [← reduceBy_mem_iff b.space _ (echelon_mem b.space _ hb), eq_of_beq hi, decode_zero]
  exact b.space.zero_mem

def checkEdge (catalog : ℕ → CertifiedFrame) (old next rank : ℕ) : Bool :=
  (catalog next).data.covers (catalog old).data &&
    (catalog next).data.rank - (catalog old).data.rank == rank && 0 < rank

theorem checkEdge_sound {catalog : ℕ → CertifiedFrame} {old next rank : ℕ}
    (h : checkEdge catalog old next rank = true) : EdgeGood catalog old next rank := by
  simp only [checkEdge, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hcovers, hrank⟩, hpos⟩ := h
  refine ⟨Frame.covers_sound hcovers, ?_, hpos⟩
  rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
  exact hrank

/-- Forward centers descend; backward centers ascend. All climbs ascend. -/
def EventGood (catalog : ℕ → CertifiedFrame) (backward : Bool) : Trace.Event → Prop
  | .climb _ _ old next rank => EdgeGood catalog old next rank
  | .center _ old next rank =>
      if backward then EdgeGood catalog old next rank else EdgeGood catalog next old rank
  | _ => True

def checkEvent (catalog : ℕ → CertifiedFrame) (backward : Bool) : Trace.Event → Bool
  | .climb _ _ old next rank => checkEdge catalog old next rank
  | .center _ old next rank =>
      if backward then checkEdge catalog old next rank else checkEdge catalog next old rank
  | _ => true

theorem checkEvent_sound {catalog : ℕ → CertifiedFrame}
    (backward : Bool) (event : Trace.Event) (h : checkEvent catalog backward event = true) :
    EventGood catalog backward event := by
  cases event <;> simp only [checkEvent, EventGood] at *
  · exact checkEdge_sound h
  · cases backward <;> exact checkEdge_sound h

def checkEvents (catalog : ℕ → CertifiedFrame) (backward : Bool) (events : List Trace.Event) :
    Bool := events.all (checkEvent catalog backward)

theorem checkEvents_split (catalog : ℕ → CertifiedFrame) (backward : Bool)
    (events : List Trace.Event) (n : ℕ) :
    checkEvents catalog backward events =
      (checkEvents catalog backward (events.take n) &&
        checkEvents catalog backward (events.drop n)) := by
  rw [checkEvents, checkEvents, checkEvents, ← List.all_append, List.take_append_drop]

theorem checkEvents_drop_split (catalog : ℕ → CertifiedFrame) (backward : Bool)
    (events : List Trace.Event) {k n k' : ℕ} (h : k + n = k') :
    checkEvents catalog backward (events.drop k) =
      (checkEvents catalog backward ((events.drop k).take n) &&
        checkEvents catalog backward (events.drop k')) := by
  rw [checkEvents_split _ _ (events.drop k) n, List.drop_drop, ← h, Nat.add_comm]

theorem checkEvents_sound {catalog : ℕ → CertifiedFrame}
    (backward : Bool) {events : List Trace.Event} (h : checkEvents catalog backward events = true)
    (event : Trace.Event) (he : event ∈ events) : EventGood catalog backward event :=
  checkEvent_sound backward event (List.all_eq_true.mp h event he)

end IntegerMultBounds.Networks.Certificates.T16.Geometry
