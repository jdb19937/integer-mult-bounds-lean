module

public import IntegerMultBounds.Networks.Certificates.T16.Trace.Forward

/-! The backward orientation, derived from the forward native trace. Each invertible gate is
replaced by its inverse transpose, in the same order, and each private center fan-out by its
transposed fan-in. The checks below and every downstream backward certificate evaluate this
derived list; it reproduces the supplier's backward events exactly. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Trace

/-- Inverse transpose of a scalar gate: an add exchanges target and source and negates, a scale
inverts. Clears and copies are unchanged. -/
def Scalar.dual : Scalar → Scalar
  | .add t r n d f => .add r t (-n) d f
  | .scale t n d f => .scale t d n f
  | g => g

/-- Gate duals, with a center move reversed. Climbs, adapters and markers are unchanged. -/
def Event.dual : Event → Event
  | .scalar g => .scalar g.dual
  | .center i old next rank => .center i next old rank
  | e => e

/-- A center transfer `t += c x` becomes `c += t x`. -/
def Event.transpose : Event → Event
  | .scalar (.add t r n d f) => .scalar (.add r t n d f)
  | e => e.dual

/-- The forward center block `clear c f, copy c s f, center, transfers out of c, clear` becomes
`clear, transfers into c, reversed center, add s c (-1), clear c f`. -/
def centerDual : List Event → List Event
  | .scalar (.clear c f) :: .scalar (.copy _ s _) :: center :: rest =>
      (rest.getLast?.map Event.dual).toList ++ rest.dropLast.map Event.transpose ++
        [center.dual, .scalar (.add s c (-1) 1 f), .scalar (.clear c f)]
  | es => es.map Event.dual

/-- The eight center blocks of the centers phase. -/
def centerStart : ℕ := 12551
def centerLength : ℕ := 26

def backwardEvents : List Event :=
  (forwardEvents.take centerStart).map Event.dual ++
    (List.range 8).flatMap (fun k =>
      centerDual ((forwardEvents.drop (centerStart + centerLength * k)).take centerLength)) ++
    (forwardEvents.drop (centerStart + 8 * centerLength)).map Event.dual

def backwardInitial : State := state0
def backwardFinal : State := state369
def backwardProgram : Circuit.Program ℕ ℚ := erase backwardEvents

theorem run_split (s : State) (es : List Event) (n : ℕ) :
    run s es = (run s (es.take n)).bind fun t => run t (es.drop n) := by
  rw [← run_append, List.take_append_drop]

/-! The run is checked in four kernel pieces between existing snapshots, keeping each
declaration's kernel memory small. -/

theorem backward_part0 : (run state0 (backwardEvents.take 6144) == some state1) = true := by
  decide +kernel

theorem backward_part1 :
    (run state1 ((backwardEvents.drop 6144).take 6144) == some state77) = true := by
  decide +kernel

theorem backward_part2 :
    (run state77 (((backwardEvents.drop 6144).drop 6144).take 6144) == some state368) = true := by
  decide +kernel

theorem backward_part3 :
    (run state368 (((backwardEvents.drop 6144).drop 6144).drop 6144) == some state369) = true := by
  decide +kernel

theorem backward_checked : run backwardInitial backwardEvents = some backwardFinal := by
  unfold backwardInitial backwardFinal
  rw [run_split _ _ 6144, eq_of_beq backward_part0, Option.bind_some,
    run_split _ _ 6144, eq_of_beq backward_part1, Option.bind_some,
    run_split _ _ 6144, eq_of_beq backward_part2, Option.bind_some, eq_of_beq backward_part3]

theorem backward_valid : Valid backwardInitial backwardEvents := ⟨backwardFinal, backward_checked⟩

theorem mem_centerDual {x : Event} {es : List Event} (h : x ∈ centerDual es) :
    (∃ e ∈ es, x = e.dual ∨ x = e.transpose) ∨ ∃ g, x = .scalar g := by
  unfold centerDual at h
  split at h
  · simp only [List.mem_append, Option.mem_toList, Option.map_eq_some_iff,
      List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with ((⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | rfl | rfl | rfl)
    · exact .inl ⟨e, by simp [List.mem_of_getLast? he], .inl rfl⟩
    · exact .inl ⟨e, by simp [List.dropLast_subset _ he], .inr rfl⟩
    · exact .inl ⟨_, by simp, .inl rfl⟩
    · exact .inr ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact .inl ⟨e, he, .inl rfl⟩

/-- Every backward event is the dual or transpose of a forward event, or a scalar gate. -/
theorem mem_backwardEvents {x : Event} (h : x ∈ backwardEvents) :
    (∃ e ∈ forwardEvents, x = e.dual ∨ x = e.transpose) ∨ ∃ g, x = .scalar g := by
  simp only [backwardEvents, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with ((⟨e, he, rfl⟩ | ⟨k, -, hk⟩) | ⟨e, he, rfl⟩)
  · exact .inl ⟨e, List.mem_of_mem_take he, .inl rfl⟩
  · rcases mem_centerDual hk with ⟨e, he, hx⟩ | hg
    · exact .inl ⟨e, List.mem_of_mem_drop (List.mem_of_mem_take he), hx⟩
    · exact .inr hg
  · exact .inl ⟨e, List.mem_of_mem_drop he, .inl rfl⟩

end IntegerMultBounds.Networks.Certificates.T16.Trace
