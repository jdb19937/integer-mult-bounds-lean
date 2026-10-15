module

public import IntegerMultBounds.Networks.Certificates.PR589.Scalar
public import IntegerMultBounds.Networks.RankTrace

/-! Literal frame-ID state replay, distinct from scalar XOR replay.
Frame IDs are labels only: geometry, dimensions and ranks are not assumed. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Frames

def touched (g : RawGate) : List ℕ := g.target :: g.sources

def step (g : RawGate) (current : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i ∈ touched g then g.frame else current i

def run : List RawGate → (ℕ → ℕ) → (ℕ → ℕ)
  | [], current => current
  | g :: gs, current => run gs (step g current)

theorem run_append (gs hs : List RawGate) (current : ℕ → ℕ) :
    run (gs ++ hs) current = run hs (run gs current) := by
  induction gs generalizing current with
  | nil => rfl
  | cons g gs ih => exact ih _

def updates (gs : List RawGate) : List (ℕ × ℕ) :=
  gs.flatMap fun g => (touched g).map fun i => (i, g.frame)

/-- Every incidence survives in order, including repeated and identity edges. -/
def edges (gs : List RawGate) (current : ℕ → ℕ) : List (ℕ × ℕ) :=
  RankTrace.edges current (updates gs)

theorem step_eq_finish (g : RawGate) (current : ℕ → ℕ) :
    step g current = RankTrace.finish current ((touched g).map fun i => (i, g.frame)) := by
  funext i
  rw [RankTrace.finish_align]
  rfl

theorem run_eq_finish (gs : List RawGate) (current : ℕ → ℕ) :
    run gs current = RankTrace.finish current (updates gs) := by
  induction gs generalizing current with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, updates, List.flatMap_cons, RankTrace.finish_append]
    rw [← step_eq_finish]
    exact ih _

theorem edges_append (gs hs : List RawGate) (current : ℕ → ℕ) :
    edges (gs ++ hs) current = edges gs current ++ edges hs (run gs current) := by
  simp only [edges, updates, List.flatMap_append, RankTrace.edges_append]
  rw [run_eq_finish]
  rfl

def snapshot (refs : ℕ → ℕ) (i : ℕ) : ℕ := if i < 661 then refs i else 0

theorem run_preserves (gs : List RawGate) (current : ℕ → ℕ) (i : ℕ)
    (h : ∀ g ∈ gs, i ∉ touched g) : run gs current i = current i := by
  induction gs generalizing current with
  | nil => rfl
  | cons g gs ih =>
    rw [run, ih _ (fun g hg => h g (List.mem_cons_of_mem _ hg))]
    exact ite_eq_right (h g (List.mem_cons_self))

theorem bounded_touched (gs : List RawGate) (hb : gs.all RawGate.bounded = true) :
    ∀ g ∈ gs, ∀ i ∈ touched g, i < 661 := by
  intro g hg i hi
  have h : g.target < 661 ∧ ∀ j ∈ g.sources, j < 661 := by
    simpa [RawGate.bounded, List.all_eq_true] using List.all_eq_true.mp hb g hg
  rcases List.mem_cons.mp hi with he | hs
  · exact he ▸ h.1
  · exact h.2 i hs

/-- Finite pointwise replay plus certified gate bounds gives full state equality. -/
theorem checkpoint (gs : List RawGate) (before after : ℕ → ℕ)
    (hb : ∀ g ∈ gs, ∀ i ∈ touched g, i < 661)
    (hc : ∀ i : Fin 661, run gs (snapshot before) i.val = snapshot after i.val) :
    run gs (snapshot before) = snapshot after := by
  funext i
  by_cases hi : i < 661
  · exact hc ⟨i, hi⟩
  · rw [run_preserves gs _ i (fun g hg hmem => hi (hb g hg i hmem))]
    simp [snapshot, hi]

/-- COPY records explicitly retain distinct source and target frames. -/
structure Copy where
  target : ℕ
  source : ℕ
  targetFrame : ℕ
  sourceFrame : ℕ
  deriving DecidableEq, Repr

def copies (current : ℕ → ℕ) (gs : List RawGate) : List Copy :=
  gs.flatMap fun g => g.sources.map fun i =>
    ⟨g.target, i, current g.target, current i⟩

/-- Scatter copies values without changing any register's frame label. -/
def scatterFinish (current : ℕ → ℕ) : ℕ → ℕ := current

end IntegerMultBounds.Networks.Certificates.PR589.Frames
