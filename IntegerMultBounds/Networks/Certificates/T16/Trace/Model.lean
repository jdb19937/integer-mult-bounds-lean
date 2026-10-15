module

public import IntegerMultBounds.Networks.FramedEventTrace
public import Mathlib.Data.Rat.Defs

/-! Source-specific native-event bookkeeping. Private-center resets remain actual
scalar clears, and endpoint adapters remain explicit events. No frame operator
or supplier identity is supplied by this model. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Trace

inductive Scalar where
  | add (target source : ℕ) (num den : ℤ) (frame : ℕ)
  | scale (target : ℕ) (num den : ℤ) (frame : ℕ)
  | clear (target frame : ℕ)
  | copy (target source frame : ℕ)
  deriving DecidableEq, Repr

/-- Native JSON is target-first. Clear and copy are faithful, possibly noninvertible rows. -/
def Scalar.gate : Scalar → Circuit.Gate ℕ ℚ
  | .add t s n d _ => ⟨t, [(s, (n : ℚ) / (d : ℚ))]⟩
  | .scale t n d _ => ⟨t, [(t, (n : ℚ) / (d : ℚ) - 1)]⟩
  | .clear t _ => ⟨t, [(t, -1)]⟩
  | .copy t s _ => ⟨t, [(t, -1), (s, 1)]⟩

/-- A finite binary trie: the low bit chooses a branch. Generated profiles have
exactly ten levels, covering all 712 native registers. -/
inductive Labels where
  | leaf (frame : ℕ)
  | fork (even odd : Labels)
  deriving DecidableEq, BEq, Repr

instance : LawfulBEq Labels where
  eq_of_beq := by
    intro a b h
    induction a generalizing b with
    | leaf f => cases b <;> simp_all [BEq.beq, instBEqLabels.beq]
    | fork l r ihl ihr =>
      cases b with
      | leaf f => simp [BEq.beq, instBEqLabels.beq] at h
      | fork l' r' =>
        change ((l == l') && (r == r')) = true at h
        have hh := Bool.and_eq_true_iff.mp h
        exact congrArg₂ Labels.fork (ihl hh.1) (ihr hh.2)
  rfl := by
    intro a
    induction a <;> simp_all [BEq.beq, instBEqLabels.beq]

def Labels.get : Labels → ℕ → ℕ
  | .leaf f, i => if i = 0 then f else 0
  | .fork even odd, i => if i % 2 = 0 then even.get (i / 2) else odd.get (i / 2)

def Labels.put : Labels → ℕ → ℕ → Labels
  | .leaf f, i, next => .leaf (if i = 0 then next else f)
  | .fork even odd, i, next =>
      if i % 2 = 0 then .fork (even.put (i / 2) next) odd
      else .fork even (odd.put (i / 2) next)

structure State where
  labels : Labels
  phase : ℕ
  deriving DecidableEq, BEq, Repr

instance : LawfulBEq State where
  eq_of_beq := by
    rintro ⟨al, ap⟩ ⟨bl, bp⟩ h
    change ((al == bl) && (ap == bp)) = true at h
    have hh := Bool.and_eq_true_iff.mp h
    exact congrArg₂ State.mk (eq_of_beq hh.1) (eq_of_beq hh.2)
  rfl := by
    rintro ⟨al, ap⟩
    change ((al == al) && (ap == ap)) = true
    simp

def State.label (s : State) (i : ℕ) : ℕ := s.labels.get i
def State.put (s : State) (i : ℕ) (f : ℕ) : State :=
  ⟨s.labels.put i f, s.phase⟩

inductive Event where
  | scalar (s : Scalar)
  | climb (phase register old next rank : ℕ)
  | center (index old next rank : ℕ)
  | adapter (entry : Bool) (register frame : ℕ)
  | residual (pre : Bool) (register start : ℕ) (terminal : Option ℕ)
  | phase (index : ℕ)
  deriving DecidableEq, Repr

def scalarStep (s : State) : Scalar → Option State
  | .clear t f =>
      if t < 712 && 704 ≤ t && f < 1004 then some (s.put t f) else none
  | .copy t r f =>
      if t < 712 && 704 ≤ t && r < 712 && f < 1004 && s.label r == f
      then some (s.put t f) else none
  | .add t r _n d f =>
      if t < 712 && r < 712 && t != r && d != 0 && f < 1004 &&
          s.label r == f && s.label t == f then some s else none
  | .scale t _n d f =>
      if t < 712 && d != 0 && f < 1004 && s.label t == f then some s else none

def step (s : State) : Event → Option State
  | .scalar g => scalarStep s g
  | .climb phase r old next rank =>
      if s.phase == phase && r < 704 && old < 1004 && next < 1004 &&
          0 < rank && rank ≤ 9 && s.label r == old
      then some (s.put r next) else none
  | .center i old next rank =>
      if s.phase == 4 && i < 8 && old < 1004 && next < 1004 &&
          0 < rank && rank ≤ 9 && s.label (704+i) == old
      then some (s.put (704+i) next) else none
  | .adapter entry r f =>
      if s.phase == (if entry then 2 else 8) && r < 704 && f < 1004 && s.label r == f
      then some s else none
  | .residual pre r start terminal =>
      if s.phase == (if pre then 2 else 9) && 224 ≤ r && r < 704 && start < 1004 &&
          terminal.getD 1 < 1004 && s.label r == (if pre then start else terminal.getD 1)
      then some s else none
  | .phase i =>
      if s.phase == i && i < 10 then some ⟨s.labels, i+1⟩ else none

def run : State → List Event → Option State
  | s, [] => some s
  | s, e::es => (step s e).bind fun t => run t es

def runChunks : State → List (List Event) → Option State
  | s, [] => some s
  | s, es::ess => (run s es).bind fun t => runChunks t ess

/-- Scalar erasure retains the exact rational gates, including private clears and copies. -/
def erase : List Event → Circuit.Program ℕ ℚ
  | [] => []
  | .scalar g :: es => g.gate :: erase es
  | _ :: es => erase es

/-- Successful execution is the explicit source-specific continuity predicate. -/
def Valid (s : State) (es : List Event) : Prop := ∃ t, run s es = some t

theorem run_append (s : State) (xs ys : List Event) :
    run s (xs++ys) = (run s xs).bind (fun t => run t ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih =>
    simp only [List.cons_append, run]
    cases step s e <;> simp [ih]

theorem run_flatten (s : State) (chunks : List (List Event)) :
    run s chunks.flatten = runChunks s chunks := by
  induction chunks generalizing s with
  | nil => rfl
  | cons es ess ih =>
    simp only [List.flatten_cons, run_append, runChunks]
    cases run s es <;> simp [ih]

end IntegerMultBounds.Networks.Certificates.T16.Trace
