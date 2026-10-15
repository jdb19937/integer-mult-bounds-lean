module

public import IntegerMultBounds.Networks.Circuit
public import Mathlib.Data.BitVec

/-! Literal scalar records and exact binary-column replay for PR589.
This is a certificate checker, not yet a soundness theorem for Circuit.run.
Frame metadata is retained but its interpretation and pricing are separate. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589

structure RawGate where
  frame : ℕ
  target : ℕ
  sources : List ℕ
  deriving DecidableEq

def RawGate.bounded (g : RawGate) : Bool :=
  decide (g.target < 661) && g.sources.all (fun i => decide (i < 661))

/-- Translate the literal scalar operation without changing its arity. -/
def RawGate.toCircuit (g : RawGate) : Circuit.Gate ℕ (ZMod 2) :=
  ⟨g.target, g.sources.map (fun i => (i, 1))⟩

/-- The source list is read from the pre-gate state, including dirty registers. -/
theorem RawGate.run_eq (g : RawGate) (stored : ℕ → ZMod 2) :
    g.toCircuit.run stored = Function.update stored g.target
      (stored g.target + (g.sources.map stored).sum) := by
  simp [toCircuit, Circuit.Gate.run, List.map_map, Function.comp_def]

def initial (i : ℕ) : BitVec 661 := BitVec.ofNat 661 (2^i)

def step (g : RawGate) (state : ℕ → BitVec 661) : ℕ → BitVec 661 :=
  Function.update state g.target
    (g.sources.foldl (fun v i => v ^^^ state i) (state g.target))

def replay (gs : List RawGate) (state : ℕ → BitVec 661) : ℕ → BitVec 661 :=
  gs.foldl (fun s g => step g s) state

theorem replay_append (left right : List RawGate) (state : ℕ → BitVec 661) :
    replay (left ++ right) state = replay right (replay left state) := by
  simp [replay, List.foldl_append]

theorem replay_preserves (gs : List RawGate) (state : ℕ → BitVec 661) (i : ℕ)
    (h : ∀ g ∈ gs, g.target ≠ i) : replay gs state i = state i := by
  induction gs generalizing state with
  | nil => rfl
  | cons g gs ih =>
    change replay gs (step g state) i = state i
    rw [ih _ (fun g hg => h g (List.mem_cons_of_mem _ hg))]
    exact Function.update_of_ne (h g (List.mem_cons_self)).symm _ _

end IntegerMultBounds.Networks.Certificates.PR589
