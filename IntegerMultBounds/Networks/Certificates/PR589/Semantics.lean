module

public import IntegerMultBounds.Networks.Certificates.PR589.FirstCheckpoint
public import IntegerMultBounds.Networks.BinaryScalarReplay

/-! Sound interpretation of PR589 symbolic replay for arbitrary dirty inputs.
Only the first four scalar gates have a concrete checked replay certificate.
No complete-word, framed-network, owner-schedule or tape-cost claim is made. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589
open BinaryScalarReplay

/-- Every symbolic replay step is the corresponding actual scalar gate. -/
theorem eval_replay (gs : List RawGate) (state : ℕ → BitVec 661)
    (stored : Fin 661 → ZMod 2) :
    (fun i => eval (replay gs state i) stored) =
      Circuit.run (gs.map RawGate.toCircuit) (fun i => eval (state i) stored) := by
  induction gs generalizing state with
  | nil => rfl
  | cons g gs ih =>
    change (fun i => eval (replay gs (step g state) i) stored) =
      Circuit.run (gs.map RawGate.toCircuit) (g.toCircuit.run (fun i => eval (state i) stored))
    rw [ih]
    exact congrArg (Circuit.run (gs.map RawGate.toCircuit))
      (eval_row_update g.target g.sources state stored)

/-- Every physical input register retains its arbitrary original value. -/
theorem eval_initial (stored : Fin 661 → ZMod 2) (i : Fin 661) :
    eval (initial i.val) stored = stored i := eval_singleton i stored

/-- The first checked scalar prefix preserves all registers outside its four
updated targets, even when sources, targets and helpers start dirty. -/
theorem first_four_dirty_preserves (stored : Fin 661 → ZMod 2) (i : Fin 661)
    (h : i.val < 111 ∨ 115 ≤ i.val) :
    Circuit.run ((sectionD.take 4).map RawGate.toCircuit)
      (fun j => eval (initial j) stored) i.val = stored i := by
  rw [← eval_replay]
  change eval (replay (sectionD.take 4) initial i.val) stored = stored i
  rw [first_four_preserves i.val h, eval_initial]

end IntegerMultBounds.Networks.Certificates.PR589
