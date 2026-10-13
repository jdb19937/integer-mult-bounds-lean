module

public import IntegerMultBounds.Schoenhage.Ops

/-! Small certificates for straight-line word programs. All bounds and full
bank endpoints are inferred from existing `Runs` proofs. Composition charges
the actual connecting transition; compilation uses the existing literal-machine
correctness theorem. No proof search or additional trusted evaluator is used. -/

@[expose] public section
namespace IntegerMultBounds.Schoenhage.CertifiedSequence
open Machine

/-- A command with an exact whole-bank endpoint and a checked step bound. -/
structure Block (alphabet tapes : ℕ) (input : Fin tapes → WTape) where
  command : Cmd alphabet tapes
  output : Fin tapes → WTape
  bound : ℕ
  runs : Runs command input (· = output) bound

variable {alphabet tapes : ℕ} {input : Fin tapes → WTape}

/-- Recover the command, endpoint and bound from an existing checked proof. -/
def ofRuns {command : Cmd alphabet tapes} {output : Fin tapes → WTape} {bound : ℕ}
    (proof : Runs command input (· = output) bound) : Block alphabet tapes input :=
  ⟨command, output, bound, proof⟩

/-- The second block must start at the actual first block's entire output bank. -/
def Block.then (first : Block alphabet tapes input)
    (second : Block alphabet tapes first.output) : Block alphabet tapes input :=
  ⟨.seq first.command second.command, second.output, first.bound + 1 + second.bound,
    Runs.then first.runs second.runs⟩

/-- Certificates retain a real halting run of the compiled finite machine. -/
theorem Block.hoare (block : Block alphabet tapes input) (tapesPositive : 0 < tapes) :
    HoareTime (compile tapesPositive block.command).2
      (· = enc input) (· = enc block.output) block.bound := by
  obtain ⟨output, elapsed, execution, endpoint, bounded⟩ := block.runs
  subst output
  exact (compile_correct tapesPositive execution).consequence
    (fun _ hypothesis => hypothesis) (fun _ hypothesis => hypothesis) bounded

end IntegerMultBounds.Schoenhage.CertifiedSequence
