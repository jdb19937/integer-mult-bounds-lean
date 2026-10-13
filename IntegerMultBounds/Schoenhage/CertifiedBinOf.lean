module

public import IntegerMultBounds.Schoenhage.CertifiedPlacement
public import IntegerMultBounds.Schoenhage.LayoutGenSetup

/-! One reusable single-output adapter for both layout binary converters. -/
@[expose] public section
namespace IntegerMultBounds.Schoenhage.CertifiedSequence
open LayoutGenSetup

theorem binOf_output_update (value : ℕ) :
    bbank value (reg (Resampling.Script.bin value)) emp =
      Function.update (bbank value emp emp) 1 (reg (Resampling.Script.bin value)) := by
  funext tape
  fin_cases tape <;> rfl

theorem runs_binOf_update (value : ℕ) :
    Runs binOf (bbank value emp emp)
      (· = Function.update (bbank value emp emp) 1 (reg (Resampling.Script.bin value)))
      (8 * value * value + 70 * value + 40) := by
  rw [← binOf_output_update]
  exact runs_binOf value

end IntegerMultBounds.Schoenhage.CertifiedSequence
