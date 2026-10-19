module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Network

/-!
# The network of the machine

`Net` fixes the bit network the recursive interchange machine runs, as an instance, so the
machine's definitions refer to it the way the Shared50 machine refers to its fixed control. A
wire of the control is a contract role or a temporary (`Wire`); wires are enumerated as
`Fin wireCount`, contract roles first (`wireEquiv`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks

/-- The bit network of the machine, with what the machine needs of it. -/
class Net where
  net : BitNetwork
  supports : Supports net

variable [Net]

/-- The contract roles. -/
abbrev World : Type := (Net.net).World
/-- The machine-private temporaries. -/
abbrev Temp : Type := (Net.net).Temp
/-- The wires of the control. -/
abbrev Wire : Type := World ⊕ Temp
/-- The number of contract roles. -/
abbrev roleCount : ℕ := (Net.net).roleCount
/-- The number of temporaries. -/
abbrev tempCount : ℕ := (Net.net).tempCount
/-- Address coordinates per field. -/
abbrev width : ℕ := (Net.net).width
/-- The edge programs. -/
abbrev FieldProgram : Type := M8.FieldProgram width
/-- One step of the control. -/
abbrev Control : Type := Step Wire FieldProgram
/-- The fixed control. -/
abbrev control : List Control := (Net.net).control

/-- The number of wires. -/
abbrev wireCount : ℕ := roleCount + tempCount

/-- The wires, contract roles first. -/
def wireEquiv : Fin wireCount ≃ Wire :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Net.net).roleEquiv (Net.net).tempEquiv)

theorem width_le_roleCount : width ≤ roleCount := (Net.supports).width_le_roleCount

theorem two_le_width : 2 ≤ width := (Net.net).two_le_width

theorem width_pos : 0 < width := lt_of_lt_of_le two_pos two_le_width

theorem one_lt_width : 1 < width := two_le_width

theorem two_le_roleCount : 2 ≤ roleCount := two_le_width.trans width_le_roleCount

theorem roleCount_pos : 0 < roleCount := lt_of_lt_of_le two_pos two_le_roleCount

theorem two_le_width_real : (2 : ℝ) ≤ width := by exact_mod_cast two_le_width

theorem one_lt_width_real : (1 : ℝ) < width := by exact_mod_cast one_lt_width

theorem wireCount_pos : 0 < wireCount := Nat.lt_of_lt_of_le roleCount_pos (Nat.le_add_right _ _)

open Shared50ModularControl (prime)

/-- The network's reductions are legal at the machine's prime. -/
theorem legal_mod (b : ℕ) (i : Wire) (p : FieldProgram) (hp : Step.edge i p ∈ control) :
    ∀ op ∈ specialize (prime ^ b) p, AffineFieldProgram.Legal op := by
  rw [← (Net.supports).prime_eq]
  exact (Net.net).legal_mod b i p hp

/-- The node theorem at the machine's prime. -/
theorem run_identity (b : ℕ) (stored : Wire → Arrays width (prime ^ b))
    (h0 : ∀ t, stored (.inr t) = 0) (i : World) (a : Address width (prime ^ b)) :
    Step.run (edgeAction width (prime ^ b)) control stored (.inl i) a =
      stored (.inl ((Net.net).route i)) (a.2, a.1) := by
  have h := (Net.net).run_identity b
  rw [(Net.supports).prime_eq] at h
  exact h stored h0 i a

end
end IntegerMultBounds.MathlibTM2.M8.Machine
