module

public import IntegerMultBounds.Machine.Shared50RecursiveNodeLayout
public import IntegerMultBounds.Machine.RecursiveRoleChildCallSetup

/-! Dimension facts for the actual power-width recursion. Splitting the node's
rows once, then entering a selected cross child with divisor one, consumes
exactly one factor of the World count and one power of the width radix. -/

@[expose] public section

namespace IntegerMultBounds.Machine.Shared50RecursiveDepth
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount)
open RecursiveInterchangeLayout (Descriptor role child volume)

/-- All dimension premises of a recursive node, with arbitrary positive
spectator factors. The row condition is the manuscript's W^depth condition. -/
structure Shape (depth : ℕ) (v : Descriptor) : Prop where
  positive : v.Positive
  width : v.width = 125000^depth
  rows : roleCount^depth ∣ v.rows

theorem roleCount_positive : 0 < roleCount := by decide

theorem base_width {v : Descriptor} (h : Shape 0 v) : v.width = 1 := by
  simpa only [pow_zero] using h.width

theorem split_divides {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v) :
    roleCount ∣ v.rows :=
  dvd_trans (by rw [pow_succ]; exact dvd_mul_left _ _) h.rows

theorem split_positive {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v) :
    (role v roleCount).Positive :=
  RecursiveRowsNodeLayout.role_positive _ _ roleCount_positive h.positive (split_divides h)

theorem split_width {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v) :
    (role v roleCount).width = 125000*(125000^depth) := by
  change v.width = _
  rw [h.width,pow_succ,Nat.mul_comm]

/-- The exact descriptor constructed by the same-row physical call setup. -/
def selected (depth : ℕ) (v : Descriptor) (i j : Fin 125000) : Descriptor :=
  child prime 1 (125000^depth) (role v roleCount) i j

theorem selected_eq (depth : ℕ) (v : Descriptor) (i j : Fin 125000) :
    selected depth v i j = child prime roleCount (125000^depth) v i j :=
  RecursiveRowsNodeLayout.child_role _ _ _ _ _ _

theorem selected_shape {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v)
    (i j : Fin 125000) : Shape depth (selected depth v i j) := by
  rw [selected_eq]
  exact ⟨RecursiveInterchangeLayout.child_positive _ _ _ _ _ _
      Shared50ModularControl.prime_prime.pos roleCount_positive (split_divides h) h.positive,
    rfl,RecursiveInterchangeLayout.child_rows_divisible _ _ _ _ _ _ _ roleCount_positive h.rows⟩

/-- The runtime volume is exactly one role stream, rather than the parked
ancestor bank or the full unsplit parent. -/
theorem selected_volume_role {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v)
    (i j : Fin 125000) :
    volume prime (selected depth v i j) = volume prime (role v roleCount) :=
  RecursiveAffineViews.cross_volume _ _ _ _ _ (split_width h)

theorem selected_volume {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v)
    (i j : Fin 125000) :
    volume prime (selected depth v i j) = volume prime v/roleCount := by
  rw [selected_eq]
  apply RecursiveInterchangeLayout.child_volume_div _ _ _ _ _ _ _ roleCount_positive (split_divides h)
  rw [h.width,pow_succ,Nat.mul_comm]

end
end IntegerMultBounds.Machine.Shared50RecursiveDepth
