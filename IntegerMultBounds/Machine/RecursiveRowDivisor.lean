module

public import IntegerMultBounds.Machine.FixedBasePowerDescriptor
public import IntegerMultBounds.Machine.Shared50RecursiveNodeLayout
public import IntegerMultBounds.Machine.RecursiveRoleChildCallSetup

/-! The fixed Shared50 row divisor W^k is actually synthesized from a runtime
binary depth on the unchanged finite alphabet. Its cost is linear in a row
range known to dominate the divisor; no precomputed power descriptor is assumed. -/

@[expose] public section

namespace IntegerMultBounds.Machine.RecursiveRowDivisor
noncomputable section
open Networks
open Shared50TapeGlobal (roleCount)
variable {q : ℕ}

/-- The fixed World count is large, but never a runtime control parameter. -/
theorem base_ge_two : 2 ≤ roleCount := by
  rw [Shared50RecursiveNodeLayout.roleCount_eq_W,Shared50Parameters.wire_count]
  omega

def program := FixedBasePowerDescriptor.program (q := q) roleCount

def constant := FixedBasePowerDescriptor.constant roleCount

theorem construct_hoare (ks : List Bool) (k : ℕ) (hk : Counter.value ks = k)
    (hc : GrowingCounterData.Canonical ks) :
    HoareTime (program (q := q))
      (fun v => v = FixedBasePowerDescriptor.input ks)
      (fun v => v = FixedBasePowerDescriptor.output roleCount k ks) (constant*roleCount^k) :=
  FixedBasePowerDescriptor.constructs_linear roleCount k base_ge_two ks hk hc

theorem divisor_value (k : ℕ) :
    Counter.value (FixedBasePowerStep.bits roleCount k) = roleCount^k :=
  FixedBasePowerStep.bits_value roleCount k

end
end IntegerMultBounds.Machine.RecursiveRowDivisor
