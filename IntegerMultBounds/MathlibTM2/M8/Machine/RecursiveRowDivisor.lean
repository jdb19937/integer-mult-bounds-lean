module

public import IntegerMultBounds.Machine.FixedBasePowerDescriptor
public import IntegerMultBounds.MathlibTM2.M8.Machine.Depth

/-! The fixed row divisor roleCount^k is actually synthesized from a runtime
binary depth on the unchanged finite alphabet. Its cost is linear in a row
range known to dominate the divisor; no precomputed power descriptor is assumed. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.RecursiveRowDivisor
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
variable {q : ℕ}

/-- The fixed role count is never a runtime control parameter. -/
theorem base_ge_two : 2 ≤ roleCount := two_le_roleCount

def program := FixedBasePowerDescriptor.program (q := q) roleCount

def constant := FixedBasePowerDescriptor.constant roleCount

theorem construct_hoare (ks : List Bool) (k : ℕ) (hk : Counter.value ks = k)
    (hc : GrowingCounterData.Canonical ks) :
    HoareTime (program (q := q))
      (fun v => v = FixedBasePowerDescriptor.input ks)
      (fun v => v = FixedBasePowerDescriptor.output roleCount k ks) (constant*roleCount^k) :=
  FixedBasePowerDescriptor.constructs_linear roleCount k base_ge_two ks hk hc

/-- A supplied dominating row range absorbs all real power construction work. -/
theorem construct_bounded (ks : List Bool) (k V : ℕ) (hk : Counter.value ks = k)
    (hc : GrowingCounterData.Canonical ks) (hV : roleCount^k ≤ V) :
    HoareTime (program (q := q))
      (fun v => v = FixedBasePowerDescriptor.input ks)
      (fun v => v = FixedBasePowerDescriptor.output roleCount k ks) (constant*V) :=
  (construct_hoare ks k hk hc).consequence (fun _ h => h) (fun _ h => h)
    (Nat.mul_le_mul_left constant hV)

theorem divisor_value (k : ℕ) :
    Counter.value (FixedBasePowerStep.bits roleCount k) = roleCount^k :=
  FixedBasePowerStep.bits_value roleCount k

theorem divisor_canonical (k : ℕ) :
    GrowingCounterData.Canonical (FixedBasePowerStep.bits roleCount k) :=
  FixedBasePowerStep.bits_canonical roleCount k

end
end IntegerMultBounds.MathlibTM2.M8.Machine.RecursiveRowDivisor
