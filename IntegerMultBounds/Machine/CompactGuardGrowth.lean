module

public import IntegerMultBounds.Machine.CompactScalarAllowances
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The actual ceiling logarithmic guard is negligible relative to the
actual floor chunk width. This quantifies the eventual guard allowance with
any positive coefficient, rather than only one fixed safety margin. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactGuardGrowth
noncomputable section
open Filter Asymptotics Sizes TimeBound Parameters CompactScalarAllowances

end
end IntegerMultBounds.Machine.CompactGuardGrowth
