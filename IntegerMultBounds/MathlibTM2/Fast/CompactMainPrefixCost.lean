module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainHost
public import IntegerMultBounds.MathlibTM2.Fast.MainChain

/-! Exact accounting for input/distribution, the complete arithmetic chain and output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Fast.ChirpSt
noncomputable section

/-- Prefix costs include all primitive stages and the actual expanded source runs. -/
theorem compactRetunedPreTime_eq (extra n : ℕ) :
    compactRetunedPreTime extra n =
      8*n+14+pmCost n mnUs+compactRetunedDist.cost n +
      mnChainCost n (dsW n) (compactMainRuns compactRetunedDist compactRetunedCF compactRetunedCO n) +
      carryOutCost (mnWo n) (b n) (S n) + extra := by
  unfold compactRetunedPreTime compactMainPreCost mnChainCost mnTail
  change (4*n+6)+(4*n+8)+pmCost n mnUs+compactRetunedDist.cost n+
      2*digitCost (b n) (p n) (dsW n) (S n)+
      (compactMainRuns compactRetunedDist compactRetunedCF compactRetunedCO n+extra)+
      mnGlue n (dsW n)+_ = _
  simp only [bdW]
  omega

/-- The sixteen-step allowance covers the combined input wrapper and twelve chain wrappers. -/
theorem compactRetuned_prefix_cost_le {n a z : ℕ}
    (ha : a ≤ 8*n+14+pmCost n mnUs+compactRetunedDist.cost n+1)
    (hz : z ≤ mnChainCost n (dsW n)
      (compactMainRuns compactRetunedDist compactRetunedCF compactRetunedCO n)+12) :
    a+z+carryOutCost (mnWo n) (b n) (S n) ≤ compactRetunedPreTime 16 n := by
  rw [compactRetunedPreTime_eq]
  omega

end
end IntegerMultBounds.MathlibTM2.Fast.Main
