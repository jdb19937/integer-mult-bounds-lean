module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainDispatch
public import IntegerMultBounds.MathlibTM2.Fast.CompactBundleWires
public import IntegerMultBounds.MathlibTM2.Fast.MainFinal
public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedTransformMatch

/-! Complete cost envelope for the concrete compact branch. The machine-execution
contract is still explicit; the unconditional public multiplier is not changed here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 Filter Asymptotics
open IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack
noncomputable section

/-- The actual retuned distribution, including its charged wires update. -/
def compactRetunedDist := compactBdDist mn_postParam_bd

/-- The two complete transforms, including layout, bootstrap and cleanup. -/
def compactRetunedCF (n : ℕ) : ℕ := compactSynRetunedFwdCost n (compactBlCL n)
def compactRetunedCO (n : ℕ) : ℕ := compactSynRetunedOppCost n (compactBlCL' n)

/-- Full cost envelope with actual source stages and a fixed normalization charge. -/
def compactRetunedTime (c extra n : ℕ) : ℕ :=
  compactMainTime compactRetunedDist
    (fun n => compactMainRuns compactRetunedDist compactRetunedCF compactRetunedCO n + extra)
    compactMnT c n

/-- No stage-cost hypotheses remain in the concrete main-time estimate. -/
theorem compactRetunedTime_isBigO (c extra : ℕ) :
    (fun n => (compactRetunedTime c extra n : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - (2 ^ 36 : ℝ)⁻¹) := by
  obtain ⟨Cs, hCs⟩ := compactRetuned_transform_cost_le
  exact compactMain_runs_time_isBigO compactRetunedDist compactRetunedCF compactRetunedCO
    compactMnT c extra hCs

/-- Closing the actual main execution contract suffices for the stronger finite-machine result. -/
theorem compactRetuned_mulInTime_of_exec
    {P U : Type} [Fintype P] [Fintype U] {Q A : ℕ}
    (body : P → Pr P compactMnT Q A U) (pm : P) (v₀ : HS compactMnT Q A U)
    (c extra : ℕ)
    (hexec : ∀ᶠ n in atTop, ∀ x y, (pairEnc (x, y)).length = n →
      HostMulWithin body pm v₀ (compactRetunedTime c extra) x y) :
    MulInTime ((2 ^ 36 : ℝ)⁻¹) := by
  obtain ⟨Cs, hCs⟩ := compactRetuned_transform_cost_le
  exact compactMulInTime_of_main_exec body pm v₀ compactRetunedDist compactRetunedCF
    compactRetunedCO c extra hCs hexec

end
end IntegerMultBounds.MathlibTM2.Fast.Main
