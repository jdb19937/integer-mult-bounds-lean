module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCore

/-! Price the executed exceptional-sort term using R1's physical bad-set density. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {K : ℕ}

noncomputable def repairDensityScanCost (p : Par) (X rb R B : ℕ) (scale : ℝ) : ℝ :=
  let k := fieldsLen (selectiveKeyLen p X rb)
  let M := R * 2 ^ fieldsLen (selectiveLen p X)
  ((M * (2 * idxStepCost (badClassifierCost p.wy) (k + B) (selectiveLen p X) +
    6 * (k + B) + 15)) : ℕ) +
    (k : ℝ) * (5 / (128 * scale ^ 3) * (M : ℝ) * ((12 * k + 6 * B + 13) : ℕ)) +
    ((10 * k + 8 * fieldsLen (selectiveLen p X) + 8 * 5 + 18) : ℕ)

theorem repairScanCost_density (p : Par) (X rb R B : ℕ) (hguard : p.G + 1 < p.K)
    (scale : ℝ) (hscale : 0 < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G)) :
    (repairScanCost p X rb R B : ℝ) ≤ repairDensityScanCost p X rb R B scale := by
  have hd := selectiveRepair_sortCost_density p X R (fieldsLen (selectiveKeyLen p X rb)) B
    hguard scale hscale hn hradix hgap
  unfold repairScanCost repairDensityScanCost
  dsimp only
  push_cast at hd ⊢
  linarith

noncomputable def repairDensityCoreCost (p : Par) (X rb R B : ℕ) (scale : ℝ)
    (S : Stacks repairT (prime + K)) : ℝ :=
  selectiveKeyPassCost p X rb (R * 2 ^ fieldsLen (selectiveLen p X)) B +
    ((progW.map (fun o => selectiveOpCost p X repairT R (fieldsLen (selectiveKeyLen p X rb) + B)
      (fun c => ∑ j, (S.R (repairHost.swaps c j)).length) o.1)).sum + 1) +
    repairDensityScanCost p X rb R B scale

theorem repairCoreCost_density (p : Par) (X rb R B : ℕ) (hguard : p.G + 1 < p.K)
    (scale : ℝ) (hscale : 0 < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G))
    (S : Stacks repairT (prime + K)) :
    repairCoreCost p X rb R B S ≤ repairDensityCoreCost p X rb R B scale S := by
  have hd := repairScanCost_density p X rb R B hguard scale hscale hn hradix hgap
  unfold repairCoreCost repairDensityCoreCost
  linarith

end IntegerMultBounds.MathlibTM2.Routing
