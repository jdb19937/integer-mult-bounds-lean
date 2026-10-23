module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactInputFrame
public import IntegerMultBounds.MathlibTM2.Routing.PlacedExactSelective

/-! Named program and price for combined generated-configuration exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def compactConfigurationRepairPrice {K : ℕ} (scale wb wm wp wk R B Lr Lm : ℕ) (Lw Lg L : Fin 11 → ℕ)
    (S : Stacks repairCompactConfigurationT (prime + K)) : ℝ :=
  let W : Stacks repairCompactConfigurationT (prime + K) := { S with R := repairCompactWidthBank rb p.wy S.R }
  let C := embStk (fieldCore (N := repairCompactT)) W
  let cfg := repairCompactJobs p X hG hK active s Lw Lg L
  let D : Stacks repairCompactT (prime + K) := { C with R := compactDescriptorBankGenerated C.R cfg }
  ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * p.wy + 11) + 2 * p.wy + 6) + 1 : ℕ) +
    compactDescriptorBatchCost cfg + exactRepairPrice p X rb scale wb wm wp wk R B (embStk (compactDescriptorCore (J := 11)) D) +
    compactDescriptorEraseCost cfg + (2 * rb + 2 * p.wy + 5 : ℕ)

def compactConfigurationRepairProgram {Q K : ℕ} {P U : Type} (Lr Lm : ℕ) (Lw Lg L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr P repairCompactConfigurationT Q (prime + K) U :=
  let cfg := repairCompactJobs p X hG hK active s Lw Lg L
  .seq (binaryFieldBatch (repairCompactWidthJobs Lr Lm rb p.wy))
    (.seq (embProg (fieldCore (N := repairCompactT)) id (.seq (compactDescriptorBatch cfg)
      (.seq (embProg (compactDescriptorCore (J := 11)) id (repairProgram hQ hA)) (metadataClean (cfg.map CompactDescriptorJob.dst)))))
      (metadataClean [repairCompactConfigurationCore (repairSetupSource (.inr .row)), repairCompactConfigurationCore (repairSetupSource (.inr .keyMask))]))

end
end IntegerMultBounds.MathlibTM2.Routing
