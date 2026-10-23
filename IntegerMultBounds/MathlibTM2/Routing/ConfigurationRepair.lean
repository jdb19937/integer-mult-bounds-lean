module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveConfigurationEmbedded
public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationInputFrame
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

def configurationRepairPrice {K : ℕ} (scale wb wm wp wk R B Lr Lm : ℕ) (L : Fin 11 → ℕ)
    (S : Stacks repairConfigurationT (prime + K)) : ℝ :=
  let W : Stacks repairConfigurationT (prime + K) := { S with R := repairConfigurationWidthBank rb p.wy S.R }
  let C := embStk (fieldCore (N := repairDescriptorT)) W
  let cfg := repairDescriptorJobs p X hG hK active s L
  let D : Stacks repairDescriptorT (prime + K) := { C with R := descriptorBankGenerated C.R cfg }
  ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * p.wy + 11) + 2 * p.wy + 6) + 1 : ℕ) +
    descriptorBatchCost cfg + exactRepairPrice p X rb scale wb wm wp wk R B (embStk (descriptorCore (J := 11)) D) +
    descriptorEraseCost cfg + (2 * rb + 2 * p.wy + 5 : ℕ)

def configurationRepairProgram {Q K : ℕ} {P U : Type} (Lr Lm : ℕ) (L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr P repairConfigurationT Q (prime + K) U :=
  let cfg := repairDescriptorJobs p X hG hK active s L
  .seq (binaryFieldBatch (repairConfigurationWidthJobs Lr Lm rb p.wy))
    (.seq (embProg (fieldCore (N := repairDescriptorT)) id (.seq (descriptorBatch cfg)
      (.seq (embProg (descriptorCore (J := 11)) id (repairProgram hQ hA)) (metadataClean (cfg.map DescriptorJob.dst)))))
      (metadataClean [repairConfigurationCore (repairSetupSource (.inr .row)), repairConfigurationCore (repairSetupSource (.inr .keyMask))]))

end
end IntegerMultBounds.MathlibTM2.Routing
