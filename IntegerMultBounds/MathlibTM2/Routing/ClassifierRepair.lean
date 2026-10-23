module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationRepair
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveClassifiersEmbedded

/-! Named complete program and price for classifier-generated exact repair.
Generation and erasure are charged around the existing configuration program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def classifierRepairPrice {K : ℕ} (scale wb wm wp wk R B Lr Lm LK Ln Lo Lt : ℕ)
    (L : Fin 11 → ℕ) (S : Stacks repairClassifierT (prime + K)) : ℝ :=
  let C := embStk classifierCore S
  let M : Stacks repairConfigurationT (prime + K) := { C with R := repairConfigurationClassifierBank p C.R }
  (binaryTemporaryMaskCost p LK Ln Lo Lt + binaryPhaseMaskCost p LK Ln Lo Lt : ℕ) +
    configurationRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lr Lm L M +
    (4 * (p.wy + 1) + 5 : ℕ)

def classifierRepairProgram {Q K : ℕ} {P U : Type} (Lr Lm : ℕ) (L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr P repairClassifierT Q (prime + K) U :=
  .seq (classifierPairProgram classifierBankReg
    (classifierBankRepeat repairClassifierTemporary repairClassifierPhase) classifierBankPad)
    (.seq (embProg classifierCore id (configurationRepairProgram p X rb hG hK active s Lr Lm L hQ hA))
      (metadataClean [classifierCore repairClassifierTemporary, classifierCore repairClassifierPhase]))

end
end IntegerMultBounds.MathlibTM2.Routing
