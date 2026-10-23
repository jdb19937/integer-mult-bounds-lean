module

public import IntegerMultBounds.MathlibTM2.Routing.CompactConfigurationRepair
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactClassifiers

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

def compactClassifierRepairPrice {K : ℕ} (scale wb wm wp wk R B Lr Lm LK Ln Lo Lt : ℕ)
    (Lw Lg L : Fin 11 → ℕ) (S : Stacks repairCompactClassifierT (prime + K)) : ℝ :=
  let C := embStk classifierCore S
  let M : Stacks repairCompactConfigurationT (prime + K) := { C with R := repairCompactConfigurationClassifierBank p C.R }
  (binaryTemporaryMaskCost p LK Ln Lo Lt + binaryPhaseMaskCost p LK Ln Lo Lt : ℕ) +
    compactConfigurationRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lr Lm Lw Lg L M +
    (4 * (p.wy + 1) + 5 : ℕ)

def compactClassifierRepairProgram {Q K : ℕ} {P U : Type} (Lr Lm : ℕ) (Lw Lg L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr P repairCompactClassifierT Q (prime + K) U :=
  .seq (classifierPairProgram classifierBankReg
    (classifierBankRepeat repairCompactClassifierTemporary repairCompactClassifierPhase) classifierBankPad)
    (.seq (embProg classifierCore id (compactConfigurationRepairProgram p X rb hG hK active s Lr Lm Lw Lg L hQ hA))
      (metadataClean [classifierCore repairCompactClassifierTemporary, classifierCore repairCompactClassifierPhase]))

end
end IntegerMultBounds.MathlibTM2.Routing
