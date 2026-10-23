module

public import IntegerMultBounds.MathlibTM2.Routing.CompactClassifierRepair
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactHeadersClean

/-! Complete header-generating repair program and its charged cost, reusable
when the repair is embedded between placement and inverse placement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def compactHeaderRepairPrice {K : ℕ} (scale wb wm wp wk R B Lr Lm LK Ln Lo Lt Lrow Lwidth : ℕ)
    (Lw Lg L : Fin 11 → ℕ) (H : Stacks repairCompactHeaderT (prime + K)) : ℝ :=
  let G : Stacks repairCompactHeaderT (prime + K) := { H with R := repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank H.R }
  let C := embStk sharedHeaderCore G
  (2 * (14 * (p.wc + p.wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
    compactClassifierRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt Lw Lg L C +
    (repairHeaderErasePrice p X rb R B : ℕ)

def compactHeaderRepairProgram {Q K : ℕ} {P U : Type} (Lr Lm : ℕ) (Lw Lg L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr P repairCompactHeaderT Q (prime + K) U :=
  .seq (binaryRepairHeaderPairProgram sharedHeaderBinary repairCompactSharedHeaderBank)
    (.seq (embProg sharedHeaderCore id (compactClassifierRepairProgram p X rb hG hK active s Lr Lm Lw Lg L hQ hA))
      (metadataClean repairCompactGeneratedHeaderTargets))

end
end IntegerMultBounds.MathlibTM2.Routing
