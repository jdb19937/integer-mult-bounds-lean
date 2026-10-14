module

public import IntegerMultBounds.Machine.LayerGuardedInput

@[expose] public section
namespace IntegerMultBounds.Machine.LayerPolynomialPaddingHeaders
noncomputable section
open ActiveRepairRankHeadersCommands (State put)
open LayerReservationHeaders (command product)
variable {alphabet : ℕ}

def span (coefficientCount width : ℕ) := 2*coefficientCount*(width+1)
def deficit (coefficientCount : ℕ) := LayerPolynomialHeaders.paddedCount coefficientCount-coefficientCount
def schedule : List CompactGlobalRowHeaderOps.Op := [
  .constant 1 27, command (.copy 13 25 (by decide)), command (.add 25 27 (by decide)), command (.erase 27),
  .constant 2 27, product ![2,25,26] (by decide), command (.erase 25),
  product ![27,26,25] (by decide), command (.erase 26), command (.erase 27),
  command (.difference 24 2 26 (by decide))]

def output (original : State) (coefficientCount width : ℕ) :=
  put (put original 25 (span coefficientCount width)) 26 (deficit coefficientCount)
def core := (CompactGlobalRowHeaderOps.compile (a := alphabet) schedule).2

theorem executes (original : State) (coefficientCount width : ℕ)
    (countReady : original 2 = some coefficientCount) (widthReady : original 13 = some width)
    (paddedReady : original 24 = some (LayerPolynomialHeaders.paddedCount coefficientCount))
    (scratchBlank : original 27 = none) :
    CompactGlobalRowHeaderOps.execute schedule original = output original coefficientCount width := by
  funext slot
  fin_cases slot
  all_goals simp [schedule, CompactGlobalRowHeaderOps.execute, CompactGlobalRowHeaderOps.eval,
    ActivePrefixStageHeadersOps.eval, ActiveRepairRankHeadersCommands.eval, put, output,
    span, deficit, countReady, widthReady, paddedReady, scratchBlank, Function.update]
  all_goals ring

theorem valid (original : State) (coefficientCount width : ℕ) (countPositive : 0 < coefficientCount)
    (countReady : original 2 = some coefficientCount) (widthReady : original 13 = some width)
    (paddedReady : original 24 = some (LayerPolynomialHeaders.paddedCount coefficientCount))
    (spanBlank : original 25 = none) (deficitBlank : original 26 = none) (scratchBlank : original 27 = none) :
    CompactGlobalRowHeaderOps.validSchedule schedule original := by
  have paddingFits := (LayerPolynomialHeaders.padded_bounds coefficientCount countPositive).1
  simp [schedule, CompactGlobalRowHeaderOps.validSchedule, CompactGlobalRowHeaderOps.valid, CompactGlobalRowHeaderOps.eval,
    ActivePrefixStageHeadersOps.valid, ActivePrefixStageHeadersOps.eval, ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval, put, countReady, widthReady, paddedReady, spanBlank, deficitBlank, scratchBlank,
    Function.update, countPositive, paddingFits]

theorem runs (original : State) (coefficientCount width : ℕ) (countPositive : 0 < coefficientCount)
    (countReady : original 2 = some coefficientCount) (widthReady : original 13 = some width)
    (paddedReady : original 24 = some (LayerPolynomialHeaders.paddedCount coefficientCount))
    (spanBlank : original 25 = none) (deficitBlank : original 26 = none) (scratchBlank : original 27 = none) :
    HoareTime (core (alphabet := alphabet)) (· = ActiveRepairRankHeadersCommands.bank original)
      (· = ActiveRepairRankHeadersCommands.bank (output original coefficientCount width))
      (CompactGlobalRowHeaderOps.scheduleCost schedule original) := by
  have execution := CompactGlobalRowHeaderOps.schedule_runs (a := alphabet) schedule original
    (valid original coefficientCount width countPositive countReady widthReady paddedReady spanBlank deficitBlank scratchBlank)
  rwa [executes original coefficientCount width countReady widthReady paddedReady scratchBlank] at execution

end
end IntegerMultBounds.Machine.LayerPolynomialPaddingHeaders
