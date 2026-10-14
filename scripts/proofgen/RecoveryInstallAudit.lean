module

import IntegerMultBounds.Machine.RecoverOutputInstall
import IntegerMultBounds.Machine.RecoverCoefficientRound
import IntegerMultBounds.Machine.RecoverCarryStep
import IntegerMultBounds.Machine.RecoverMagnitude
import IntegerMultBounds.Machine.RecoverCoefficientStep
import IntegerMultBounds.Machine.RecoverPrecisionSplit
import IntegerMultBounds.Machine.RecoverSignedCoefficient
import Lean.Util.CollectAxioms

/-! Targeted transitive audit for section 8 rounding, carry and installation. -/
open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (name, _) in environment.constants.toList do
    if [`IntegerMultBounds.Machine.RecoverOutputInstall,
        `IntegerMultBounds.Machine.RecoverCoefficientRound,
        `IntegerMultBounds.Machine.RecoverCarryStep,
        `IntegerMultBounds.Machine.RecoverMagnitude,
        `IntegerMultBounds.Machine.RecoverCoefficientStep,
        `IntegerMultBounds.Machine.RecoverPrecisionSplit,
        `IntegerMultBounds.Machine.RecoverSignedCoefficient,
        `IntegerMultBounds.Schoenhage.RecoveryCleanupGenerated,
        `IntegerMultBounds.Schoenhage.CertifiedSequence].any (·.isPrefixOf name) then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  logInfo m!"Recovery rounding, carry and installation axiom audit passed for {count} declarations."
