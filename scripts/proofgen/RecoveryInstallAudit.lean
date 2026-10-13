module

import IntegerMultBounds.Machine.RecoverOutputInstall
import Lean.Util.CollectAxioms

/-! Targeted transitive audit for the production section 8 installation path. -/
open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (name, _) in environment.constants.toList do
    if [`IntegerMultBounds.Machine.RecoverOutputInstall,
        `IntegerMultBounds.Schoenhage.RecoveryCleanupGenerated,
        `IntegerMultBounds.Schoenhage.CertifiedSequence].any (·.isPrefixOf name) then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  logInfo m!"Recovery installation axiom audit passed for {count} declarations."
