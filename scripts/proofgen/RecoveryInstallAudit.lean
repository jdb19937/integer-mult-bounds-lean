module

import IntegerMultBounds.Machine.RecoverOutputInstall
import IntegerMultBounds.Machine.RecoverCoefficientRound
import IntegerMultBounds.Machine.RecoverCarryStep
import IntegerMultBounds.Machine.RecoverMagnitude
import IntegerMultBounds.Machine.RecoverCoefficientStep
import IntegerMultBounds.Machine.RecoverPrecisionSplit
import IntegerMultBounds.Machine.RecoverSignedCoefficient
import IntegerMultBounds.Machine.RecoverWorkspace
import IntegerMultBounds.Machine.RecoverIterationFinish
import IntegerMultBounds.Machine.RecoverIteration
import IntegerMultBounds.Machine.RecoverLoad
import IntegerMultBounds.Machine.RecoverArray
import IntegerMultBounds.Machine.RecoverOutputSerialize
import IntegerMultBounds.Machine.RecoverArrayCleanup
import IntegerMultBounds.Machine.RecoverCarryFlush
import IntegerMultBounds.Machine.RecoverOutput
import IntegerMultBounds.Machine.RecoverNumericalBridge
import IntegerMultBounds.Machine.RulerReverseCopy
import IntegerMultBounds.Machine.RecoverRecordFormat
import IntegerMultBounds.Machine.RecoverRecordField
import IntegerMultBounds.Machine.RecoverRecordArray
import IntegerMultBounds.Machine.RecoverRecordReady
import IntegerMultBounds.Machine.RecoverPublicOutput
import IntegerMultBounds.Machine.RecoverBinaryRuler
import IntegerMultBounds.Machine.RecoverControlSetup
import IntegerMultBounds.Machine.RecoverBinaryOutput
import IntegerMultBounds.Machine.GammaPrefix
import IntegerMultBounds.Machine.GammaRead
import IntegerMultBounds.Machine.RawMsbDescriptor
import IntegerMultBounds.Machine.GammaDescriptorRead
import IntegerMultBounds.Machine.GammaHeaderRead
import IntegerMultBounds.Machine.RecoverChunkParameter
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
        `IntegerMultBounds.Machine.RecoverWorkspace,
        `IntegerMultBounds.Machine.RecoverIterationFinish,
        `IntegerMultBounds.Machine.RecoverIteration,
        `IntegerMultBounds.Machine.RecoverLoad,
        `IntegerMultBounds.Machine.RecoverArray,
        `IntegerMultBounds.Machine.RecoverOutputSerialize,
        `IntegerMultBounds.Machine.RecoverArrayCleanup,
        `IntegerMultBounds.Machine.RecoverCarryFlush,
        `IntegerMultBounds.Machine.RecoverOutput,
        `IntegerMultBounds.Machine.RecoverNumericalBridge,
        `IntegerMultBounds.Machine.RulerReverseCopy,
        `IntegerMultBounds.Machine.RecoverRecordFormat,
        `IntegerMultBounds.Machine.RecoverRecordField,
        `IntegerMultBounds.Machine.RecoverRecordArray,
        `IntegerMultBounds.Machine.RecoverRecordReady,
        `IntegerMultBounds.Machine.RecoverPublicOutput,
        `IntegerMultBounds.Machine.RecoverBinaryRuler,
        `IntegerMultBounds.Machine.RecoverControlSetup,
        `IntegerMultBounds.Machine.RecoverBinaryOutput,
        `IntegerMultBounds.Machine.GammaPrefix,
        `IntegerMultBounds.Machine.GammaRead,
        `IntegerMultBounds.Machine.RawMsbDescriptor,
        `IntegerMultBounds.Machine.GammaDescriptorRead,
        `IntegerMultBounds.Machine.GammaHeaderRead,
        `IntegerMultBounds.Machine.RecoverChunkParameter,
        `IntegerMultBounds.ExactRecovery,
        `IntegerMultBounds.NLogN.recover_coefficient_error,
        `IntegerMultBounds.NLogN.recover_coefficient_real_error,
        `IntegerMultBounds.Schoenhage.RecoveryCleanupGenerated,
        `IntegerMultBounds.Schoenhage.CertifiedSequence].any (·.isPrefixOf name) then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  logInfo m!"Recovery rounding, carry and installation axiom audit passed for {count} declarations."
