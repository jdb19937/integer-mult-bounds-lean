module

public import IntegerMultBounds.Schoenhage.LayoutSequenceGenerated
import Lean.Util.CollectAxioms

/-! Independent manual baseline, regression checks and transitive axiom audit
for the sequence-generator pilot. This does not close a section 6 milestone. -/

@[expose] public section
namespace IntegerMultBounds.Schoenhage.LayoutSequencePilot
open Machine LayoutGenRun LayoutSequenceGenerated

/-- Manual baseline: the first two layout setup phases and their paid join. -/
theorem manual_constants_copies (ell chunk width axisCount : ℕ) (flags : List Bool) :
    Runs (.seq constsA (.seq copyFlags (.seq copyTicks lm1Calc)))
      (lstart ell chunk width axisCount flags) (· = stB ell chunk width axisCount flags)
      (40 + 1 + (13 * flags.length + 10 * axisCount + 4 * ell + 60)) :=
  Runs.then (runs_constsA ell chunk width axisCount flags)
    (runs_copies ell chunk width axisCount flags)

/-- The generated bound is exactly the manually accounted bound. -/
theorem baseline_cost (ell chunk width axisCount : ℕ) (flags : List Bool)
    (chunkPositive : 0 < chunk) (widthPositive : 0 < width) :
    constantsCopiesCost ell chunk width axisCount flags chunkPositive widthPositive =
      40 + 1 + (13 * flags.length + 10 * axisCount + 4 * ell + 60) := rfl

/-- The six-phase pilot is the actual layout setup prefix, independent of data. -/
theorem setup_program : descriptorSetupProgram =
    .seq constsA (.seq (.seq copyFlags (.seq copyTicks lm1Calc))
      (.seq nPhase (.seq divPhase (.seq binPhase arrPhase)))) := rfl

end IntegerMultBounds.Schoenhage.LayoutSequencePilot

open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (name, _) in environment.constants.toList do
    if [`IntegerMultBounds.Schoenhage.CertifiedSequence,
        `IntegerMultBounds.Schoenhage.LayoutSequenceGenerated,
        `IntegerMultBounds.Schoenhage.LayoutSequencePilot].any (·.isPrefixOf name) then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  logInfo m!"Sequence pilot axiom audit passed for {count} declarations."
