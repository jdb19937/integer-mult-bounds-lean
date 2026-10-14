import IntegerMultBounds.Machine.ChirpPublicArray
import Lean.Util.CollectAxioms

/-! Transitive proof-integrity audit for actual chirp tape primitives. -/
open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (name, _) in environment.constants.toList do
    if [`IntegerMultBounds.Machine.RulerMapCopy,
        `IntegerMultBounds.Machine.ChirpPublicCodec,
        `IntegerMultBounds.Machine.ChirpPublicField,
        `IntegerMultBounds.Machine.ChirpPublicPair,
        `IntegerMultBounds.Machine.ChirpPublicArray,
        `IntegerMultBounds.Machine.ChirpConjugateNumerator,
        `IntegerMultBounds.Machine.ChirpConjugateRecord,
        `IntegerMultBounds.Machine.ChirpConjugateArray,
        `IntegerMultBounds.Machine.ChirpConjugateStream].any (·.isPrefixOf name) then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  logInfo m!"Chirp tape axiom audit passed for {count} declarations."
