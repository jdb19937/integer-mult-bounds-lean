import IntegerMultBounds.Machine.ChirpPublicConjugation
import IntegerMultBounds.Machine.ChirpFastProduct
import IntegerMultBounds.Machine.ChirpSignExtend
import IntegerMultBounds.Machine.ChirpProductNumerator
import IntegerMultBounds.Machine.ChirpArithmeticCodec
import IntegerMultBounds.Machine.ChirpFastNativeProduct
import IntegerMultBounds.Machine.ChirpScalarProducts
import IntegerMultBounds.Machine.ChirpExactProduct
import IntegerMultBounds.Machine.ChirpTruncate
import IntegerMultBounds.Machine.ChirpNativeTruncate
import Lean.Util.CollectAxioms

/-! Transitive proof-integrity audit for actual chirp tape primitives. -/
open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (name, _) in environment.constants.toList do
    if [`IntegerMultBounds.Machine.ChirpConsumeNumerator,
        `IntegerMultBounds.Machine.ChirpNativeTruncate,
        `IntegerMultBounds.Machine.ChirpUnitOperand,
        `IntegerMultBounds.Machine.ChirpTruncate,
        `IntegerMultBounds.Machine.ChirpMarkProduct,
        `IntegerMultBounds.Machine.ChirpMarkedProducts,
        `IntegerMultBounds.Machine.ChirpExactProduct,
        `IntegerMultBounds.Machine.ChirpScalarProducts,
        `IntegerMultBounds.Machine.InjectivePlacement.replace_set,
        `IntegerMultBounds.Machine.ChirpFastNativeProduct,
        `IntegerMultBounds.Machine.RulerWordMap,
        `IntegerMultBounds.Machine.ChirpArithmeticCodec,
        `IntegerMultBounds.Machine.ChirpProductNumerator,
        `IntegerMultBounds.Machine.FixedMulTruncation,
        `IntegerMultBounds.Machine.ChirpFastProduct,
        `IntegerMultBounds.Machine.ChirpSignExtend,
        `IntegerMultBounds.Machine.ChirpPublicPublished,
        `IntegerMultBounds.Machine.ChirpPublicConjugation,
        `IntegerMultBounds.Machine.GuardedMapCopy,
        `IntegerMultBounds.Machine.ChirpPublicDecode,
        `IntegerMultBounds.Machine.ChirpPublicEmitField,
        `IntegerMultBounds.Machine.ChirpPublicEmitArray,
        `IntegerMultBounds.Machine.ChirpPublicEmitStream,
        `IntegerMultBounds.Machine.InjectivePlacement.replace_eq,
        `IntegerMultBounds.Machine.ChirpHeaderWidth,
        `IntegerMultBounds.Machine.ChirpPublicConjugate,
        `IntegerMultBounds.Machine.RulerMapCopy,
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
