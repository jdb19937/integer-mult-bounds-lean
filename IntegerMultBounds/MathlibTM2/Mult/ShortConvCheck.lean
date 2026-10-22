module

import IntegerMultBounds.MathlibTM2.Mult.ShortConvUnary
import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchProgram
import IntegerMultBounds.MathlibTM2.Mult.ChirpRing
import Lean.Util.CollectAxioms

/-! Standalone integrity audit of the shared convolution, outside the root imports. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.program_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.program_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpAR_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpAR_approx

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.withHeader_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.withHeader_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.fromUnary_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.fromUnary_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.batchProgram_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.batchProgram_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Short-convolution axiom audit passed."
