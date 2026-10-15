import IntegerMultBounds.MathlibTM2.Fast.CRTGap
import Lean.Util.CollectAxioms

/-! Focused integrity audit for M2's distant CRT interchange contracts.
This checks the new bridge; it does not assert a faster multiplication theorem. -/

open Lean in
run_cmd do
  let names := #[
    ``IntegerMultBounds.MathlibTM2.Fast.crtSwapGapList,
    ``IntegerMultBounds.MathlibTM2.Fast.crtSwapGapBox,
    ``IntegerMultBounds.MathlibTM2.Fast.crtSwapGapBoxBits,
    ``IntegerMultBounds.MathlibTM2.Fast.crtGapHeaderP_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtGapHdrBits_canonical,
    ``IntegerMultBounds.MathlibTM2.Fast.crtGapHdrBits_value,
    ``IntegerMultBounds.MathlibTM2.Fast.crtSwapGapPass_runs]
  for name in names do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo m!"CRT distant-swap axiom audit passed for {names.size} contracts."
