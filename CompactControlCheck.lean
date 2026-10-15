import IntegerMultBounds.MathlibTM2.Cost.CompactSwap
import IntegerMultBounds.MathlibTM2.Node.CompactRotParity
import Lean.Util.CollectAxioms

/-! Focused integrity audit for the compact-control host primitives.
These are prepared execution contracts, not an improved layer or multiplier theorem. -/

open Lean in
run_cmd do
  let names := #[
    ``IntegerMultBounds.MathlibTM2.Node.compactSwap_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactParityPack_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactParityWord_binSyms,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSwapCost_le_volume]
  for name in names do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo m!"Compact-control host axiom audit passed for {names.size} contracts."
