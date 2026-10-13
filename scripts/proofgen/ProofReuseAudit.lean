module

import IntegerMultBounds.Machine.RecoverOutputInstall
import IntegerMultBounds.Machine.ElementaryMultiply
import IntegerMultBounds.Schoenhage.ScriptMain
import IntegerMultBounds.Schoenhage.LayoutGenWrap
import IntegerMultBounds.Schoenhage.CertifiedPlacement
import IntegerMultBounds.Schoenhage.TwistCleanupGenerated
import Lean.Util.CollectAxioms

/-! Transitive audit of shared bank/representation lemmas and real callers. -/
open Lean in
run_cmd do
  let environment ← getEnv
  let callers := #[
    `IntegerMultBounds.Machine.putWord_blank_origin,
    `IntegerMultBounds.Machine.ElementaryMultiply.runs_correct,
    `IntegerMultBounds.Machine.RecoverOutputInstall.runs_recovered,
    `IntegerMultBounds.Schoenhage.ScriptMain.upd_update,
    `IntegerMultBounds.Schoenhage.ScriptMain.upd_comp_self,
    `IntegerMultBounds.Schoenhage.ScriptMain.runs_lift,
    `IntegerMultBounds.Schoenhage.LayoutGenWrap.upd_lslot,
    `IntegerMultBounds.Schoenhage.CertifiedSequence.placed_update,
    `IntegerMultBounds.Schoenhage.TwistCleanupGenerated.twistCleanup_bank]
  for caller in callers do
    unless environment.contains caller do
      throwError "Missing reuse caller: {caller}"
  let mut count : Nat := 0
  for (name, _) in environment.constants.toList do
    if (`IntegerMultBounds.Schoenhage.TapeBank).isPrefixOf name || callers.contains name then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  logInfo m!"Shared-lemma audit passed for {count} declarations and all nine named callers."
