import IntegerMultBounds.MathlibTM2.Fast.CRTControlProg
import Lean.Util.CollectAxioms

/-! Audit the replacement CRT control semantics and arithmetic kernels.
The descriptor-tape loop and multiplier integration are still separate work. -/

open Lean in
run_cmd do
  let names := #[
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlValue_eq_crtKI,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlValid_eq_controls,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlShift_mod,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlRot_fiber,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlRotOut_top,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlStep_do,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlStepState_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlStep_descriptor,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlOffset_do,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlStep_host]
  for name in names do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo m!"CRT control axiom audit passed for {names.size} contracts."
