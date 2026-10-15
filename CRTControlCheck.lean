import IntegerMultBounds.MathlibTM2.Fast.CRTControlTape
import IntegerMultBounds.MathlibTM2.Fast.CRTControlBounds
import IntegerMultBounds.MathlibTM2.Fast.CRTSchedule
import IntegerMultBounds.MathlibTM2.Cost.CRTControl
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
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlStep_host,
    ``IntegerMultBounds.MathlibTM2.Fast.crtReadWord_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtLoadControl_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlTape_restore,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlTape_eq_nil,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlConsume_do,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlConsumeState_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlFields_fit,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlValue_lt_pow,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControl_accumulate_le,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlStep_descriptor_bounded,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControl_offset_mul_lt,
    ``IntegerMultBounds.MathlibTM2.Fast.crtExpose_controlValue,
    ``IntegerMultBounds.MathlibTM2.Fast.crtLinear_route,
    ``IntegerMultBounds.MathlibTM2.Fast.crtLinear_inverse_route,
    ``IntegerMultBounds.MathlibTM2.Fast.crtSchedule_swap_count,
    ``IntegerMultBounds.MathlibTM2.Cost.crtControl_polynomial_pipeline_le]
  for name in names do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo m!"CRT control axiom audit passed for {names.size} contracts."
