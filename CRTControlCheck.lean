import IntegerMultBounds.MathlibTM2.Fast.CRTControlScanner
import IntegerMultBounds.MathlibTM2.Fast.CRTControlOffset
import IntegerMultBounds.MathlibTM2.Fast.CRTLinear
import IntegerMultBounds.MathlibTM2.Cost.CRTControlScan
import IntegerMultBounds.MathlibTM2.Fast.CRTControlTape
import IntegerMultBounds.MathlibTM2.Fast.CRTControlBounds
import IntegerMultBounds.MathlibTM2.Fast.CRTSchedule
import IntegerMultBounds.MathlibTM2.Cost.CRTControl
import Lean.Util.CollectAxioms

/-! Audit the replacement CRT control semantics and arithmetic kernels.
Includes the concrete runtime descriptor scanner, offset conversion and distant
exposure; the outer rotation loop and multiplier integration remain separate work. -/

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
    ``IntegerMultBounds.MathlibTM2.Cost.crtControl_polynomial_pipeline_le,
    ``IntegerMultBounds.MathlibTM2.Fast.crtRuns_of_tbl,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlConsume_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlLoad_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlState_consume,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlScan_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlScan_result,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlPacket_concrete,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlScanner_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlScanner_exact_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlScanner_width_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlOffsetHost_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlOffsetRho_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlOffsetClear_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtGapSwapStep_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtExposeStep_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtUnexposeStep_runs,
    ``IntegerMultBounds.MathlibTM2.Cost.crtControlScanCost_pipeline_le]
  for name in names do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo m!"CRT control axiom audit passed for {names.size} contracts."
