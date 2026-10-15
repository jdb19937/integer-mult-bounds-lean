import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateSetup
import IntegerMultBounds.MathlibTM2.Cost.CRTControlGenerate
import IntegerMultBounds.MathlibTM2.Fast.CRTControlDriverSpec
import IntegerMultBounds.MathlibTM2.Fast.CRTControlExposeRotation
import IntegerMultBounds.MathlibTM2.Fast.CRTControlAllWorkspace
import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateLayout
import IntegerMultBounds.MathlibTM2.Fast.CRTControlRotation
import IntegerMultBounds.MathlibTM2.Fast.CRTControlSetup
import IntegerMultBounds.MathlibTM2.Cost.CRTControlAllFibers
import IntegerMultBounds.MathlibTM2.Fast.CRTControlPass
import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerate
import IntegerMultBounds.MathlibTM2.Fast.CRTControlLoop
import IntegerMultBounds.MathlibTM2.Fast.CRTControlReset
import IntegerMultBounds.MathlibTM2.Cost.CRTControlOffset
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
Includes the complete all-fiber rotation and its semantic specialization,
workspace restoration and distant exposure. Runtime descriptor production and
complete driver/multiplier integration remain separate work. -/

open Lean in
run_cmd do
  let names := #[
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlUnaryWord_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlPadding_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlPrefixWidth_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlParameters_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlParametersClear_runs,
    ``IntegerMultBounds.MathlibTM2.Cost.crtControlParameters_pipeline_le,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlReadUnary_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlGenerateAxis_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlBankPow2_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlGenerateInit_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlGenerateSetup_runs,
    ``IntegerMultBounds.MathlibTM2.Cost.crtControlGenerateAxisCost_le,
    ``IntegerMultBounds.MathlibTM2.Cost.crtControlGenerateAxes_pipeline_le,
    ``IntegerMultBounds.MathlibTM2.Cost.crtControlGenerateSetup_pipeline_le,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlExposeRotation_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlRot_zero,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlDriver_forward,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlDriver_inverse,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlDriver_records,
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
    ``IntegerMultBounds.MathlibTM2.Cost.crtControlScanCost_pipeline_le,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlOffsets_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlUnary10Clear_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlConstants_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlFiber_shift_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlRotate_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlPass_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlPassReset_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlReset_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlBegin_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlIndexedLoop_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlIndexedFull_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlEmitPacket_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlPow2_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlGeneratePacket_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlGeneratedField_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlAdvanceWeight_runs,
    ``IntegerMultBounds.MathlibTM2.Cost.crtControlOffsetUnaryCost_pipeline_le,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlAllBody_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlAllFibers_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlAllFibersWorkspace_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlRotation_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlWorkspaceInit_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlWorkspace_restore,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlWidthSetup_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlWidthClear_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlGeneratedFields_full,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlGeneratedFields_zero_target,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlGeneratedField_eq_axisField,
    ``IntegerMultBounds.MathlibTM2.Fast.crtControlRotationWorkspace_runs,
    ``IntegerMultBounds.MathlibTM2.Cost.crtControlAllWorkspace_pipeline_le,
    ``IntegerMultBounds.MathlibTM2.Cost.crtControlAllFibersCost_pipeline_le]
  for name in names do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo m!"CRT control axiom audit passed for {names.size} contracts."
