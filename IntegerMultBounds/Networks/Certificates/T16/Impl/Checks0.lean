module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallChecks

/-! The checks of the sixteen stage-0 invocations, evaluated by the kernel one at a time. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem check_0_0 : callCheck 0 0 = true := by decide +kernel

theorem check_0_1 : callCheck 0 1 = true := by decide +kernel

theorem check_0_2 : callCheck 0 2 = true := by decide +kernel

theorem check_0_3 : callCheck 0 3 = true := by decide +kernel

theorem check_0_4 : callCheck 0 4 = true := by decide +kernel

theorem check_0_5 : callCheck 0 5 = true := by decide +kernel

theorem check_0_6 : callCheck 0 6 = true := by decide +kernel

theorem check_0_7 : callCheck 0 7 = true := by decide +kernel

theorem check_0_8 : callCheck 0 8 = true := by decide +kernel

theorem check_0_9 : callCheck 0 9 = true := by decide +kernel

theorem check_0_10 : callCheck 0 10 = true := by decide +kernel

theorem check_0_11 : callCheck 0 11 = true := by decide +kernel

theorem check_0_12 : callCheck 0 12 = true := by decide +kernel

theorem check_0_13 : callCheck 0 13 = true := by decide +kernel

theorem check_0_14 : callCheck 0 14 = true := by decide +kernel

theorem check_0_15 : callCheck 0 15 = true := by decide +kernel

theorem stage0_check : ∀ r < 16, callCheck 0 r = true := by
  intro r hr
  interval_cases r
  exacts [check_0_0, check_0_1, check_0_2, check_0_3, check_0_4, check_0_5, check_0_6, check_0_7, check_0_8, check_0_9, check_0_10, check_0_11, check_0_12, check_0_13, check_0_14, check_0_15]

end IntegerMultBounds.Networks.Certificates.T16.Impl
