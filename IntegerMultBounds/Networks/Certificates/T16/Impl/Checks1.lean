module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallChecks

/-! The checks of the sixteen stage-1 invocations, evaluated by the kernel one at a time. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem check_1_0 : callCheck 1 0 = true := by decide +kernel

theorem check_1_1 : callCheck 1 1 = true := by decide +kernel

theorem check_1_2 : callCheck 1 2 = true := by decide +kernel

theorem check_1_3 : callCheck 1 3 = true := by decide +kernel

theorem check_1_4 : callCheck 1 4 = true := by decide +kernel

theorem check_1_5 : callCheck 1 5 = true := by decide +kernel

theorem check_1_6 : callCheck 1 6 = true := by decide +kernel

theorem check_1_7 : callCheck 1 7 = true := by decide +kernel

theorem check_1_8 : callCheck 1 8 = true := by decide +kernel

theorem check_1_9 : callCheck 1 9 = true := by decide +kernel

theorem check_1_10 : callCheck 1 10 = true := by decide +kernel

theorem check_1_11 : callCheck 1 11 = true := by decide +kernel

theorem check_1_12 : callCheck 1 12 = true := by decide +kernel

theorem check_1_13 : callCheck 1 13 = true := by decide +kernel

theorem check_1_14 : callCheck 1 14 = true := by decide +kernel

theorem check_1_15 : callCheck 1 15 = true := by decide +kernel

theorem stage1_check : ∀ r < 16, callCheck 1 r = true := by
  intro r hr
  interval_cases r
  exacts [check_1_0, check_1_1, check_1_2, check_1_3, check_1_4, check_1_5, check_1_6, check_1_7, check_1_8, check_1_9, check_1_10, check_1_11, check_1_12, check_1_13, check_1_14, check_1_15]

end IntegerMultBounds.Networks.Certificates.T16.Impl
