module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs

/-! The checks of the sixteen stage-2 invocations, evaluated by the kernel one at a time. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem check_2_0 : callCheck 2 0 = true := by decide +kernel

theorem check_2_1 : callCheck 2 1 = true := by decide +kernel

theorem check_2_2 : callCheck 2 2 = true := by decide +kernel

theorem check_2_3 : callCheck 2 3 = true := by decide +kernel

theorem check_2_4 : callCheck 2 4 = true := by decide +kernel

theorem check_2_5 : callCheck 2 5 = true := by decide +kernel

theorem check_2_6 : callCheck 2 6 = true := by decide +kernel

theorem check_2_7 : callCheck 2 7 = true := by decide +kernel

theorem check_2_8 : callCheck 2 8 = true := by decide +kernel

theorem check_2_9 : callCheck 2 9 = true := by decide +kernel

theorem check_2_10 : callCheck 2 10 = true := by decide +kernel

theorem check_2_11 : callCheck 2 11 = true := by decide +kernel

theorem check_2_12 : callCheck 2 12 = true := by decide +kernel

theorem check_2_13 : callCheck 2 13 = true := by decide +kernel

theorem check_2_14 : callCheck 2 14 = true := by decide +kernel

theorem check_2_15 : callCheck 2 15 = true := by decide +kernel

theorem stage2_check : ∀ r < 16, callCheck 2 r = true := by
  intro r hr
  interval_cases r
  exacts [check_2_0, check_2_1, check_2_2, check_2_3, check_2_4, check_2_5, check_2_6, check_2_7, check_2_8, check_2_9, check_2_10, check_2_11, check_2_12, check_2_13, check_2_14, check_2_15]

end IntegerMultBounds.Networks.Certificates.T16.Impl
