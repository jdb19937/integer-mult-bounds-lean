module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs

/-! The checks of the sixteen stage-4 invocations, evaluated by the kernel one at a time. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem check_4_0 : callCheck 4 0 = true := by decide +kernel

theorem check_4_1 : callCheck 4 1 = true := by decide +kernel

theorem check_4_2 : callCheck 4 2 = true := by decide +kernel

theorem check_4_3 : callCheck 4 3 = true := by decide +kernel

theorem check_4_4 : callCheck 4 4 = true := by decide +kernel

theorem check_4_5 : callCheck 4 5 = true := by decide +kernel

theorem check_4_6 : callCheck 4 6 = true := by decide +kernel

theorem check_4_7 : callCheck 4 7 = true := by decide +kernel

theorem check_4_8 : callCheck 4 8 = true := by decide +kernel

theorem check_4_9 : callCheck 4 9 = true := by decide +kernel

theorem check_4_10 : callCheck 4 10 = true := by decide +kernel

theorem check_4_11 : callCheck 4 11 = true := by decide +kernel

theorem check_4_12 : callCheck 4 12 = true := by decide +kernel

theorem check_4_13 : callCheck 4 13 = true := by decide +kernel

theorem check_4_14 : callCheck 4 14 = true := by decide +kernel

theorem check_4_15 : callCheck 4 15 = true := by decide +kernel

theorem stage4_check : ∀ r < 16, callCheck 4 r = true := by
  intro r hr
  interval_cases r
  exacts [check_4_0, check_4_1, check_4_2, check_4_3, check_4_4, check_4_5, check_4_6, check_4_7, check_4_8, check_4_9, check_4_10, check_4_11, check_4_12, check_4_13, check_4_14, check_4_15]

end IntegerMultBounds.Networks.Certificates.T16.Impl
