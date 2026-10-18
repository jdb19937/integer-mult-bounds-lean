module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs

/-! The checks of the sixteen stage-8 invocations, evaluated by the kernel one at a time. The
frame check depends only on the stage, so it is evaluated once and shared by all sixteen. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem ext_8 : (List.range 112).all (extCheck 8) = true := by decide +kernel

theorem check_8_0 : callCheck 8 0 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_1 : callCheck 8 1 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_2 : callCheck 8 2 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_3 : callCheck 8 3 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_4 : callCheck 8 4 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_5 : callCheck 8 5 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_6 : callCheck 8 6 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_7 : callCheck 8 7 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_8 : callCheck 8 8 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_9 : callCheck 8 9 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_10 : callCheck 8 10 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_11 : callCheck 8 11 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_12 : callCheck 8 12 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_13 : callCheck 8 13 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_14 : callCheck 8 14 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem check_8_15 : callCheck 8 15 = true := by
  rw [callCheck, ext_8, Bool.and_true]
  decide +kernel

theorem stage8_check : ∀ r < 16, callCheck 8 r = true := by
  intro r hr
  interval_cases r
  exacts [check_8_0, check_8_1, check_8_2, check_8_3, check_8_4, check_8_5, check_8_6, check_8_7, check_8_8, check_8_9, check_8_10, check_8_11, check_8_12, check_8_13, check_8_14, check_8_15]

end IntegerMultBounds.Networks.Certificates.T16.Impl
