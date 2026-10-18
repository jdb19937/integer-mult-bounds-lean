module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs

/-! The checks of the sixteen stage-7 invocations, evaluated by the kernel one at a time. The
frame check depends only on the stage, so it is evaluated once and shared by all sixteen. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem ext_7 : (List.range 112).all (extCheck 7) = true := by decide +kernel

theorem check_7_0 : callCheck 7 0 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_1 : callCheck 7 1 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_2 : callCheck 7 2 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_3 : callCheck 7 3 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_4 : callCheck 7 4 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_5 : callCheck 7 5 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_6 : callCheck 7 6 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_7 : callCheck 7 7 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_8 : callCheck 7 8 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_9 : callCheck 7 9 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_10 : callCheck 7 10 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_11 : callCheck 7 11 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_12 : callCheck 7 12 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_13 : callCheck 7 13 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_14 : callCheck 7 14 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem check_7_15 : callCheck 7 15 = true := by
  rw [callCheck, ext_7, Bool.and_true]
  decide +kernel

theorem stage7_check : ∀ r < 16, callCheck 7 r = true := by
  intro r hr
  interval_cases r
  exacts [check_7_0, check_7_1, check_7_2, check_7_3, check_7_4, check_7_5, check_7_6, check_7_7, check_7_8, check_7_9, check_7_10, check_7_11, check_7_12, check_7_13, check_7_14, check_7_15]

end IntegerMultBounds.Networks.Certificates.T16.Impl
