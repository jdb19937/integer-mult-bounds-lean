module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs

/-! The checks of the sixteen stage-3 invocations, evaluated by the kernel one at a time. The
frame check depends only on the stage, so it is evaluated once and shared by all sixteen. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem ext_3 : (List.range 112).all (extCheck 3) = true := by decide +kernel

theorem check_3_0 : callCheck 3 0 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_1 : callCheck 3 1 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_2 : callCheck 3 2 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_3 : callCheck 3 3 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_4 : callCheck 3 4 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_5 : callCheck 3 5 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_6 : callCheck 3 6 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_7 : callCheck 3 7 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_8 : callCheck 3 8 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_9 : callCheck 3 9 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_10 : callCheck 3 10 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_11 : callCheck 3 11 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_12 : callCheck 3 12 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_13 : callCheck 3 13 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_14 : callCheck 3 14 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem check_3_15 : callCheck 3 15 = true := by
  rw [callCheck, ext_3, Bool.and_true]
  decide +kernel

theorem stage3_check : ∀ r < 16, callCheck 3 r = true := by
  intro r hr
  interval_cases r
  exacts [check_3_0, check_3_1, check_3_2, check_3_3, check_3_4, check_3_5, check_3_6, check_3_7, check_3_8, check_3_9, check_3_10, check_3_11, check_3_12, check_3_13, check_3_14, check_3_15]

end IntegerMultBounds.Networks.Certificates.T16.Impl
