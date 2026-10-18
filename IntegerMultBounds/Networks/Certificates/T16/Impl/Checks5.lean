module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs

/-! The checks of the sixteen stage-5 invocations, evaluated by the kernel one at a time. The
frame check depends only on the stage, so it is evaluated once and shared by all sixteen. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem ext_5 : (List.range 112).all (extCheck 5) = true := by decide +kernel

theorem check_5_0 : callCheck 5 0 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_1 : callCheck 5 1 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_2 : callCheck 5 2 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_3 : callCheck 5 3 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_4 : callCheck 5 4 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_5 : callCheck 5 5 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_6 : callCheck 5 6 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_7 : callCheck 5 7 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_8 : callCheck 5 8 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_9 : callCheck 5 9 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_10 : callCheck 5 10 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_11 : callCheck 5 11 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_12 : callCheck 5 12 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_13 : callCheck 5 13 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_14 : callCheck 5 14 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem check_5_15 : callCheck 5 15 = true := by
  rw [callCheck, ext_5, Bool.and_true]
  decide +kernel

theorem stage5_check : ∀ r < 16, callCheck 5 r = true := by
  intro r hr
  interval_cases r
  exacts [check_5_0, check_5_1, check_5_2, check_5_3, check_5_4, check_5_5, check_5_6, check_5_7, check_5_8, check_5_9, check_5_10, check_5_11, check_5_12, check_5_13, check_5_14, check_5_15]

end IntegerMultBounds.Networks.Certificates.T16.Impl
