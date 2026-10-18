module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs

/-! The checks of the sixteen stage-6 invocations, evaluated by the kernel one at a time. The
frame check depends only on the stage, so it is evaluated once and shared by all sixteen. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem ext_6 : (List.range 112).all (extCheck 6) = true := by decide +kernel

theorem check_6_0 : callCheck 6 0 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_1 : callCheck 6 1 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_2 : callCheck 6 2 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_3 : callCheck 6 3 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_4 : callCheck 6 4 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_5 : callCheck 6 5 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_6 : callCheck 6 6 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_7 : callCheck 6 7 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_8 : callCheck 6 8 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_9 : callCheck 6 9 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_10 : callCheck 6 10 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_11 : callCheck 6 11 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_12 : callCheck 6 12 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_13 : callCheck 6 13 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_14 : callCheck 6 14 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem check_6_15 : callCheck 6 15 = true := by
  rw [callCheck, ext_6, Bool.and_true]
  decide +kernel

theorem stage6_check : ∀ r < 16, callCheck 6 r = true := by
  intro r hr
  interval_cases r
  exacts [check_6_0, check_6_1, check_6_2, check_6_3, check_6_4, check_6_5, check_6_6, check_6_7, check_6_8, check_6_9, check_6_10, check_6_11, check_6_12, check_6_13, check_6_14, check_6_15]

end IntegerMultBounds.Networks.Certificates.T16.Impl
