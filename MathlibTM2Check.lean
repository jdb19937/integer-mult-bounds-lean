module

import IntegerMultBounds.MathlibTM2

/-! The audited declarations depend only on Lean's three standard axioms. -/

/-- info: 'IntegerMultBounds.MathlibTM2.mul_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IntegerMultBounds.MathlibTM2.mul_quadratic

/-- info: 'IntegerMultBounds.MathlibTM2.statement_of_endToEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IntegerMultBounds.MathlibTM2.statement_of_endToEnd

/-- info: 'IntegerMultBounds.MathlibTM2.tm2_of_runsWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IntegerMultBounds.MathlibTM2.tm2_of_runsWithin

/-- info: 'IntegerMultBounds.MathlibTM2.mulInTime_of_computesWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IntegerMultBounds.MathlibTM2.mulInTime_of_computesWithin
