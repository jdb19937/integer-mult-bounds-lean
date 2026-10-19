module

-- S6 supplier seam
public import IntegerMultBounds.Machine.BinaryRadixEqualShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInterchangeRun

/-!
# The rectangular interchange of the cost chain

The cost chain uses the supplier's width-selecting rectangular interchange under these names.
The supplier is the M8 machine on the PR97 node (`M8.Global.pr97`).
-/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryInterchangeRun

export IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInterchangeRun (values shortWords shortFocus prefixSlot middle bankInput input bankCount slot flag slot_injective slot_ne_flag input_cells flag_cells equalProgram longHProgram longDProgram program cost equal_runs longH_runs longD_runs runs)

end IntegerMultBounds.Machine.BinaryInterchangeRun
