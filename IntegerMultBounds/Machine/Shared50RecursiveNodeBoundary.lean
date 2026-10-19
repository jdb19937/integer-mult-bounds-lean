module

public import IntegerMultBounds.Machine.Shared50RecursiveNodeBinary

/-! Actual fixed Shared50 node entry/exit contracts on the binary World bank.
All header and movement work is charged; the saved descriptor stack supports
nested calls through its preserved blank suffix. -/

@[expose] public section

namespace IntegerMultBounds.Machine.Shared50RecursiveNodeBoundary
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount)
open RecursiveInterchangeLayout (Descriptor volume role)
open Shared50RecursiveNodeLayout (wires entry exit)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeBinary (splitWorld networkWorld)
open RecursiveViewFrameRoleBank (bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
variable {u : ℕ} {v : Descriptor}

end
end IntegerMultBounds.Machine.Shared50RecursiveNodeBoundary
