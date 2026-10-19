module

public import IntegerMultBounds.MathlibTM2.M8.Machine.BankNodes
public import IntegerMultBounds.MathlibTM2.M8.Machine.Control
public import IntegerMultBounds.Machine.RecursiveDigitRoleBank
public import IntegerMultBounds.Machine.RecursiveChildReturnRoleBank

/-! One concrete fixed recursive graph for the network, as `Shared50RecursiveImplementation`: all
implementation fields are physical programs on the common bank, including the temporaries' fills
and the resets. No runtime width or recursion depth is a program parameter. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.Implementation
noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open CallLayout (parked active_ne_io)
open Control (PC)
variable [Net]

abbrev commonCount : ℕ := Shared50RecursiveBank.Count payloadCount 0

def widthSlot : Fin commonCount := RecursiveCallBank.headerSlot 3
def descriptorStack : Fin commonCount := Shared50RecursiveBank.returnSlot 0
def pcStack : Fin commonCount := Shared50RecursiveBank.returnSlot 1

/-- Only the fixed return-address bit capacity parametrizes the implementation;
every call site parks the other wire streams in the same finite order. -/
def implementation (k : ℕ) : Control.Implementation commonCount prime k where
  base := SharedBankFamily.ofProgram
    (RecursiveDigitRoleBank.program (u := Shared50RecursiveBank.AuxCount 0) io)
  split := BankNodes.entry (u := 0)
  tempInit := BankNodes.tempInit (u := 0)
  tempClear := BankNodes.tempClear (u := 0)
  merge := BankNodes.exit (u := 0)
  restore := SharedBankFamily.ofProgram
    (RecursiveChildReturnRoleBank.restoreProgram (t := payloadCount) (u := 3+(1+(1+0))))
  segment := BankNodes.segment (u := 0)
  gate := BankNodes.gate (u := 0)
  reset := BankNodes.reset (u := 0)
  enter := fun w i j code => RecursiveCallProtocol.enter (u := 1+(1+0))
    (parked w) (wireSlot w) io (active_ne_io w) i j code
  recover := fun w _ _ => RecursiveCallProtocol.recover (u := 1+(1+0))
    (parked w) (wireSlot w) io (active_ne_io w)

/-- A single compile-time return width for the full literal schedule. -/
def returnWidth : ℕ := Classical.choose Control.capacity_exists

theorem returnCapacity : Fintype.card PC ≤ 2^returnWidth :=
  Classical.choose_spec Control.capacity_exists

/-- The actual closed cyclic machine, including guard and decoded returns. -/
def graph := Control.program returnCapacity widthSlot pcStack (implementation returnWidth)

def headerField (i : Fin 6) : BinaryDescriptorFrames.Slot descriptorStack :=
  ⟨RecursiveCallBank.headerSlot i,by
    intro he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    simp only [RecursiveCallBank.headerSlot,descriptorStack,Shared50RecursiveBank.returnSlot,
      Fin.val_natAdd,Fin.val_castAdd] at hv
    omega⟩

def rootFields : List (BinaryDescriptorFrames.Slot descriptorStack) :=
  List.ofFn headerField

/-- Root header saving and the real halt-sentinel push precede the same fixed
graph used by every child. Proving its total execution remains an obligation. -/
def program := Control.rootProgram returnCapacity widthSlot pcStack descriptorStack
  rootFields (implementation returnWidth)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.Implementation
