module

public import IntegerMultBounds.MathlibTM2.M8.Local.Compile

/-! Structural sorting for the small slot intervals checked by the kernel. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local

def insertSlot (index : Nat → Nat) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if Nat.ble (index x) (index y) then x :: y :: ys else y :: insertSlot index x ys

def sortSlots (index : Nat → Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => insertSlot index x (sortSlots index xs)

end IntegerMultBounds.MathlibTM2.M8.Local
