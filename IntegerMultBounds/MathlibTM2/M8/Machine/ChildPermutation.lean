module

public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeData
public import IntegerMultBounds.Machine.Shared50RecursiveChildPermutation

/-!
# The child call on a wire

A recursive call on a wire is the full H/D swap of its tape in the cross-field view of its two
chosen sub-fields (`Shared50RecursiveChildPermutation.array`, which is generic in the width).
On the node bank it changes only its wire's tape (`child`), it meets the transport's
`ChildSpec` (`child_spec`), and on bit streams it updates exactly its wire's stream
(`child_encoded`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50RecursiveChildPermutation (array array_entry array_encoded)

variable [Net] {b : ℕ} {v : Descriptor}

namespace ChildPermutation

/-- The child call on the node bank. -/
def child (hw : v.width = width * b) : Transport.Child v :=
  fun w i j data => Function.update data (wireSlot w) (array hw i j (data (wireSlot w)))

theorem child_spec (hw : v.width = width * b) : Transport.ChildSpec hw (child hw) := by
  constructor
  · intro w i j data a
    simp only [child, Function.update_self]
    exact array_entry hw i j (data (wireSlot w)) a
  · intro w i j data k hk
    exact Function.update_of_ne hk _ _

/-- On bit streams a child call updates exactly its wire's stream. -/
theorem child_encoded (hw : v.width = width * b) (w : Wire) (i j : Fin width)
    (bits : Wire → Fin (volume prime v) → ZMod 2) (extra : Fin (volume prime v) → Fin 4) :
    child hw w i j (encodedBits bits extra) =
      encodedBits (Function.update bits w (array hw i j (bits w))) extra := by
  rw [encodedBits_update]
  simp only [child, encodedBits_wire]
  rfl

end ChildPermutation

end
end IntegerMultBounds.MathlibTM2.M8.Machine
