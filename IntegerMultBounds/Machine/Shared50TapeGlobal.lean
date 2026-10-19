module

public import IntegerMultBounds.Machine.Shared50TapeInvocation

/-! The actual Shared50 three-coordinate reused-world scalar list compiled to
one fixed multitape program. This establishes exact stream-bank exchange and
restoration of arbitrary dirty scratch at linear stream-volume cost; affine
routing and recursive interchange composition remain separate operations. -/

@[expose] public section

namespace IntegerMultBounds.Machine.Shared50TapeGlobal
open Networks
open Shared50GlobalBudget (Address Scratch World)
variable {a L : ℕ}
noncomputable section

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code
  Shared50Finite.program Shared50GlobalCircuit.program50

abbrev roleCount := 406321422080000

def roleEquiv : Fin roleCount ≃ World :=
  (Fintype.equivFinOfCardEq Shared50GlobalBudget.world_card).symm

def contents (X Y : Address → Fin L → ZMod 2) (S : Scratch → Fin L → ZMod 2) :
    World → Fin L → ZMod 2 :=
  fun k i => Shared50GlobalCircuit.contents (fun j => X j i) (fun j => Y j i) (fun j => S j i) k

def bank (background : Fin roleCount → ℤ → Fin (a+4)) (origins : Fin roleCount → ℤ)
    (X Y : Address → Fin L → ZMod 2) (S : Scratch → Fin L → ZMod 2) (bs : List Bool) :=
  PointwiseRoleGate.bank background origins
    (SparseRoleCircuit.encoded (fun k i => contents X Y S (roleEquiv k) i)) bs

/-- This is the compiled real instruction list, independent of stream length. -/
def program :=
  OneSourceCircuit.program (a := a) roleEquiv Shared50GlobalCircuit.program50 Shared50XorLists.global50

theorem cost_linear (bs : List Bool) (hL : Counter.value bs = L)
    (hc : GrowingCounterData.Canonical bs) (hpos : 0 < L) :
    Shared50GlobalCircuit.program50.length*(14*L+14*bs.length+34) ≤
      (76*(3*19600^2*5209540))*L := by
  have ht := SparseRoleCircuit.cost_linear Shared50GlobalCircuit.program50.length L bs hL hc hpos
  have hg := Shared50GlobalCircuit.program50_instruction_bound
  nlinarith

end
end IntegerMultBounds.Machine.Shared50TapeGlobal
