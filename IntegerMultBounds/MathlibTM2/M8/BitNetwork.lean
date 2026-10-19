module

public import IntegerMultBounds.Networks.FramedCircuit
public import IntegerMultBounds.Networks.AffineFieldProgram
public import IntegerMultBounds.Networks.ReversibleFanout
public import IntegerMultBounds.Swap.Modular
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The bit-network interface

A `BitNetwork` is a fixed interchange node: a finite list of steps on named role streams, whose
semantics is the routed transpose of the two address fields on every contract role, with an
exact count of recursive interchanges. The word side supplies an instance (PR97 in `M8`);
the machine side runs any instance in the recursive interchange machine. The Shared50 control
(`Networks.Shared50FixedControl`) has the same content, without temporaries.

A role stream is an array over the address pairs `(H, D) ∈ (ℤ/q^b)^m × (ℤ/q^b)^m` with bits as
values (`Arrays m (q^b)`). A step is one of:
* `edge i p`: the rational field program `p`, reduced mod `q^b`, moves the addresses of stream `i`;
  its `interchange` operations are the recursive children, the others are nonrecursive passes;
* `gate g`: the pointwise bit XOR `dst += src` of two streams;
* `reset i`: stream `i` becomes zero.

Roles are the contract streams `World` and machine-private temporaries `Temp`. Temporaries are
zero on entry and carry no contract on exit; the machine allocates them as extra rows of the
node's row size, so they do not enter the child volume `V / roleCount`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8

noncomputable section
open Networks

/-- One address field: `m` coordinates in `ℤ/q`. -/
abbrev Vector (m q : ℕ) := Fin m → ZMod q
/-- An address pair `(H, D)`. -/
abbrev Address (m q : ℕ) := Vector m q × Vector m q
/-- A role stream: one bit per address pair. -/
abbrev Arrays (m q : ℕ) := Address m q → ZMod 2

/-- A rational field program on `m` coordinates per field. -/
abbrev FieldProgram (m : ℕ) := List (AffineFieldProgram.Op (Fin m) ℚ)

/-- The reduction of a rational field program mod `q`. -/
def specialize {m : ℕ} (q : ℕ) (p : FieldProgram m) : List (AffineFieldProgram.Op (Fin m) (ZMod q)) :=
  p.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod q))

/-- One step of a node on wires `ι` with edge programs `P`. -/
inductive Step (ι P : Type) where
  | edge (wire : ι) (program : P)
  | gate (g : Circuit.Gate ι (ZMod 2))
  | reset (wire : ι)

namespace Step
variable {ι P E : Type} [AddCommGroup E] [Module (ZMod 2) E] [DecidableEq ι]

/-- Semantics of one step, for a given meaning `edge` of edge programs. -/
def execute (edge : P → E → E) : Step ι P → (ι → E) → (ι → E)
  | .edge i p, x => Function.update x i (edge p (x i))
  | .gate g, x => FramedCircuit.moduleGate g x
  | .reset i, x => Function.update x i 0

def run (edge : P → E → E) : List (Step ι P) → (ι → E) → (ι → E)
  | [], x => x
  | step :: rest, x => run edge rest (execute edge step x)

/-- The edge programs, in order. -/
def programs (s : List (Step ι P)) : List P :=
  s.filterMap fun step => match step with
    | .edge _ p => some p
    | _ => none

/-- The gates, in order. -/
def gates (s : List (Step ι P)) : Circuit.Program ι (ZMod 2) :=
  s.filterMap fun step => match step with
    | .gate g => some g
    | _ => none

end Step

/-- The meaning of an edge program on a stream at modulus `q`: the stored array is read through
the inverse of the program's address map, so the stream's entry at `a` moves to `run p a`. This
is a semantic evaluator; the machine executes the program's passes and children. -/
def edgeAction (m q : ℕ) (p : FieldProgram m) (f : Arrays m q) : Arrays m q :=
  fun a => f (Function.invFun (AffineFieldProgram.run (specialize q p)) a)

/-- The number of recursive interchanges in all edge programs of a step list. -/
def calls {ι : Type} {m : ℕ} (s : List (Step ι (FieldProgram m))) : ℕ :=
  ((Step.programs s).map AffineFieldProgram.interchanges).sum

/-- A fixed interchange node with its certificates. -/
structure BitNetwork where
  /-- The contract roles. -/
  World : Type
  /-- The machine-private temporaries. -/
  Temp : Type
  [worldFintype : Fintype World]
  [worldDecidableEq : DecidableEq World]
  [tempFintype : Fintype Temp]
  [tempDecidableEq : DecidableEq Temp]
  /-- The number of contract roles, the row divisor of the node. -/
  roleCount : ℕ
  /-- A fixed enumeration of the contract roles (the machine's row order). -/
  roleEquiv : Fin roleCount ≃ World
  /-- The number of temporaries. -/
  tempCount : ℕ
  /-- A fixed enumeration of the temporaries. -/
  tempEquiv : Fin tempCount ≃ Temp
  /-- Address coordinates per field (`m`): the node interchanges `m` sub-fields of `H` with `m`
  sub-fields of `D`, and every child interchanges one sub-field of each. -/
  width : ℕ
  two_le_width : 2 ≤ width
  /-- The address prime `q`: sub-fields are `ℤ/q^b` at runtime width `b`. -/
  prime : ℕ
  prime_prime : prime.Prime
  prime_odd : prime ≠ 2
  /-- The node: one fixed list, the same at every runtime width `b`. -/
  control : List (Step (World ⊕ Temp) (FieldProgram width))
  /-- The data route: contract role `i` ends with the transposed stream of role `route i`. -/
  route : World → World
  route_involutive : Function.Involutive route
  /-- The exact number of recursive children of one node (`s`). -/
  rankSum : ℕ
  calls_exact : calls control = rankSum
  /-- Every operation of every edge program is legal over `ℚ`: scalings by nonzero rationals and
  shifts whose control coordinate precedes the target (`OrderedAffine.Legal`). -/
  legal : ∀ (i : World ⊕ Temp) (p : FieldProgram width), Step.edge i p ∈ control →
    ∀ op ∈ p, AffineFieldProgram.Legal op
  /-- The reductions mod every `q^b` are legal too: every scaling stays a unit. -/
  legal_mod : ∀ (b : ℕ) (i : World ⊕ Temp) (p : FieldProgram width), Step.edge i p ∈ control →
    ∀ op ∈ specialize (prime ^ b) p, AffineFieldProgram.Legal op
  /-- Every gate is one XOR `dst += src` of two distinct streams. -/
  xor_gate : ∀ g, Step.gate g ∈ control → ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src
  /-- The node theorem: at every width `b`, on arbitrary stored streams of the contract roles and
  zero temporaries, contract role `i` ends with the stream of `route i`, its two address fields
  exchanged. -/
  run_identity : ∀ (b : ℕ) (stored : World ⊕ Temp → Arrays width (prime ^ b)),
    (∀ t, stored (.inr t) = 0) → ∀ (i : World) (a : Address width (prime ^ b)),
      Step.run (edgeAction width (prime ^ b)) control stored (.inl i) a =
        stored (.inl (route i)) (a.2, a.1)
  /-- The width exponent of the uniform recursion. -/
  tau : ℝ
  tau_pos : 0 < tau
  tau_lt_one : tau < 1
  /-- Uniform branching: `s` children of volume `V / roleCount` per node of width `m`. -/
  branching : (rankSum : ℝ) / roleCount < (width : ℝ) ^ tau

attribute [instance] BitNetwork.worldFintype BitNetwork.worldDecidableEq BitNetwork.tempFintype
  BitNetwork.tempDecidableEq

end
end IntegerMultBounds.MathlibTM2.M8
