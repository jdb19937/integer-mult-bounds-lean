module

public import IntegerMultBounds.MathlibTM2.M8.Frames.RootBankCheck

/-! A common description for plain spans, root complements and wire endpoints.
Nesting reduces to certified span inclusion or exact orthogonality of bases. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames.Signed

inductive Frame where
  | zero
  | one
  | positive (i : Nat)
  | negative (i : Nat)
  deriving Inhabited, DecidableEq

def Frame.validCheck (size : Nat) : Frame → Bool
  | .zero | .one => true
  | .positive i | .negative i => Nat.blt i size

/-- Rank determined by the basis certificate and the sign. -/
def Frame.rankValue (bank : Nat → RootBank.Record) : Frame → Nat
  | .zero => 0
  | .one => 23
  | .positive i => (bank i).basis.length
  | .negative i => 23 - (bank i).basis.length

/-- Reuse an existing generator claim when possible; otherwise verify the
small target basis by the certified source inverse. -/
def spanCheck (a b : RootBank.Record) : Bool :=
  a.nestedCheck b || a.generatorCheck b.basis

/-- Orthogonality under `9 G`, without rational matrix evaluation. -/
def orthogonalCheck (a b : RootBank.Record) : Bool :=
  a.basis.all fun u => b.basis.all fun v => RootCheck.g9 u v == 0

def Frame.nestedCheck (bank : Nat → RootBank.Record) : Frame → Frame → Bool
  | .zero, _ => true
  | _, .one => true
  | .positive i, .positive j => spanCheck (bank j) (bank i)
  | .negative i, .negative j => spanCheck (bank i) (bank j)
  | .positive i, .negative j => orthogonalCheck (bank i) (bank j)
  | _, _ => false

def chainCheck (bank : Nat → RootBank.Record) (size : Nat) : List Frame → Bool
  | [] => true
  | frame :: frames => frame.validCheck size &&
      match frames with
      | [] => true
      | next :: _ => frame.nestedCheck bank next && chainCheck bank size frames

end IntegerMultBounds.MathlibTM2.M8.Frames.Signed
