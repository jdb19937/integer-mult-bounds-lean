module

public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Ring

/-! Finite charge bookkeeping only: no scalar correctness or hosting assertion. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16

inductive Rank where
  | r1 | r2 | r3 | r4 | r5 | r8
  deriving DecidableEq, Repr

def Rank.value : Rank → ℕ
  | .r1 => 1 | .r2 => 2 | .r3 => 3 | .r4 => 4 | .r5 => 5 | .r8 => 8

structure Profile where
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  c5 : ℕ
  c8 : ℕ
  deriving DecidableEq, Repr

def Profile.zero : Profile := ⟨0,0,0,0,0,0⟩
def Profile.add (x y : Profile) : Profile :=
  ⟨x.c1+y.c1,x.c2+y.c2,x.c3+y.c3,x.c4+y.c4,x.c5+y.c5,x.c8+y.c8⟩
def Rank.profile : Rank → Profile
  | .r1 => ⟨1,0,0,0,0,0⟩ | .r2 => ⟨0,1,0,0,0,0⟩
  | .r3 => ⟨0,0,1,0,0,0⟩ | .r4 => ⟨0,0,0,1,0,0⟩
  | .r5 => ⟨0,0,0,0,1,0⟩ | .r8 => ⟨0,0,0,0,0,1⟩
def Profile.cost (p : Profile) (price : ℕ → ℕ) : ℕ :=
  p.c1*price 1+p.c2*price 2+p.c3*price 3+p.c4*price 4+p.c5*price 5+p.c8*price 8

/-- Literal charge-event projection; dimensions are copied from the pinned canonical frames. -/
structure Charge where
  event : ℕ
  center : Bool
  register : ℕ
  oldFrame : ℕ
  newFrame : ℕ
  oldDim : ℕ
  newDim : ℕ
  rank : Rank
  deriving DecidableEq, Repr

def Charge.valid (c : Charge) : Bool :=
  c.event < 24767 && c.register < (if c.center then 8 else 704) &&
  c.oldFrame < 1004 && c.newFrame < 1004 && c.oldDim ≤ 9 && c.newDim ≤ 9 &&
  c.rank.value = c.newDim - c.oldDim + (c.oldDim - c.newDim)

def chargeProfile : List Charge → Profile
  | [] => .zero
  | c::cs => c.rank.profile.add (chargeProfile cs)
def chunkProfile : List (List Charge) → Profile
  | [] => .zero
  | cs::css => (chargeProfile cs).add (chunkProfile css)
def chargeCost (cs : List Charge) (price : ℕ → ℕ) : ℕ :=
  (cs.map fun c => price c.rank.value).sum
def chunkCost (css : List (List Charge)) (price : ℕ → ℕ) : ℕ :=
  (css.map fun cs => chargeCost cs price).sum

theorem profile_add_cost (p q : Profile) (price : ℕ → ℕ) :
    (p.add q).cost price = p.cost price + q.cost price := by
  simp only [Profile.cost, Profile.add]
  ring

/-- This equality applies to any price assigned to each child rank. -/
theorem chargeCost_eq (cs : List Charge) (price : ℕ → ℕ) :
    chargeCost cs price = (chargeProfile cs).cost price := by
  induction cs with
  | nil => simp [chargeCost, chargeProfile, Profile.zero, Profile.cost]
  | cons c cs ih =>
    simp only [chargeCost, List.map_cons, List.sum_cons] at *
    rw [ih, chargeProfile, profile_add_cost]
    cases c.rank <;> simp [Rank.value, Rank.profile, Profile.cost]

theorem chunkCost_eq (css : List (List Charge)) (price : ℕ → ℕ) :
    chunkCost css price = (chunkProfile css).cost price := by
  induction css with
  | nil => simp [chunkCost, chunkProfile, Profile.zero, Profile.cost]
  | cons cs css ih =>
    simp only [chunkCost, List.map_cons, List.sum_cons] at *
    rw [ih, chunkProfile, profile_add_cost, chargeCost_eq]

structure Owner where
  time : ℕ
  stage : ℕ
  replica : ℕ
  helper : ℕ
  ownerReplica : ℕ
  child : ℕ
  port : ℕ
  copy : ℕ
  family : ℕ
  offset : ℕ
  width : ℕ
  deriving DecidableEq, Repr

/-- Index and namespace checks only. Slice disjointness and source-event windows are separate. -/
def Owner.valid (o : Owner) : Bool :=
  o.time < 144 && o.stage < 9 && o.replica < 16 &&
  o.helper < 480 && o.ownerReplica < 16 && o.child < 18 && o.port < 112 &&
  o.copy = 112*o.ownerReplica+o.port && o.family < 14336 &&
  o.width ≤ 9 && 0 < o.width && o.offset + o.width ≤ 73

structure Call where
  stage : ℕ
  replica : ℕ
  forward : Bool
  deriving DecidableEq, Repr

def Call.valid (c : Call) : Bool :=
  c.stage < 9 && c.replica < 16 && c.forward = (c.stage % 2 = 0)

theorem sum_map_constant {α : Type*} (xs : List α) (n : ℕ) :
    (xs.map fun _ => n).sum = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

end IntegerMultBounds.Networks.Certificates.T16
