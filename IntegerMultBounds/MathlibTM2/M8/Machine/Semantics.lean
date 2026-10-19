module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Pieces
public import IntegerMultBounds.Networks.AffineFieldBijective

/-!
# Semantics of the pieces

The pieces act on role streams as their atoms do: a segment moves the addresses of its wire by
its field program, a call by its interchange, a gate is the module gate and a reset zeroes its
wire (`piece`). Flattening the pieces back to the control gives the network's run
(`run_fixed`), hence the routed transpose on every contract role when the temporaries start at
zero (`run_identity`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks
open Shared50ModularControl (prime)

variable [Net] (b : ℕ)

local instance : NeZero (prime ^ b) := ⟨ne_of_gt (pow_pos Shared50ModularControl.prime_prime.pos _)⟩

/-- A stream of the machine at width `b`. -/
abbrev Stream := Arrays width (prime ^ b)

namespace Semantics

/-- Legality of the reduction mod `prime ^ b`. -/
def Legal (p : FieldProgram) : Prop := ∀ op ∈ specialize (prime ^ b) p, AffineFieldProgram.Legal op

theorem legal_control {i : Wire} {p : FieldProgram} (hp : Step.edge i p ∈ control) : Legal b p :=
  legal_mod b i p hp

theorem legal_sublist (p q : FieldProgram) (hp : Legal b p) (hq : ∀ op ∈ q, op ∈ p) : Legal b q := by
  intro op hop
  obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hop
  exact hp _ (List.mem_map.mpr ⟨src, hq src hsrc, rfl⟩)

theorem legal_append (p q : FieldProgram) (hp : Legal b p) (hq : Legal b q) : Legal b (p ++ q) := by
  intro op hop
  simp only [specialize, List.map_append, List.mem_append] at hop
  exact hop.elim (hp op) (hq op)

theorem bijective (p : FieldProgram) (hp : Legal b p) :
    Function.Bijective (AffineFieldProgram.run (specialize (prime ^ b) p)) :=
  AffineFieldBijective.run_bijective _ hp

/-- The forward-entry law of the edge semantics. -/
theorem edge_entry (p : FieldProgram) (hp : Legal b p) (f : Stream b)
    (x : Address width (prime ^ b)) :
    edgeAction width (prime ^ b) p f (AffineFieldProgram.run (specialize (prime ^ b) p) x) = f x :=
  congrArg f (Function.leftInverse_invFun (bijective b p hp).1 x)

theorem edge_nil (f : Stream b) : edgeAction width (prime ^ b) [] f = f := by
  funext x
  exact edge_entry b [] (by intro op hop; exact (List.not_mem_nil hop).elim) f x

theorem run_append (p q : FieldProgram) (x : Address width (prime ^ b)) :
    AffineFieldProgram.run (specialize (prime ^ b) (p ++ q)) x =
      AffineFieldProgram.run (specialize (prime ^ b) q)
        (AffineFieldProgram.run (specialize (prime ^ b) p) x) := by
  simp only [specialize, List.map_append, AffineFieldProgram.run, List.foldl_append]

theorem edge_append (p q : FieldProgram) (hp : Legal b p) (hq : Legal b q) (f : Stream b) :
    edgeAction width (prime ^ b) (p ++ q) f =
      edgeAction width (prime ^ b) q (edgeAction width (prime ^ b) p f) := by
  funext x
  obtain ⟨y, rfl⟩ := (bijective b (p ++ q) (legal_append b p q hp hq)).2 x
  rw [edge_entry b (p ++ q) (legal_append b p q hp hq), run_append, edge_entry b q hq,
    edge_entry b p hp]

def atom (a : Atom) (stored : Wire → Stream b) : Wire → Stream b := match a with
  | .field wire op => Function.update stored wire (edgeAction width (prime ^ b) [op] (stored wire))
  | .gate g => FramedCircuit.moduleGate g stored
  | .reset wire => Function.update stored wire 0

def atoms (as : List Atom) (stored : Wire → Stream b) :=
  as.foldl (fun stored a => atom b a stored) stored

def piece (p : Piece) (stored : Wire → Stream b) : Wire → Stream b := match p with
  | .segment seg => Function.update stored seg.wire (edgeAction width (prime ^ b) seg.ops (stored seg.wire))
  | .call wire i j =>
      Function.update stored wire (edgeAction width (prime ^ b) [.interchange i j] (stored wire))
  | .gate g => FramedCircuit.moduleGate g.scalar stored
  | .reset r => Function.update stored r.wire 0

def run (ps : List Piece) (stored : Wire → Stream b) :=
  ps.foldl (fun stored p => piece b p stored) stored

theorem atoms_append (as bs : List Atom) (stored : Wire → Stream b) :
    atoms b (as ++ bs) stored = atoms b bs (atoms b as stored) := List.foldl_append

/-- A complete field program is its atoms, in order. -/
theorem atoms_fields (wire : Wire) (ops : FieldProgram) (hp : Legal b ops)
    (stored : Wire → Stream b) :
    atoms b (ops.map (Atom.field wire)) stored =
      Function.update stored wire (edgeAction width (prime ^ b) ops (stored wire)) := by
  induction ops generalizing stored with
  | nil => simp only [List.map_nil, atoms, List.foldl_nil, edge_nil, Function.update_eq_self]
  | cons op ops ih =>
    have hhead : Legal b [op] := legal_sublist b _ _ hp
      (by intro x hx; exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hx)))
    have htail : Legal b ops := legal_sublist b _ _ hp (by intro x hx; exact List.mem_cons_of_mem _ hx)
    change atoms b (ops.map (Atom.field wire))
      (Function.update stored wire (edgeAction width (prime ^ b) [op] (stored wire))) = _
    rw [ih htail, Function.update_self, Function.update_idem]
    rw [show op :: ops = [op] ++ ops from rfl, edge_append b _ _ hhead htail]

/-- Every piece agrees with its atoms. -/
theorem piece_expand (p : Piece) (stored : Wire → Stream b) :
    atoms b (expandPiece p) stored = piece b p stored := by
  cases p with
  | segment seg =>
    exact atoms_fields b seg.wire seg.ops
      (legal_sublist b seg.parent seg.ops (legal_control b seg.member)
        (AffineFieldSegments.split_run_spec _ _ seg.run_member).1) stored
  | call wire i j => rfl
  | gate g => rfl
  | reset r => rfl

theorem run_expand (ps : List Piece) (stored : Wire → Stream b) :
    run b ps stored = atoms b (ps.flatMap expandPiece) stored := by
  induction ps generalizing stored with
  | nil => rfl
  | cons p ps ih =>
    change run b ps (piece b p stored) = _
    rw [ih, List.flatMap_cons, atoms_append, piece_expand]

theorem control_expand (cs : List Control) (hc : ∀ wire p, Step.edge wire p ∈ cs → Legal b p)
    (stored : Wire → Stream b) :
    atoms b (cs.flatMap expandControl) stored =
      Step.run (edgeAction width (prime ^ b)) cs stored := by
  induction cs generalizing stored with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, atoms_append]
    cases c with
    | edge wire p =>
      rw [show expandControl (.edge wire p) = p.map (Atom.field wire) from rfl,
        atoms_fields b wire p (hc wire p List.mem_cons_self)]
      exact ih (fun wire p hp => hc wire p (List.mem_cons_of_mem _ hp)) _
    | gate g => exact ih (fun wire p hp => hc wire p (List.mem_cons_of_mem _ hp)) _
    | reset w => exact ih (fun wire p hp => hc wire p (List.mem_cons_of_mem _ hp)) _

/-- Piece execution is the network's run. -/
theorem run_fixed (stored : Wire → Stream b) :
    run b pieces stored = Step.run (edgeAction width (prime ^ b)) control stored := by
  rw [run_expand, expansion_exact]
  exact control_expand b _ (fun wire p hp => legal_control b hp) stored

/-- The pieces realize the routed transpose on every contract role, from zero temporaries. -/
theorem run_identity (stored : Wire → Stream b) (h0 : ∀ t, stored (.inr t) = 0) (i : World)
    (a : Address width (prime ^ b)) :
    run b pieces stored (.inl i) a = stored (.inl ((Net.net).route i)) (a.2, a.1) := by
  rw [run_fixed]
  exact Machine.run_identity b stored h0 i a

end Semantics

end
end IntegerMultBounds.MathlibTM2.M8.Machine
