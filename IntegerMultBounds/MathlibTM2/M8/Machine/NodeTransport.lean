module

public import IntegerMultBounds.MathlibTM2.M8.Machine.NodePieces
public import IntegerMultBounds.MathlibTM2.M8.Machine.Semantics

/-!
# The pieces on the node bank follow the network

On the node payload bank, every piece acts on each fiber of fixed spectator coordinates as the
semantic piece acts on streams (`represents_step`), given that each recursive call exchanges
exactly its chosen sub-fields and keeps every other tape (`ChildSpec`). Through the whole piece
list, from zero temporaries, every contract role ends with the routed transpose of the input
(`run_entry`), and the input/output tape is unchanged (`run_io`). This is
`Shared50NodePieceTransport` with temporaries and resets.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (index)
open RecursiveMixedSchedule (Data)

variable [Net] {b : ℕ} {v : Descriptor}

local instance : NeZero (prime ^ b) := ⟨ne_of_gt (pow_pos Shared50ModularControl.prime_prime.pos _)⟩

namespace Transport

abbrev Addr (b : ℕ) (v : Descriptor) := RecursiveScalarCoordinates.Address width b v

def withState (x : Addr b v) (s : Address width (prime ^ b)) : Addr b v := {x with h := s.1, d := s.2}

/-- The node bank holds the streams on the fiber of `x`. -/
def Represents (hw : v.width = width * b) (x : Addr b v) (data : Data payloadCount v)
    (stored : Wire → Stream b) : Prop :=
  ∀ w s, data (wireSlot w) (index hw (withState x s)) = SparseRoleCircuit.encode (a := 0) (stored w s)

/-- The streams of bits on the fiber of `x`. -/
def fiber (hw : v.width = width * b) (bits : Wire → Fin (volume prime v) → ZMod 2) (x : Addr b v) :
    Wire → Stream b :=
  fun w s => bits w (index hw (withState x s))

theorem represents_encoded (hw : v.width = width * b) (bits : Wire → Fin (volume prime v) → ZMod 2)
    (extra : Fin (volume prime v) → Fin 4) (x : Addr b v) :
    Represents hw x (encodedBits bits extra) (fiber hw bits x) := fun w _ => by
  rw [encodedBits_wire]; rfl

/-- A forward permutation contract determines the edge action. -/
theorem represents_edge (hw : v.width = width * b) (x : Addr b v) (data out : Data payloadCount v)
    (stored : Wire → Stream b) (hr : Represents hw x data stored) (w : Wire) (p : FieldProgram)
    (hp : Semantics.Legal b p)
    (he : ∀ s, out (wireSlot w) (index hw (withState x (AffineFieldProgram.run (specialize (prime ^ b) p) s))) =
      data (wireSlot w) (index hw (withState x s)))
    (ho : ∀ k, k ≠ w → out (wireSlot k) = data (wireSlot k)) :
    Represents hw x out (Function.update stored w (edgeAction width (prime ^ b) p (stored w))) := by
  intro k s
  by_cases hk : k = w
  · subst k
    obtain ⟨y, rfl⟩ := (Semantics.bijective b p hp).2 s
    rw [he, hr, Function.update_self, Semantics.edge_entry b p hp]
  · rw [ho k hk, hr, Function.update_of_ne hk]

theorem represents_segment (seg : Segment) (hw : v.width = width * b) (x : Addr b v)
    (data : Data payloadCount v) (stored : Wire → Stream b) (hr : Represents hw x data stored) :
    Represents hw x (seg.array hw data) (Semantics.piece b (.segment seg) stored) := by
  apply represents_edge hw x data _ stored hr seg.wire seg.ops
  · exact Semantics.legal_sublist b seg.parent seg.ops (Semantics.legal_control b seg.member)
      (AffineFieldSegments.split_run_spec _ _ seg.run_member).1
  · intro s
    exact seg.array_entry hw data (withState x s)
  · intro k hk
    exact seg.array_other hw data (wireSlot k) (wireSlot_injective.ne hk)

/-- A gate reads only wire tapes at the same symbol position. -/
theorem gate_congr (g : Gate) (data other : Data payloadCount v) (z : Fin (volume prime v))
    (h : ∀ w, data (wireSlot w) z = other (wireSlot w) z) (w : Wire) :
    g.array data (wireSlot w) z = g.array other (wireSlot w) z := by
  by_cases hk : wireSlot w = (Gate.physical g).dst
  · rw [hk]
    simp only [Gate.array, Gate.ops, RoleOps.run, List.foldl_cons, List.foldl_nil,
      RoleOps.transform, Function.update_self]
    simp only [Gate.physical]
    rw [h, h]
  · simp only [Gate.array, Gate.ops, RoleOps.run, List.foldl_cons, List.foldl_nil,
      RoleOps.transform, Function.update_of_ne hk]
    exact h w

theorem represents_gate (g : Gate) (hw : v.width = width * b) (x : Addr b v)
    (data : Data payloadCount v) (stored : Wire → Stream b) (hr : Represents hw x data stored) :
    Represents hw x (g.array data) (Semantics.piece b (.gate g) stored) := by
  intro w s
  let ref := encodedBits (v := v) (fun w _ => stored w s) (fun _ => 0)
  have hc := gate_congr g data ref (index hw (withState x s)) (fun k => by
    rw [hr k s]
    simp only [ref, encodedBits_wire]) w
  rw [hc]
  simp only [ref]
  rw [Gate.array_encoded, encodedBits_wire]
  simp only [Semantics.piece, FramedCircuit.moduleGate_pointwise]

theorem represents_reset (r : Reset) (hw : v.width = width * b) (x : Addr b v)
    (data : Data payloadCount v) (stored : Wire → Stream b) (hr : Represents hw x data stored) :
    Represents hw x (r.array data) (Semantics.piece b (.reset r) stored) := by
  intro w s
  simp only [Reset.array, Reset.ops, RoleOps.run, List.foldl_cons, List.foldl_nil,
    RoleOps.transform, Reset.physical, Semantics.piece]
  by_cases hk : w = r.wire
  · subst hk
    simp
  · rw [Function.update_of_ne (wireSlot_injective.ne hk), hr, Function.update_of_ne hk]

/-- A child call on a wire with its two chosen sub-fields. -/
abbrev Child (v : Descriptor) := Wire → Fin width → Fin width → Data payloadCount v → Data payloadCount v

/-- A recursive call exchanges exactly its chosen sub-fields of its wire and keeps every other
tape, including the input/output tape. -/
structure ChildSpec (hw : v.width = width * b) (child : Child v) : Prop where
  entry : ∀ w i j data (x : Addr b v),
    child w i j data (wireSlot w)
      (index hw (withState x (AffineFieldProgram.execute (.interchange i j) (x.h, x.d)))) =
      data (wireSlot w) (index hw x)
  other : ∀ w i j data k, k ≠ wireSlot w → child w i j data k = data k

def step (hw : v.width = width * b) (child : Child v) (p : Piece) (data : Data payloadCount v) :
    Data payloadCount v :=
  match p with
  | .segment seg => seg.array hw data
  | .gate g => g.array data
  | .call w i j => child w i j data
  | .reset r => r.array data

def run (hw : v.width = width * b) (child : Child v) (ps : List Piece) (data : Data payloadCount v) :=
  ps.foldl (fun data p => step hw child p data) data

theorem represents_call (hw : v.width = width * b) (child : Child v) (hc : ChildSpec hw child)
    (w : Wire) (i j : Fin width) (x : Addr b v) (data : Data payloadCount v)
    (stored : Wire → Stream b) (hr : Represents hw x data stored) :
    Represents hw x (child w i j data) (Semantics.piece b (.call w i j) stored) := by
  apply represents_edge hw x data _ stored hr w [.interchange i j]
  · intro op hop
    simp only [specialize, List.map_cons, List.map_nil, List.mem_singleton,
      AffineFieldProgram.mapOp] at hop
    subst op
    trivial
  · intro s
    exact hc.entry w i j data (withState x s)
  · intro k hk
    exact hc.other w i j data (wireSlot k) (wireSlot_injective.ne hk)

theorem represents_step (hw : v.width = width * b) (child : Child v) (hc : ChildSpec hw child)
    (p : Piece) (x : Addr b v) (data : Data payloadCount v) (stored : Wire → Stream b)
    (hr : Represents hw x data stored) :
    Represents hw x (step hw child p data) (Semantics.piece b p stored) := by
  cases p with
  | segment seg => exact represents_segment seg hw x data stored hr
  | gate g => exact represents_gate g hw x data stored hr
  | call w i j => exact represents_call hw child hc w i j x data stored hr
  | reset r => exact represents_reset r hw x data stored hr

theorem represents_run (hw : v.width = width * b) (child : Child v) (hc : ChildSpec hw child)
    (ps : List Piece) (x : Addr b v) (data : Data payloadCount v) (stored : Wire → Stream b)
    (hr : Represents hw x data stored) :
    Represents hw x (run hw child ps data) (Semantics.run b ps stored) := by
  induction ps generalizing data stored with
  | nil => exact hr
  | cons p ps ih => exact ih _ _ (represents_step hw child hc p x data stored hr)

theorem step_io (hw : v.width = width * b) (child : Child v) (hc : ChildSpec hw child)
    (p : Piece) (data : Data payloadCount v) : step hw child p data io = data io := by
  cases p with
  | segment seg => exact seg.array_io hw data
  | gate g => exact g.array_io data
  | call w i j => exact hc.other w i j data io (wireSlot_ne_io w).symm
  | reset r => exact r.array_io data

theorem run_io (hw : v.width = width * b) (child : Child v) (hc : ChildSpec hw child)
    (ps : List Piece) (data : Data payloadCount v) : run hw child ps data io = data io := by
  induction ps generalizing data with
  | nil => rfl
  | cons p ps ih => exact (ih _).trans (step_io hw child hc p data)

/-- From zero temporaries, the piece list ends with the routed transpose on every contract role,
given only each child call's exact interchange semantics. -/
theorem run_entry (hw : v.width = width * b) (child : Child v) (hc : ChildSpec hw child)
    (bits : Wire → Fin (volume prime v) → ZMod 2) (h0 : ∀ t, bits (.inr t) = 0)
    (extra : Fin (volume prime v) → Fin 4) (w : World) (x : Addr b v) :
    run hw child pieces (encodedBits bits extra) (wireSlot (.inl w)) (index hw x) =
      SparseRoleCircuit.encode (a := 0) (bits (.inl ((Net.net).route w))
        (index hw {x with h := x.d, d := x.h})) := by
  have hh := represents_run hw child hc pieces x (encodedBits bits extra) (fiber hw bits x)
    (represents_encoded hw bits extra x)
  have hz : ∀ t, fiber hw bits x (.inr t) = 0 := fun t => by
    funext s; simp [fiber, h0 t]
  have e := hh (.inl w) (x.h, x.d)
  rw [Semantics.run_identity b _ hz w (x.h, x.d)] at e
  exact e

end Transport

end
end IntegerMultBounds.MathlibTM2.M8.Machine
