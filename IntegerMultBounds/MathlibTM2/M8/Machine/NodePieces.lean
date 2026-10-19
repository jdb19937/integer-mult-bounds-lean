module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Pieces
public import IntegerMultBounds.MathlibTM2.M8.Machine.RoleOpsBank
public import IntegerMultBounds.Machine.RecursiveScalarSchedule

/-!
# Pieces on the node payload bank

The node bank holds one role tape per wire, contract roles first and then the temporaries, and
one separate input/output tape last (`payloadCount`, `io`). On it:
* a segment runs its stages on its wire's tape (`Segment.machine`, `Segment.realizesNode`): the wire's addresses move by
  the reduced field program (`Segment.array_entry`), and every other tape, in particular the
  input/output tape, is unchanged;
* a gate is one XOR of two wire tapes (`Gate.machine`), the exact module gate on bit streams
  (`Gate.array_encoded`);
* a reset zeroes its wire's tape, reading the input/output tape only as a source slot
  (`Reset.machine`, `Reset.array_encoded`).

Each has a fixed machine with a linear time bound on the permanent role bank, as the Shared50
node segments and gates do.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (index)
open RecursiveViewedAction (Data)
open RecursiveViewFrameRoleBank (bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)

variable [Net] {b u : ℕ} {v : Descriptor}

local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- The wire tapes and the input/output tape. -/
abbrev payloadCount : ℕ := wireCount + 1

/-- The input/output tape. -/
def io : Fin payloadCount := Fin.last wireCount

/-- The tape of a wire. -/
def wireSlot (w : Wire) : Fin payloadCount := Fin.castAdd 1 (wireEquiv.symm w)

theorem wireSlot_ne_io (w : Wire) : wireSlot w ≠ io := by
  intro he
  have hv := congrArg Fin.val he
  have hi := (wireEquiv.symm w).isLt
  simp only [wireSlot, io, Fin.val_castAdd, Fin.val_last] at hv
  omega

theorem wireSlot_injective : Function.Injective wireSlot := fun _ _ h =>
  wireEquiv.symm.injective (Fin.castAdd_injective _ _ h)

/-! ### Segments -/

namespace Segment

def machine (seg : Segment) := RecursiveScalarSchedule.machine (u := u) (wireSlot seg.wire) seg.stages

def coefficient (seg : Segment) := RecursiveScalarSchedule.coefficient (wireSlot seg.wire) seg.stages

def array (seg : Segment) (hw : v.width = width * b) (data : Data payloadCount v) :=
  RecursiveScalarSchedule.run (wireSlot seg.wire) seg.stages hw data

/-- The field-program semantics, keeping all spectators and rows fixed. -/
def execute (seg : Segment) (x : RecursiveScalarCoordinates.Address width b v) : RecursiveScalarCoordinates.Address width b v :=
  let out := AffineFieldProgram.run
    (seg.ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) (x.h, x.d)
  {x with h := out.1, d := out.2}

theorem execute_exact (seg : Segment) (x : RecursiveScalarCoordinates.Address width b v) :
    RecursiveScalarSchedule.execute seg.stages x = seg.execute x := by
  rw [RecursiveScalarSchedule.execute_eq]
  have he := Segments.description_actions seg.ops seg.good b
  change seg.stages.map (fun op => op.action b) = _ at he
  rw [he]
  change RecursiveScalarSchedule.replaceFields x
    (OrderedAffine.run _ (AffineFieldCoordinates.embed (x.h, x.d))) = _
  rw [AffineFieldCoordinates.segment_run _ (Segments.nonrecursive_map seg.ops seg.good b)]
  simp only [RecursiveScalarSchedule.replaceFields, AffineFieldCoordinates.embed_h,
    AffineFieldCoordinates.embed_d, execute]

/-- Every input symbol appears at its field-program destination. -/
theorem array_entry (seg : Segment) (hw : v.width = width * b) (data : Data payloadCount v)
    (x : RecursiveScalarCoordinates.Address width b v) :
    seg.array hw data (wireSlot seg.wire) (index hw (seg.execute x)) =
      data (wireSlot seg.wire) (index hw x) := by
  rw [← execute_exact]
  exact RecursiveScalarSchedule.run_entry (wireSlot seg.wire) seg.stages hw data x

theorem array_other (seg : Segment) (hw : v.width = width * b) (data : Data payloadCount v)
    (other : Fin payloadCount) (hne : other ≠ wireSlot seg.wire) :
    seg.array hw data other = data other :=
  RecursiveScalarSchedule.run_other (wireSlot seg.wire) seg.stages hw data other hne

theorem array_io (seg : Segment) (hw : v.width = width * b) (data : Data payloadCount v) :
    seg.array hw data io = data io :=
  array_other seg hw data io (wireSlot_ne_io seg.wire).symm

/-- One fixed clean program realizes the segment on the node bank. -/
theorem realizesNode (seg : Segment) (hw : v.width = width * b) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (aux : Tapes u prime) (data : Data payloadCount v) :
    HoareTime (seg.machine (u := u)).program
      (fun w => w = raw (bank (roles data) hs (SharedBank.empty 1 prime) aux) (seg.machine (u := u)).tapes)
      (fun w => w = raw (bank (roles (seg.array hw data)) hs (SharedBank.empty 1 prime) aux)
        (seg.machine (u := u)).tapes)
      (seg.coefficient * volume prime v) :=
  RecursiveScalarSchedule.realizes (wireSlot seg.wire) seg.stages hw hp hs hv aux data

end Segment

/-! ### Bit streams on the node bank -/

/-- Bit streams on the wires and the input/output tape's symbols. -/
def encodedBits (data : Wire → Fin (volume prime v) → ZMod 2) (inputOutput : Fin (volume prime v) → Fin 4) :
    RecursiveMixedSchedule.Data payloadCount v :=
  Fin.addCases (fun k i => SparseRoleCircuit.encode (a := 0) (data (wireEquiv k) i)) (fun _ => inputOutput)

theorem encodedBits_wire (data : Wire → Fin (volume prime v) → ZMod 2)
    (inputOutput : Fin (volume prime v) → Fin 4) (w : Wire) :
    encodedBits data inputOutput (wireSlot w) = fun i => SparseRoleCircuit.encode (a := 0) (data w i) := by
  simp [encodedBits, wireSlot]

theorem encodedBits_io (data : Wire → Fin (volume prime v) → ZMod 2)
    (inputOutput : Fin (volume prime v) → Fin 4) : encodedBits data inputOutput io = inputOutput := by
  have h : io = Fin.natAdd wireCount (0 : Fin 1) := rfl
  rw [h]
  simp only [encodedBits, Fin.addCases_right]

/-- Updating one wire's bits updates its tape. -/
theorem encodedBits_update (data : Wire → Fin (volume prime v) → ZMod 2)
    (inputOutput : Fin (volume prime v) → Fin 4) (w : Wire) (f : Fin (volume prime v) → ZMod 2) :
    encodedBits (Function.update data w f) inputOutput =
      Function.update (encodedBits data inputOutput) (wireSlot w)
        (fun i => SparseRoleCircuit.encode (a := 0) (f i)) := by
  funext k
  induction k using Fin.addCases with
  | left k =>
    by_cases hk : wireEquiv k = w
    · subst hk
      have hs : Fin.castAdd 1 k = wireSlot (wireEquiv k) := by simp [wireSlot]
      rw [hs, Function.update_self, encodedBits_wire, Function.update_self]
    · have hs : Fin.castAdd 1 k ≠ wireSlot w := by
        intro he
        apply hk
        have := Fin.castAdd_injective _ _ (he.trans rfl)
        rw [this]; simp
      rw [Function.update_of_ne hs]
      simp [encodedBits, Function.update_of_ne hk]
  | right k =>
    have hs : Fin.natAdd wireCount k ≠ wireSlot w := by
      intro he
      have hv := congrArg Fin.val he
      have hi := (wireEquiv.symm w).isLt
      simp only [wireSlot, Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    rw [Function.update_of_ne hs]
    simp [encodedBits]

/-! ### Gates -/

namespace Gate

theorem witness (g : Gate) : ∃ dst src, dst ≠ src ∧ g.scalar = ReversibleFanout.add dst src :=
  g.xor g.scalar List.mem_cons_self

/-- The gate on its wire tapes. -/
def physical (g : Gate) : PointwiseRoleGate.Gate payloadCount where
  dst := wireSlot (Classical.choose (witness g))
  src := wireSlot (Classical.choose (Classical.choose_spec (witness g)))
  distinct := wireSlot_injective.ne (Classical.choose_spec (Classical.choose_spec (witness g))).1.symm

def ops (g : Gate) : List (RoleOps.Op payloadCount) := [.xor (physical g)]

def machine (g : Gate) := RoleOpsBank.machine (u := u) (ops g)

def array (g : Gate) (data : RecursiveMixedSchedule.Data payloadCount v) := RoleOps.run (ops g) data

theorem array_other (g : Gate) (data : RecursiveMixedSchedule.Data payloadCount v)
    (other : Fin payloadCount) (hne : other ≠ (physical g).dst) : array g data other = data other := by
  simp only [array, ops, RoleOps.run, List.foldl_cons, List.foldl_nil, RoleOps.transform,
    Function.update_of_ne hne]

theorem array_io (g : Gate) (data : RecursiveMixedSchedule.Data payloadCount v) :
    array g data io = data io :=
  array_other g data io (wireSlot_ne_io _).symm

/-- On bit streams the gate is the module gate; the input/output tape is unchanged. -/
theorem array_encoded (g : Gate) (data : Wire → Fin (volume prime v) → ZMod 2)
    (inputOutput : Fin (volume prime v) → Fin 4) :
    array g (encodedBits data inputOutput) =
      encodedBits (FramedCircuit.moduleGate g.scalar data) inputOutput := by
  set dst := Classical.choose (witness g)
  set src := Classical.choose (Classical.choose_spec (witness g))
  have hspec : dst ≠ src ∧ g.scalar = ReversibleFanout.add dst src :=
    Classical.choose_spec (Classical.choose_spec (witness g))
  have hmod : FramedCircuit.moduleGate g.scalar data =
      Function.update data dst (fun i => data dst i + data src i) := by
    rw [hspec.2]
    funext w i
    simp only [FramedCircuit.moduleGate, ReversibleFanout.add]
    by_cases hw : w = dst
    · subst hw; simp
    · simp [Function.update_of_ne hw]
  rw [hmod, encodedBits_update]
  simp only [array, ops, RoleOps.run, List.foldl_cons, List.foldl_nil, RoleOps.transform, physical]
  congr 1
  funext i
  rw [encodedBits_wire, encodedBits_wire]
  exact SparseRoleCircuit.encode_add _ _

/-- One fixed machine realizes the gate on the node bank. -/
theorem realizesNode (g : Gate) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (st : Tapes 1 prime) (aux : Tapes u prime)
    (data : RecursiveMixedSchedule.Data payloadCount v) :
    HoareTime (machine (u := u) g).program
      (fun w => w = raw (bank (roles data) hs st aux) (machine (u := u) g).tapes)
      (fun w => w = raw (bank (roles (array g data)) hs st aux) (machine (u := u) g).tapes)
      (RoleOpsClean.coefficient (ops g) * volume prime v) :=
  RoleOpsBank.realizes (ops g) hs st aux hv hp data

end Gate

/-! ### Resets -/

namespace Reset

/-- Zero the wire's tape; the input/output tape is the read-only source slot. -/
def physical (r : Reset) : PointwiseRoleGate.Gate payloadCount where
  dst := wireSlot r.wire
  src := io
  distinct := (wireSlot_ne_io r.wire).symm

def ops (r : Reset) : List (RoleOps.Op payloadCount) := [.fill (physical r) (SparseRoleCircuit.encode (a := 0) 0)]

def machine (r : Reset) := RoleOpsBank.machine (u := u) (ops r)

def array (r : Reset) (data : RecursiveMixedSchedule.Data payloadCount v) := RoleOps.run (ops r) data

theorem array_io (r : Reset) (data : RecursiveMixedSchedule.Data payloadCount v) :
    array r data io = data io := by
  simp only [array, ops, RoleOps.run, List.foldl_cons, List.foldl_nil, RoleOps.transform, physical,
    Function.update_of_ne (wireSlot_ne_io r.wire).symm]

/-- On bit streams a reset is the zero stream on its wire. -/
theorem array_encoded (r : Reset) (data : Wire → Fin (volume prime v) → ZMod 2)
    (inputOutput : Fin (volume prime v) → Fin 4) :
    array r (encodedBits data inputOutput) =
      encodedBits (Function.update data r.wire 0) inputOutput := by
  rw [encodedBits_update]
  rfl

/-- One fixed machine realizes the reset on the node bank. -/
theorem realizesNode (r : Reset) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (st : Tapes 1 prime) (aux : Tapes u prime)
    (data : RecursiveMixedSchedule.Data payloadCount v) :
    HoareTime (machine (u := u) r).program
      (fun w => w = raw (bank (roles data) hs st aux) (machine (u := u) r).tapes)
      (fun w => w = raw (bank (roles (array r data)) hs st aux) (machine (u := u) r).tapes)
      (RoleOpsClean.coefficient (ops r) * volume prime v) :=
  RoleOpsBank.realizes (ops r) hs st aux hv hp data

end Reset

end
end IntegerMultBounds.MathlibTM2.M8.Machine
