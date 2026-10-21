module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemRank

/-!
# The node's data on the fibers of its role view

On a role view whose fields have `m f` coordinates of `b` digits, an address with fixed spectators
`x` and an atom state `s` (`m` coordinates of `f` atoms, refined coordinate-major) is the address
`withState x s`. The node's data represents streams on the fiber of `x` (`Represents`) when
every wire holds, at `withState x s`, the bit of its stream at `s`.

Every piece keeps the representation, as the piece acts on streams (`SemPieces.pieceSem`): an
atom segment by its twisted run (`represents_seg`, from `AtomRoleSegment.segment_twisted`), an
XOR gate and a zero fill pointwise (`represents_gate`, `represents_reset`), and a block call
whose output moves its wire by the twisted reversed pivots (`represents_call`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (index field)
open AffineFieldCoordinates (hIndex dIndex embed)
open AtomRoleSem (castE)
open NodeBank (tapes io wireSlot)
open ReversedExchange (revPivots)
open TwistedExchange (revSwaps atomRev)
open Exchange (swapOps)
open Rev (twMap twEdgeAction)

variable {m f b : ℕ} {v : Descriptor}

local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
local instance : NeZero (prime ^ b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- The atoms of a coordinate at the machine prime. -/
abbrev SA (f b : ℕ) := Fin f → ZMod (prime ^ b)

/-! ### Addresses of atom states -/

/-- The address with the spectators of `x` and the fields of the atom state `s`. -/
def withState (x : RecursiveScalarCoordinates.Address (m * f) b v) (s : Rev.Addr m (SA f b)) : RecursiveScalarCoordinates.Address (m * f) b v :=
  { x with h := AtomOps.refine s.1, d := AtomOps.refine s.2 }

/-- The atom state of an address. -/
def stateOf (x : RecursiveScalarCoordinates.Address (m * f) b v) : Rev.Addr m (SA f b) :=
  (fun i l => x.h (AtomOps.«at» i l), fun i l => x.d (AtomOps.«at» i l))

theorem withState_stateOf (x : RecursiveScalarCoordinates.Address (m * f) b v) : withState x (stateOf x) = x := by
  cases x
  simp only [withState, stateOf, RecursiveScalarCoordinates.Address.mk.injEq, true_and, and_true]
  exact ⟨refine_ext fun i l => by rw [AtomOps.refine_at], refine_ext fun i l => by rw [AtomOps.refine_at]⟩

theorem withState_withState (x : RecursiveScalarCoordinates.Address (m * f) b v) (s t : Rev.Addr m (SA f b)) :
    withState (withState x s) t = withState x t := rfl

theorem field_withState (x : RecursiveScalarCoordinates.Address (m * f) b v) (s : Rev.Addr m (SA f b)) :
    field (withState x s) ∘ castE = AtomOps.refine (embed s) := by
  funext k
  obtain ⟨c, l, rfl⟩ := exists_at k
  rw [Function.comp_apply, AtomOps.refine_at]
  induction c using Fin.addCases with
  | left i =>
    rw [AtomRoleSem.castE_h _ l (by simp), RecursiveScalarCoordinates.field_h]
    have e1 : (⟨(Fin.castAdd m i).val * f + l.val, by have := l.isLt; have := i.isLt; simp; nlinarith⟩ :
        Fin (m * f)) = AtomOps.«at» i l := Fin.ext (by simp [at_val]; ring)
    simp only [withState]
    rw [e1]
    exact (AtomOps.refine_at s.1 i l).trans (by simp only [embed, Fin.addCases_left])
  | right i =>
    rw [AtomRoleSem.castE_d _ l (by simp), RecursiveScalarCoordinates.field_d]
    have e1 : (⟨((Fin.natAdd m i).val - m) * f + l.val, by have := l.isLt; have := i.isLt; simp; nlinarith⟩ :
        Fin (m * f)) = AtomOps.«at» i l := Fin.ext (by simp [at_val]; ring)
    simp only [withState]
    rw [e1]
    exact (AtomOps.refine_at s.2 i l).trans (by simp only [embed, Fin.addCases_right])

theorem spect_withState (x : RecursiveScalarCoordinates.Address (m * f) b v) (s : Rev.Addr m (SA f b)) :
    AtomRoleSegment.spect (withState x s) = AtomRoleSegment.spect x := rfl

/-- The array index of an atom state. -/
def pos (hw : v.width = (m * f) * b) (x : RecursiveScalarCoordinates.Address (m * f) b v) (s : Rev.Addr m (SA f b)) :
    Fin (volume prime v) :=
  index hw (withState x s)

theorem pos_val (hw : v.width = (m * f) * b) (x : RecursiveScalarCoordinates.Address (m * f) b v) (s : Rev.Addr m (SA f b)) :
    (pos hw x s).val = RecursiveInterchangeLayout.index prime v x.beforeRows.val x.row.val x.before.val
      (Machine.FlatCoordinateLayout.rank (AtomOps.refine s.1)).val x.middle.val
      (Machine.FlatCoordinateLayout.rank (AtomOps.refine s.2)).val x.after.val :=
  RecursiveScalarCoordinates.index_val hw _

/-- Every index is the index of an atom state. -/
theorem pos_surjective (hw : v.width = (m * f) * b) (z : Fin (volume prime v)) :
    ∃ x s, pos hw x s = z := by
  obtain ⟨x, rfl⟩ := SegmentBits.index_surjective hw z
  exact ⟨x, stateOf x, by rw [pos, withState_stateOf]⟩

/-! ### Representation -/

variable (N : RevNetwork)

/-- The streams of the wires at the machine prime. -/
abbrev Streams' (N : RevNetwork) (f b : ℕ) := N.World ⊕ N.Temp → Rev.Streams N.width (SA f b)

/-- **The node's data represents the streams** on the fiber of `x`. -/
def Represents (hw : v.width = (N.width * f) * b) (x : RecursiveScalarCoordinates.Address (N.width * f) b v)
    (data : RecursiveMixedSchedule.Data (tapes N) v) (stored : Streams' N f b) : Prop :=
  ∀ w s, data (wireSlot N w) (pos hw x s) = SparseRoleCircuit.encode (a := 0) (stored w s)

variable {N} {hw : v.width = (N.width * f) * b} {x : RecursiveScalarCoordinates.Address (N.width * f) b v}

theorem invFun_involutive {α : Type*} [Nonempty α] {g : α → α} (h : Function.Involutive g) :
    Function.invFun g = g := by
  funext a
  have := Function.leftInverse_invFun h.injective (g a)
  rwa [h] at this

/-- A map of the fiber moving one wire's record determines its edge action. -/
theorem represents_move {data out : RecursiveMixedSchedule.Data (tapes N) v} {stored : Streams' N f b}
    (hr : Represents N hw x data stored) (w : N.World ⊕ N.Temp) (g : Rev.Addr N.width (SA f b) → _)
    (hg : Function.Bijective g) (he : ∀ s, out (wireSlot N w) (pos hw x (g s)) = data (wireSlot N w) (pos hw x s))
    (ho : ∀ k, k ≠ wireSlot N w → out k = data k) :
    Represents N hw x out (Function.update stored w (fun a => stored w (Function.invFun g a))) := by
  intro k s
  by_cases hk : k = w
  · subst k
    obtain ⟨t, rfl⟩ := hg.2 s
    rw [he, hr, Function.update_self, Function.leftInverse_invFun hg.1 t]
  · rw [ho _ ((NodeBank.wireSlot_injective N).ne hk), hr, Function.update_of_ne hk]

/-- **A segment keeps the representation**: its data moves the wire's records by the twisted run. -/
theorem represents_seg {data out : RecursiveMixedSchedule.Data (tapes N) v} {stored : Streams' N f b}
    (hr : Represents N hw x data stored) (w : N.World ⊕ N.Temp) (ops : FieldProgram N.width)
    (hb : Function.Bijective (twMap (atomScalar prime b f) (atomRev f) ops))
    (he : ∀ (s : Swap.Shear.State (Fin N.width) (Fin f → ZMod (modulus b))) (y z : RecursiveScalarCoordinates.Address (N.width * f) b v),
      AtomRoleSegment.spect z = AtomRoleSegment.spect y → field y ∘ castE = AtomOps.refine (embed s) →
      field z ∘ castE = AtomOps.refine (embed (TwistedProgram.twRun (atomRev f)
        ((ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))).map
          (AffineFieldProgram.mapOp AtomOps.scalar)) s)) →
      out (wireSlot N w) (index hw z) = data (wireSlot N w) (index hw y))
    (ho : ∀ k, k ≠ wireSlot N w → out k = data k) :
    Represents N hw x out (Function.update stored w (twEdgeAction (atomScalar prime b f) (atomRev f) ops (stored w))) :=
  represents_move hr w _ hb (fun s => he s (withState x s) _ rfl (field_withState x s) (field_withState x _)) ho

/-- **A gate keeps the representation.** -/
theorem represents_gate {data : RecursiveMixedSchedule.Data (tapes N) v} {stored : Streams' N f b}
    (hr : Represents N hw x data stored) (g : Circuit.Gate (N.World ⊕ N.Temp) (ZMod 2))
    (hg : ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src) :
    Represents N hw x (Machine.RoleOps.run (RevNode.gateOp N g) data) (FramedCircuit.moduleGate g stored) := by
  classical
  set dst := hg.choose
  set src := hg.choose_spec.choose
  have hspec : dst ≠ src ∧ g = ReversibleFanout.add dst src := hg.choose_spec.choose_spec
  have hop : RevNode.gateOp N g = [.xor ⟨wireSlot N src, wireSlot N dst,
      fun he => hspec.1 (NodeBank.wireSlot_injective N he).symm⟩] := by
    unfold RevNode.gateOp; rw [dite_eq_left_of_eq_true (eq_true hg)]
  rw [hop]
  intro w s
  simp only [Machine.RoleOps.run, List.foldl_cons, List.foldl_nil, Machine.RoleOps.transform]
  rw [FramedCircuit.moduleGate_pointwise, hspec.2, ReversibleFanout.add_run]
  by_cases hw' : w = dst
  · subst hw'
    rw [Function.update_self, Function.update_self, hr, hr, SparseRoleCircuit.encode_add]
  · rw [Function.update_of_ne ((NodeBank.wireSlot_injective N).ne hw'), Function.update_of_ne hw', hr]

/-- **A reset keeps the representation.** -/
theorem represents_reset {data : RecursiveMixedSchedule.Data (tapes N) v} {stored : Streams' N f b}
    (hr : Represents N hw x data stored) (w : N.World ⊕ N.Temp) :
    Represents N hw x (Machine.RoleOps.run [.fill ⟨io N, wireSlot N w, (NodeBank.wireSlot_ne_io N w).symm⟩
      NodeSplit.zeroBit] data) (Function.update stored w 0) := by
  intro k s
  simp only [Machine.RoleOps.run, List.foldl_cons, List.foldl_nil, Machine.RoleOps.transform]
  by_cases hk : k = w
  · subst hk
    rw [Function.update_self, Function.update_self]
    rfl
  · rw [Function.update_of_ne ((NodeBank.wireSlot_injective N).ne hk), Function.update_of_ne hk, hr]

/-- **A block call keeps the representation**, when its output moves the wire's records by the
twisted reversed pivots. -/
theorem represents_call {data : RecursiveMixedSchedule.Data (tapes N) v} {stored : Streams' N f b}
    (hr : Represents N hw x data stored) (w : N.World ⊕ N.Temp) (r : ℕ) (out : Fin (volume prime v) → Fin 4)
    (he : ∀ s, out (pos hw x s) = data (wireSlot N w) (pos hw x (revSwaps (atomRev f) (revPivots N.width r) s))) :
    Represents N hw x (Function.update data (wireSlot N w) out)
      (Function.update stored w (twEdgeAction (atomScalar prime b f) (atomRev f) (swapOps (revPivots N.width r)) (stored w))) := by
  have hinv : Function.Involutive (revSwaps (atomRev f) (revPivots N.width r) : Rev.Addr N.width (SA f b) → _) :=
    revSwaps_revPivots_invol (TwistedExchange.atomRev_atomRev f)
  have hmap : twMap (atomScalar prime b f) (atomRev f) (swapOps (revPivots N.width r)) =
      revSwaps (atomRev f) (revPivots N.width r) := twRun_swapOps _
  refine represents_move hr w (twMap (atomScalar prime b f) (atomRev f) (swapOps (revPivots N.width r)))
    (by rw [hmap]; exact hinv.bijective) (fun s => ?_) (fun k hk => Function.update_of_ne hk _ _)
  rw [Function.update_self, hmap, he, hinv]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics
