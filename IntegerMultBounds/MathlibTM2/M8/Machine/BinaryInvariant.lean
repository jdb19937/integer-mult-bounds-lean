module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ChildPermutation

/-!
# Binary wire tapes at piece boundaries

At every piece boundary every wire tape holds bits and the input/output tape is blank (`Ready`),
as `Shared50RecursiveBinaryInvariant` states for Shared50. Every piece kind keeps it: segments,
gates, resets (`step`, `run`) and child calls (`child`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInvariant

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveMixedSchedule (Data)

variable [Net] {b : ℕ} {v : Descriptor}

local instance : NeZero (prime ^ b) := ⟨ne_of_gt (pow_pos Shared50ModularControl.prime_prime.pos _)⟩

/-- Bits on every wire tape and a blank input/output tape. -/
def Ready (data : Data payloadCount v) : Prop :=
  ∃ bits : Wire → Fin (volume prime v) → ZMod 2, data = encodedBits bits (fun _ => blank)

theorem of_encoded (bits : Wire → Fin (volume prime v) → ZMod 2) :
    Ready (encodedBits bits (fun _ => blank)) := ⟨bits, rfl⟩

theorem io_blank {data : Data payloadCount v} (hr : Ready data) : data io = fun _ => blank := by
  obtain ⟨bits, rfl⟩ := hr
  exact encodedBits_io _ _

theorem cells {data : Data payloadCount v} (hr : Ready data) (w : Wire) (z : Fin (volume prime v)) :
    ∃ bit : ZMod 2, data (wireSlot w) z = SparseRoleCircuit.encode (a := 0) bit := by
  obtain ⟨bits, rfl⟩ := hr
  exact ⟨bits w z, by rw [encodedBits_wire]⟩

/-- Reconstruct the bit arrays from encoded cells. -/
theorem of_cells (data : Data payloadCount v)
    (hc : ∀ w z, ∃ bit : ZMod 2, data (wireSlot w) z = SparseRoleCircuit.encode (a := 0) bit)
    (hi : data io = fun _ => blank) : Ready data := by
  classical
  refine ⟨fun w z => Classical.choose (hc w z), ?_⟩
  funext k z
  induction k using Fin.addCases with
  | left k =>
    have he := Classical.choose_spec (hc (wireEquiv k) z)
    have hs : Fin.castAdd 1 k = wireSlot (wireEquiv k) := by simp [wireSlot]
    rw [hs, encodedBits_wire]
    exact he
  | right k =>
    have hk : Fin.natAdd wireCount k = io := by
      rw [show k = 0 from Subsingleton.elim _ _]; rfl
    rw [hk, encodedBits_io]
    exact congrFun hi z

/-- Every piece keeps bits on the wires. -/
theorem step (hw : v.width = width * b) (child : Transport.Child v) (hc : Transport.ChildSpec hw child)
    (p : Piece) (data : Data payloadCount v) (hr : Ready data) :
    Ready (Transport.step hw child p data) := by
  obtain ⟨bits, rfl⟩ := hr
  apply of_cells
  · intro w z
    obtain ⟨x, rfl⟩ := RecursiveScalarIndex.surjective (v := v) hw z
    have he := Transport.represents_step hw child hc p x (encodedBits bits (fun _ => blank))
      (Transport.fiber hw bits x) (Transport.represents_encoded hw bits (fun _ => blank) x)
    exact ⟨Semantics.piece b p (Transport.fiber hw bits x) w (x.h, x.d), he w (x.h, x.d)⟩
  · rw [Transport.step_io hw child hc, encodedBits_io]

theorem run (hw : v.width = width * b) (child : Transport.Child v) (hc : Transport.ChildSpec hw child)
    (ps : List Piece) (data : Data payloadCount v) (hr : Ready data) :
    Ready (Transport.run hw child ps data) := by
  induction ps generalizing data with
  | nil => exact hr
  | cons p ps ih => exact ih _ (step hw child hc p data hr)

theorem child (hw : v.width = width * b) (w : Wire) (i j : Fin width)
    (data : Data payloadCount v) (hr : Ready data) :
    Ready (ChildPermutation.child hw w i j data) := by
  obtain ⟨bits, rfl⟩ := hr
  rw [ChildPermutation.child_encoded]
  exact ⟨_, rfl⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInvariant
