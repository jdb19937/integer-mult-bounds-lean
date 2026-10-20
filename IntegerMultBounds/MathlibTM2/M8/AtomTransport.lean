module

public import IntegerMultBounds.MathlibTM2.M8.AtomOps
public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-!
# Array transport of atom field programs

The coordinate stages move the records of an array: a stage realizes a coordinate map `g` when
the record at address `x` moves to address `g x` (`Transports`). Transports compose
(`Transports.trans`), so a list of stages, one per ordinary operation, realizes the run of the
list (`transports_run`).

For atom fields this gives the semantics of the stage-2 adapters: the stages of the refined atom
operations of a nonrecursive segment move the record of every atom state `s` to the address of
the twisted run of the segment (`atom_segment_transports`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.AtomTransport

open IntegerMultBounds.Networks
open IntegerMultBounds.Machine.FlatCoordinateLayout (index)

variable {D Q W : ℕ} [NeZero Q]

/-- The array `a'` holds the record of `a` at address `x` at address `g x`. -/
def Transports (a a' : Fin (Q ^ D * W) → Fin 4) (g : (Fin D → ZMod Q) → Fin D → ZMod Q) : Prop :=
  ∀ x j, a' (index (g x) j) = a (index x j)

theorem Transports.trans {a a' a'' : Fin (Q ^ D * W) → Fin 4} {g g' : (Fin D → ZMod Q) → Fin D → ZMod Q}
    (h : Transports a a' g) (h' : Transports a' a'' g') : Transports a a'' (g' ∘ g) :=
  fun x j => (h' (g x) j).trans (h x j)

/-- A chain of arrays, each realizing the next operation, realizes the run of the operations. -/
theorem transports_run : ∀ (ops : List (OrderedAffine.Op (Fin D) (ZMod Q)))
    (arr : ℕ → Fin (Q ^ D * W) → Fin 4),
    (∀ i (hi : i < ops.length), Transports (arr i) (arr (i + 1)) (OrderedAffine.execute ops[i])) →
    Transports (arr 0) (arr ops.length) (OrderedAffine.run ops)
  | [], _, _ => fun _ _ => rfl
  | op :: ops, arr, h => by
    have h0 := h 0 (by simp)
    have hrest := transports_run ops (fun i => arr (i + 1)) (fun i hi => by
      exact h (i + 1) (by simp only [List.length_cons]; omega))
    exact (h0.trans hrest : _)

/-- **Atom segments on the array.** The stages of the refined atom operations of a nonrecursive
segment realize, on the refined address of every atom state, the twisted run of the segment. -/
theorem atom_segment_transports {m f : ℕ}
    (ops : List (AffineFieldProgram.Op (Fin m) (ZMod Q)))
    (hn : ∀ op ∈ ops, AffineFieldCoordinates.Nonrecursive op)
    (hl : ∀ op ∈ ops, AffineFieldProgram.Legal op)
    {a a' : Fin (Q ^ ((m + m) * f) * W) → Fin 4}
    (h : Transports a a' (OrderedAffine.run ((ops.flatMap AtomOps.atomExpand).flatMap AtomOps.refined)))
    (s : Swap.Shear.State (Fin m) (Fin f → ZMod Q)) (j : Fin W) :
    a' (index (AtomOps.refine (AffineFieldCoordinates.embed
        (TwistedProgram.twRun (TwistedExchange.atomRev f)
          (ops.map (AffineFieldProgram.mapOp AtomOps.scalar)) s))) j) =
      a (index (AtomOps.refine (AffineFieldCoordinates.embed s)) j) := by
  have hd : ∀ o ∈ ops.flatMap AtomOps.atomExpand, AtomOps.Distinct o := by
    intro o ho
    obtain ⟨op, hop, ho⟩ := List.mem_flatMap.mp ho
    exact (AtomOps.atomExpand_legal op (hl op hop) o ho).2
  have hr := AtomOps.refined_atomRun _ hd (AffineFieldCoordinates.embed s)
  rw [AtomOps.atom_segment_run ops hn s] at hr
  rw [← hr]
  exact h _ j

end IntegerMultBounds.MathlibTM2.M8.AtomTransport
