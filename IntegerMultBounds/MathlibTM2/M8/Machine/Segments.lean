module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Coordinates
public import IntegerMultBounds.Machine.FlatCoordinateCleanSchedule

/-!
# Supported nonrecursive segments

A maximal run of legal nonrecursive field operations with supported coefficients compiles to one
fixed list of flat coordinate stages (`description`). One fixed clean machine executes it at
every prime-power width: the payload follows the exact reduced field-program run, the `b`/`W`
headers are kept, and every private tape ends blank (`realizes`). This is
`Shared50CleanSegments.realizes` for any width `d` and any supported segment.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.Segments

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open FlatCoordinateSchedule AffineFieldCoordinates
open ActualAffineScaling (modulus)
open Coordinates (CoeffSupported)

variable {d : ℕ}

/-- The hypotheses of one segment: legal, supported and nonrecursive operations. -/
structure Good (ops : List (AffineFieldProgram.Op (Fin d) ℚ)) : Prop where
  legal : ∀ op ∈ ops, AffineFieldProgram.Legal op
  supported : ∀ op ∈ ops, CoeffSupported op
  nonrecursive : ∀ op ∈ ops, Nonrecursive op

def description (ops : List (AffineFieldProgram.Op (Fin d) ℚ)) (h : Good ops) :
    List (FlatCoordinateSchedule.Op (d + d)) :=
  ofList (ops.flatMap expand) (by
    intro out hout
    obtain ⟨op, hop, he⟩ := List.mem_flatMap.mp hout
    exact Coordinates.expanded_supported op (h.legal op hop) (h.supported op hop)
      (h.nonrecursive op hop) out he)

theorem description_rational (ops : List (AffineFieldProgram.Op (Fin d) ℚ)) (h : Good ops) :
    (description ops h).map FlatCoordinateSchedule.Op.rational = ops.flatMap expand :=
  rational_ofList _ _

theorem description_actions (ops : List (AffineFieldProgram.Op (Fin d) ℚ)) (h : Good ops) (b : ℕ) :
    (description ops h).map (fun op => op.action b) =
      (ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))).flatMap expand := by
  change (description ops h).map
    ((OrderedAffine.mapOp (Swap.Modular.ratMod (modulus b))) ∘ FlatCoordinateSchedule.Op.rational) = _
  rw [← List.map_map, description_rational, List.map_flatMap, List.flatMap_map]
  congr 1
  funext op
  exact expand_map _ (Swap.Modular.ratMod_one _) (by simp [Swap.Modular.ratMod]) op

theorem nonrecursive_map (ops : List (AffineFieldProgram.Op (Fin d) ℚ)) (h : Good ops) (b : ℕ) :
    ∀ op ∈ ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b))), Nonrecursive op := by
  intro op hop
  obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hop
  have hh := h.nonrecursive src hsrc
  cases src <;> exact hh

/-- Every record symbol follows the exact field-program run through the whole segment. -/
theorem array_entry (ops : List (AffineFieldProgram.Op (Fin d) ℚ)) (h : Good ops)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array (d + d) b W)
    (s : Swap.Shear.State (Fin d) (ZMod (modulus b))) (j : Fin W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    FlatCoordinateInitializedSchedule.array (description ops h) b W hW a
      (FlatCoordinateLayout.index (embed (AffineFieldProgram.run
        (ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) s)) j) =
      a (FlatCoordinateLayout.index (embed s) j) := by
  dsimp only
  have hh := FlatCoordinateInitializedSchedule.array_entry (description ops h) b W hW a (embed s) j
  rw [description_actions, segment_run _ (nonrecursive_map ops h b)] at hh
  exact hh

/-- One fixed clean machine implements a supported segment at every width. Its complete output
bank is directly reusable as the next call's input. -/
theorem realizes (ops : List (AffineFieldProgram.Op (Fin d) ℚ)) (h : Good ops)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array (d + d) b W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    let stages := description ops h
    HoareTime (FlatCoordinateCleanSchedule.program stages)
      (fun v => v = SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common a)
        (FlatCoordinateCleanSchedule.tapeCount stages))
      (fun v => v = SharedBankStageInput.raw
        (FlatCoordinateShiftSharedBank.common (FlatCoordinateInitializedSchedule.array stages b W hW a))
        (FlatCoordinateCleanSchedule.tapeCount stages) ∧
        ∀ (s : Swap.Shear.State (Fin d) (ZMod (modulus b))) (j : Fin W),
          FlatCoordinateInitializedSchedule.array stages b W hW a
            (FlatCoordinateLayout.index (embed (AffineFieldProgram.run
              (ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) s)) j) =
                a (FlatCoordinateLayout.index (embed s) j))
      (FlatCoordinateCleanSchedule.constant stages * ((modulus b) ^ (d + d) * W)) := by
  dsimp only
  apply (FlatCoordinateCleanSchedule.realizes (description ops h) b W hW a).consequence
    (fun _ h => h) ?_ le_rfl
  intro v hv
  exact ⟨hv.1, array_entry ops h b W hW a⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.Segments
