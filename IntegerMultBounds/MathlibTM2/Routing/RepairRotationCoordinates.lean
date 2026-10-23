module

public import IntegerMultBounds.MathlibTM2.Routing.RepairKeyCoordinates

/-! Sparse coordinate specifications for every actual selective rotation.
Positions and source formulas are the ones used by the existing R2 patterns. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (X : ℕ)

def repairRotationSlots : Off → ℕ
  | .A => p.n * p.G
  | _ => p.n

def repairRotationPosition : Off → ℕ → ℕ
  | .A => posA p
  | .Z => posS p
  | _ => posC p

def repairRotationSources (hG : 0 < p.G) (hK : 0 < p.K) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) : (off : Off) → Fin 2 →
      Fin (repairRotationSlots p off) → Option (Fin (selectiveSourceWidth p X off))
  | .A => aSources p hG active p.wc 0 (by dsimp only [selectiveSourceWidth]; omega) (by dsimp only [selectiveSourceWidth]; omega)
  | .Z => ![fun c => if active c then some (controlWire p hG p.wc (by dsimp only [selectiveSourceWidth]; omega) c) else none, fun _ => none]
  | .Y => ![fun c => some (targetWire p hK 0 (by dsimp only [selectiveSourceWidth]; omega) c), fun _ => none]
  | .YZ => yzSources p hG hK active (p.wy + p.wc) 0 (by dsimp only [selectiveSourceWidth]; omega) (by dsimp only [selectiveSourceWidth]; omega)
  | .X => ![fun c => some (sourceWire p X (s c)), fun _ => none]

theorem repairRotationPattern_sparse (hG : 0 < p.G) (hK : 0 < p.K) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) (off : Off) (k : Fin 2) :
    selectivePatterns p X hG hK active s off k =
      sparsePattern (repairRotationPosition p off) (repairRotationSources p X hG hK active s off k) := by
  cases off <;> rfl

theorem repairRotationPosition_mono (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K) (off : Off) :
    StrictMono (repairRotationPosition p off) := by
  cases off with
  | A => exact posA_mono hG hGK
  | Z => exact posS_mono hK
  | Y => exact posC_mono hG
  | YZ => exact posC_mono hG
  | X => exact posC_mono hG

theorem repairRotationPosition_bound (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (off : Off) : ∀ j < repairRotationSlots p off, repairRotationPosition p off j < selectiveTargetWidth p off := by
  cases off with
  | A => exact fun j hj => posA_lt hG hGK hj
  | Z => exact repairKeyCoordinates_bound p hK
  | Y => exact fun j hj => Nat.mul_lt_mul_of_pos_right hj hG
  | YZ => exact fun j hj => Nat.mul_lt_mul_of_pos_right hj hG
  | X => exact fun j hj => Nat.mul_lt_mul_of_pos_right hj hG

def repairRotationCoordinates (hG : 0 < p.G) (hK : 0 < p.K) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) (off : Off) (k : Fin 2) :=
  sparseCoordinateClose (selectiveTargetWidth p off)
    (sparsePatternCoordinates (N := selectiveTargetWidth p off) (repairRotationPosition p off)
      (repairRotationSources p X hG hK active s off k))

theorem repairRotationCoordinates_indices (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (off : Off) (k : Fin 2)
    (L : ℕ) (hwidth : 0 < selectiveTargetWidth p off) (hfit : selectiveTargetWidth p off < 2 ^ L) :
    SparseSelectorRun.expand (sparseCoordinateRuns 0 (repairRotationCoordinates p X hG hK active s off k)) =
      (repairDescriptorIndices p X hG hK active s (some (off, k))).reverse := by
  change _ = (List.ofFn (patternIndex (selectivePatterns p X hG hK active s off k))).reverse
  rw [repairRotationPattern_sparse]
  exact sparsePatternComplete_indices L hwidth hfit _ (repairRotationPosition_mono p hG hK hGK off) _
    (repairRotationPosition_bound p hG hK hGK off)

theorem repairRotationCoordinates_ready (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (off : Off) (k : Fin 2)
    (L : ℕ) (hwidth : 0 < selectiveTargetWidth p off) (hfit : selectiveTargetWidth p off < 2 ^ L) :
    SparseCoordinatesReady L 0 (sparseCoordinateValues (repairRotationCoordinates p X hG hK active s off k)) :=
  sparseCoordinateClose_ready L _ hwidth hfit _
    (sparsePatternCoordinates_ordered _ (repairRotationPosition_mono p hG hK hGK off) _
      (repairRotationPosition_bound p hG hK hGK off))
    (sparsePatternCoordinates_bound _ _ (repairRotationPosition_bound p hG hK hGK off))

theorem repairRotationCoordinates_length (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (off : Off) (k : Fin 2) :
    (repairRotationCoordinates p X hG hK active s off k).length ≤ repairRotationSlots p off + 1 := by
  have hh := sparseCoordinateClose_length (selectiveTargetWidth p off)
    (sparsePatternCoordinates (N := selectiveTargetWidth p off) (repairRotationPosition p off)
      (repairRotationSources p X hG hK active s off k))
  simpa only [repairRotationCoordinates, sparsePatternCoordinates, List.length_reverse, List.length_ofFn] using hh

end IntegerMultBounds.MathlibTM2.Routing
