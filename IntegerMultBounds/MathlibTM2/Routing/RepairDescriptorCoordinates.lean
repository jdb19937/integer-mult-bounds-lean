module

public import IntegerMultBounds.MathlibTM2.Routing.RepairRotationCoordinates
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactPattern

/-! One coordinate interface for all eleven actual repair descriptors. The
executed compiler's ordering and readiness conditions follow from these specs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def repairDescriptorCoordinates : (key : RepairDescriptorKey) →
    List (ℕ × Fin (repairCompactSourceWidth p X key + 1))
  | none => repairKeyCoordinates p X active s
  | some (off, k) => repairRotationCoordinates p X hG hK active s off k

def repairDescriptorCoordinateSlots : RepairDescriptorKey → ℕ
  | none => p.n
  | some (off, _) => repairRotationSlots p off

theorem repairDescriptorCoordinates_ready (hGK : p.G < p.K) (key : RepairDescriptorKey)
    (L : ℕ) (hwidth : 0 < repairCompactRows p key) (hfit : repairCompactRows p key < 2 ^ L) :
    SparseCoordinatesReady L 0 (sparseCoordinateValues (repairDescriptorCoordinates p X hG hK active s key)) := by
  cases key with
  | none => exact repairKeyCoordinates_ready p X active s hK L hwidth hfit
  | some pair =>
    obtain ⟨off, k⟩ := pair
    exact repairRotationCoordinates_ready p X hG hK hGK active s off k L hwidth hfit

theorem repairDescriptorCoordinates_indices {A : ℕ} (hGK : p.G < p.K) (key : RepairDescriptorKey)
    (L : ℕ) (hwidth : 0 < repairCompactRows p key) (hfit : repairCompactRows p key < 2 ^ L) :
    (sourceTable (SparseSelectorRun.expand (sparseCoordinateRuns 0
      (repairDescriptorCoordinates p X hG hK active s key))).reverse).flatten.map
        (IntegerMultBounds.bitSymbol (a := A)) =
      repairDescriptorWord p X hG hK active s key := by
  cases key with
  | none =>
    have hi := repairKeyCoordinates_indices p X active s hG hK L hwidth hfit
    dsimp only [repairDescriptorCoordinates, repairCompactSourceWidth]
    dsimp only [repairDescriptorIndices, repairDescriptorWidth] at hi
    rw [hi, List.reverse_reverse]
    exact repairDescriptorIndices_word p X hG hK active s none
  | some pair =>
    obtain ⟨off, k⟩ := pair
    have hi := repairRotationCoordinates_indices p X hG hK hGK active s off k L hwidth hfit
    dsimp only [repairDescriptorCoordinates, repairCompactSourceWidth]
    dsimp only [repairDescriptorIndices, repairDescriptorWidth] at hi
    rw [hi, List.reverse_reverse]
    exact repairDescriptorIndices_word p X hG hK active s (some (off, k))

theorem repairDescriptorCoordinates_dense_length (hGK : p.G < p.K) (key : RepairDescriptorKey)
    (L : ℕ) (hwidth : 0 < repairCompactRows p key) (hfit : repairCompactRows p key < 2 ^ L) :
    (SparseSelectorRun.expand (sparseCoordinateRuns 0
      (repairDescriptorCoordinates p X hG hK active s key))).length = repairCompactRows p key := by
  cases key with
  | none =>
    have hi := congrArg List.length (repairKeyCoordinates_indices p X active s hG hK L hwidth hfit)
    dsimp only [repairDescriptorIndices, repairDescriptorWidth] at hi
    simpa only [repairDescriptorCoordinates, List.length_reverse,
      List.length_ofFn, repairCompactRows, repairCompactSourceWidth] using hi
  | some pair =>
    obtain ⟨off, k⟩ := pair
    have hi := congrArg List.length (repairRotationCoordinates_indices p X hG hK hGK active s off k L hwidth hfit)
    dsimp only [repairDescriptorIndices, repairDescriptorWidth] at hi
    simpa only [repairDescriptorCoordinates, List.length_reverse,
      List.length_ofFn, repairCompactRows, repairCompactSourceWidth] using hi

theorem repairDescriptorCoordinates_length (key : RepairDescriptorKey) :
    (repairDescriptorCoordinates p X hG hK active s key).length ≤ repairDescriptorCoordinateSlots p key + 1 := by
  cases key with
  | none =>
    dsimp only [repairCompactSourceWidth]
    have hh := sparseCoordinateClose_length p.wy
      (sparsePatternCoordinates (N := p.wy) (posS p) (selectiveKeySources p X active s))
    simpa only [repairDescriptorCoordinates, repairKeyCoordinates, sparsePatternCoordinates,
      List.length_reverse, List.length_ofFn, repairDescriptorCoordinateSlots] using hh
  | some pair =>
    obtain ⟨off, k⟩ := pair
    exact repairRotationCoordinates_length p X hG hK active s off k

end
end IntegerMultBounds.MathlibTM2.Routing
