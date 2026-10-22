module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveLayout
public import IntegerMultBounds.MathlibTM2.Routing.HeaderOffsets

/-!
# Actual descriptor tables for every selective rotation

Each offset uses a suffix of the same five-field bank. The source-load descriptor
reads the actual physical source positions, in the requested order. Header widths,
relative windows and target widths are explicit and charged by `HeaderRot`.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (X : ℕ)

def selectiveTgt : Off → Fin 5
  | .A | .Z => 1
  | _ => 0

def selectiveTargetWidth : Off → ℕ
  | .A | .Z => p.wy
  | _ => p.wc

def selectiveSourceWidth : Off → ℕ
  | .A | .Z => 2 * p.wc + X
  | _ => p.wy + 2 * p.wc + X

def selectiveStart (off : Off) : ℕ :=
  fieldOff (selectiveLen p X) (selectiveTgt off) + (selectiveLen p X) (selectiveTgt off)

def selectiveGate : Off → Bool → Bool → Bool
  | .A => Bool.and
  | .YZ => Bool.xor
  | _ => fun a _ => a

/-- Both descriptor words for each actual rotation. -/
def selectivePatterns (hG : 0 < p.G) (hK : 0 < p.K) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) :
    (off : Off) → Fin 2 → Fin (selectiveTargetWidth p off) → Option (Fin (selectiveSourceWidth p X off))
  | .A => aPatterns (W := 2 * p.wc + X) p hG active p.wc 0 (by omega) (by omega)
  | .Z => zPatterns (W := 2 * p.wc + X) p hG active p.wc (by omega)
  | .Y => yPatterns (W := p.wy + 2 * p.wc + X) p hK 0 (by omega)
  | .YZ => yzPatterns (W := p.wy + 2 * p.wc + X) p hG hK active (p.wy + p.wc) 0 (by omega) (by omega)
  | .X => plainPatterns (posC p) (fun c => some (sourceWire p X (s c)))

theorem selectiveTarget_len (off : Off) :
    selectiveLen p X (selectiveTgt off) = selectiveTargetWidth p off := by
  cases off <;> rfl

theorem selectiveHeader_width (off : Off) :
    ((higherFields (selectiveTgt off)).map (selectiveLen p X)).sum = selectiveSourceWidth p X off := by
  cases off <;> first | exact selectiveHeader_y p X | exact selectiveHeader_b p X

/-- Offsets of the actual instruction semantics, including current-state sources. -/
def selectiveOffset (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (off : Off) (i : ℕ) : ℕ :=
  match off with
  | .X => casm p.G p.n (slotPhysicalRead s (selectiveView p X i).y (selectiveView p X i).x)
  | off => off.eval p (maskedView p active (selectiveView p X i))

/-- The concrete descriptor interpreters compute exactly the actual rank offsets. -/
theorem selectivePatterns_offset (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (off : Off) (i : ℕ) :
    headerOffset (selectiveStart p X off) (selectiveGate off)
      (selectivePatterns p X hG hK active s off) i = selectiveOffset p X active s off i := by
  have ht : window 0 p.wc ((i / 2 ^ (p.wc + p.wy)) % 2 ^ (2 * p.wc + X)) =
      digit (selectiveLen p X) 2 i := by
    simpa [selectiveLen] using headerWindow (selectiveLen p X) 2 (p.wc + p.wy) 0
      (2 * p.wc + X) i (by simp [selectiveFieldOff]) (by simp [selectiveLen]; omega)
  have hu : window p.wc p.wc ((i / 2 ^ (p.wc + p.wy)) % 2 ^ (2 * p.wc + X)) =
      digit (selectiveLen p X) 3 i := by
    simpa [selectiveLen] using headerWindow (selectiveLen p X) 3 (p.wc + p.wy) p.wc
      (2 * p.wc + X) i (by simp [selectiveFieldOff]) (by simp [selectiveLen]; omega)
  have hy : window 0 p.wy ((i / 2 ^ p.wc) % 2 ^ (p.wy + 2 * p.wc + X)) =
      digit (selectiveLen p X) 1 i := by
    simpa [selectiveLen] using headerWindow (selectiveLen p X) 1 p.wc 0
      (p.wy + 2 * p.wc + X) i (by simp [selectiveFieldOff]) (by simp [selectiveLen]; omega)
  have hu' : window (p.wy + p.wc) p.wc ((i / 2 ^ p.wc) % 2 ^ (p.wy + 2 * p.wc + X)) =
      digit (selectiveLen p X) 3 i := by
    simpa [selectiveLen] using headerWindow (selectiveLen p X) 3 p.wc (p.wy + p.wc)
      (p.wy + 2 * p.wc + X) i (by simp [selectiveFieldOff]; omega) (by simp [selectiveLen]; omega)
  have hstart (o : Off) : selectiveStart p X o =
      (match o with | .A | .Z => p.wc + p.wy | _ => p.wc) := by
    cases o <;> simp only [selectiveStart, selectiveTgt] <;>
      rw [selectiveFieldOff] <;> simp [selectiveLen]
  cases off <;> rw [hstart] <;>
    dsimp only [selectivePatterns, selectiveGate, selectiveTargetWidth, selectiveSourceWidth]
  · rw [headerOffset, aPatterns_eq p hG hGK, ht, hu]
    rfl
  · rw [headerOffset, zPatterns_eq p hG hK, hu]
    rfl
  · rw [headerOffset, yPatterns_eq p hG hK, hy]
    rfl
  · rw [headerOffset, yzPatterns_eq p hG hK, hy, hu']
    rfl
  · change headerOffset p.wc (fun a _ => a)
      (plainPatterns (L := p.wc) (posC p) (fun c => some (sourceWire p X (s c)))) i = _
    rw [sourceHeaderOffset_eq p hG]
    unfold selectiveOffset placeVal casm
    apply Finset.sum_congr rfl
    intro c hc
    have hc' := Finset.mem_range.mp hc
    simp only [dite_eq_left hc', slotPhysicalRead]
    rw [sourceWire_bit]
    simp [posC]

end IntegerMultBounds.MathlibTM2.Routing
