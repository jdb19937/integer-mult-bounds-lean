module

public import IntegerMultBounds.MathlibTM2.Routing.WordRepeatNumeral
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScale
public import IntegerMultBounds.MathlibTM2.Routing.RepeatedTemporaryMask

/-! Numeric meaning and fit of low-zero padding, including the exact shifted
value required for R2's temporary classifier mask. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem binSyms_lowPad {A : ℕ} (e W x : ℕ) (hx : x < 2 ^ W) :
    binSyms (A := A) e 0 ++ binSyms W x = binSyms (e + W) (2 ^ e * x) := by
  have hb := binaryBits_value_repr (List.replicate e false ++ binBits W x)
  rw [List.length_append, List.length_replicate, length_binBits,
    binaryScale_value, binaryCanonical_value_binBits W x hx] at hb
  rw [IntegerMultBounds.MathlibTM2.Node.binSyms_zero_right]
  simp only [binSyms_eq, hb, List.map_append, List.map_replicate]

theorem lowPadValue_lt (e W x : ℕ) (hx : x < 2 ^ W) : 2 ^ e * x < 2 ^ (e + W) := by
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_left hx (Nat.two_pow_pos e)

theorem temporaryMask_shiftedWord {A : ℕ} (p : Par) (hG : 0 < p.G) (hGK : p.G ≤ p.K) :
    binSyms (A := A) (p.ρ + 1) 0 ++
      wordCopies (binSyms p.K (maskVal p.G id)) p.n =
      binSyms (p.ρ + 1 + p.n * p.K) (IntegerMultBounds.MathlibTM2.Node.mAV p) := by
  rw [temporaryRepeatedWord p.K p.G p.n hGK]
  rw [binSyms_lowPad _ _ _ (repeatBlockValue_lt _ _ _ (temporaryBlockValue_lt p.K p.G hGK))]
  rw [temporaryMask_repeatBlocks p hG]

end IntegerMultBounds.MathlibTM2.Routing
