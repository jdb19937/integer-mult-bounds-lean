module

public import IntegerMultBounds.MathlibTM2.Node.CompactSlotXorPasses

/-!
# The bound on the exceptional addresses of the compact program

`cxBad d` counts the addresses the compact slot XOR repairs. Through `cbad_iff_badE` and
`cbad_iff_badL` it is the exceptional set of the layer, bounded by `card_badE_le` and
`card_badL_le`: at most `nn · (2 / 2^G + 8 · 2^G / 2^K) · M` addresses.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor
  IntegerMultBounds.MathlibTM2.Layer.CompactXor

namespace CxD

variable (d : CxD)

/-- The size `M = R · 2^n` as a real number. -/
lemma cast_M : (d.M : ℝ) = d.R * 2 ^ d.n := by
  show ((d.R * 2 ^ d.n : ℕ) : ℝ) = _
  push_cast
  ring

/-- The exceptional addresses are at most `nn · (2 / 2^G + 8 · 2^G / 2^K) · M`. -/
theorem cxBad_le (hv : d.Valid) :
    (cxBad d : ℝ) ≤ d.nn * (2 / 2 ^ d.G + 8 * 2 ^ d.G / 2 ^ d.K) * d.M := by
  classical
  unfold cxBad
  rw [d.cast_M]
  by_cases hxy : d.x < d.y
  · rw [decide_eq_true hxy]
    calc (Fintype.card {j : Fin d.M //
            CBad d.len11 true CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn j} : ℝ)
        = Fintype.card {a : Fin (d.R * 2 ^ d.n) // BadL d.len12 CxD.fU.castSucc CxD.fT.castSucc
            d.fY.castSucc d.K d.ρ d.G d.nn a} := by
          congr 1
          exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => d.cbad_iff_badL a)
      _ ≤ d.nn * (2 / 2 ^ d.G + 8 * 2 ^ d.G / 2 ^ d.K) * (d.R * 2 ^ d.n) :=
          card_badL_le d.len12 (d.layL hv hxy)
  · rw [decide_eq_false hxy]
    calc (Fintype.card {j : Fin d.M //
            CBad d.len11 false CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn j} : ℝ)
        = Fintype.card {a : Fin (d.R * 2 ^ d.n) // BadE d.len12 CxD.fT.castSucc
            d.fY.castSucc d.K d.ρ d.G d.nn a} := by
          congr 1
          exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => d.cbad_iff_badE a)
      _ ≤ d.nn * (1 / 2 ^ d.G + 8 * 2 ^ d.G / 2 ^ d.K) * (d.R * 2 ^ d.n) :=
          card_badE_le d.len12 (d.layE hv hxy)
      _ ≤ d.nn * (2 / 2 ^ d.G + 8 * 2 ^ d.G / 2 ^ d.K) * (d.R * 2 ^ d.n) := by
          gcongr
          norm_num

end CxD

end IntegerMultBounds.MathlibTM2.Node
