module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopBound

/-! Linear volume bounds for actual top-level control stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node

/-- Both full-array phase scans are linear in actual bit volume once address
length fits the coefficient payload. Configuration reads stay explicit. -/
theorem compactTopPhaseSCost_linear (cfg : List ℕ) (N R r w K ρ o D : ℕ)
    (hR : 1 ≤ R) (hrw : 1 ≤ r*w) (hN : N ≤ r*w)
    (hρo : ρ+o ≤ N) (hDK : D*K ≤ N) (hD : D ≤ N) :
    compactTopPhaseSCost cfg N R r w K ρ o D ≤
      3*topGetCost cfg + 512*(R*2^N*(r*w)) := by
  have hpow : 1 ≤ 2^N := Nat.one_le_pow N 2 (by decide)
  have hstock : 1 ≤ R*2^N := by nlinarith
  have hV : r*w ≤ R*2^N*(r*w) := Nat.le_mul_of_pos_left _ (by omega)
  have hNstock : R*2^N*N ≤ R*2^N*(r*w) := Nat.mul_le_mul_left _ hN
  have hstockV : R*2^N ≤ R*2^N*(r*w) := Nat.le_mul_of_pos_right _ hrw
  unfold compactTopPhaseSCost
  nlinarith only [hρo,hDK,hD,hN,hV,hNstock,hstockV,hstock]

/-- The final unit multiplication is linear in stream volume, with configuration
reads and the unary dimension header charged explicitly. -/
theorem compactTopUnitSCost_linear (cfg : List ℕ) (R N r w D : ℕ)
    (hw : 1 ≤ w) :
    compactTopUnitSCost cfg R N r w D ≤
      topGetCost cfg + 16*(R*2^N*(r*w)) + 6*D + 17 := by
  have hcoeff : R*2^N*r ≤ R*2^N*r*w := Nat.le_mul_of_pos_right _ hw
  unfold compactTopUnitSCost compactTopUnitCost
  nlinarith only [hcoeff, Nat.zero_le (R*2^N*r*w)]

end IntegerMultBounds.MathlibTM2.Cost
