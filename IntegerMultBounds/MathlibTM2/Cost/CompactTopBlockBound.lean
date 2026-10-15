module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopRecordBound

/-! Complete padded-piece block overhead, including metadata reshaping, row
padding, every record/control operation, and cleanup. Recursive calls remain
separately charged by the exact top-cost decomposition. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

/-- All nonrecursive block work is bounded by padded bit volume and explicit
piece-record/header overhead. The only piece premise is actual validity. -/
theorem compactTopBlockCost_control {ds : ComplexFramedExecution.Directions}
    (cfg : List ℕ) (K n a r w R R₂ : ℕ) (pcs : List TopPc)
    (hK : 1≤K) (hr : 1≤r) (hw : 1≤w) (hR : 1≤R)
    (hcap : 2^a*R≤R₂) (hpcs : ∀ pc∈pcs,pc.Ok ds K n w R₂) :
    compactTopBlockCost cfg K n a r w R R₂ (fun _ => 0) pcs ≤
      512*(R₂*(2^n*r*w))+8*topGetCost cfg+
        pcs.length*(topGetCost cfg+32*n+2*R₂+32)+4 := by
  have hrw : 1≤r*w := Nat.mul_le_mul hr hw
  have hL : 1≤2^n*r*w := Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow n 2 (by decide)) hr) hw
  have hpow : 2^a≤R₂ := (Nat.le_mul_of_pos_right _ hR).trans hcap
  have hsmall : 2^(n+a)*(r*w)≤R₂*(2^n*r*w) := by
    have hm := Nat.mul_le_mul_right (2^n*(r*w)) hpow
    rw [pow_add]
    nlinarith only [hm]
  have hinput : R*2^a*2^n*r*w≤R₂*(2^n*r*w) := by
    have hm := Nat.mul_le_mul_right (2^n*r*w) hcap
    nlinarith only [hm]
  have hfull : R₂*2^n*r*w≤R₂*(2^n*r*w) := by simp only [Nat.mul_assoc,le_refl]
  have hdown := compactTopDownCost_linear cfg n a r w hrw
  have hup := compactTopUpCost_linear cfg n a r w hrw
  have hpad := compactTopPadCost_linear cfg a R R₂ (2^n*r*w)
    (R*2^a*2^n*r*w) hR hL hcap hinput
  have hunpad := compactTopUnpadCost_linear cfg a R R₂ (2^n*r*w)
    (R₂*2^n*r*w) hR hL hcap hfull
  have hdispatch := compactTopPcsCost_control cfg pcs hK hpcs
  have hrecord := compactTopPcRecLen_control pcs hK hpcs
  unfold compactTopBlockCost
  nlinarith only [hdown,hup,hpad,hunpad,hdispatch,hrecord,hsmall,
    Nat.zero_le (R₂*(2^n*r*w)),Nat.zero_le (topGetCost cfg),Nat.zero_le (pcs.length*n)]

end IntegerMultBounds.MathlibTM2.Cost
