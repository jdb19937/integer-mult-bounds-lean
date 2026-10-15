module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopControlVolume
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopPieceCount

/-! Absorb complete actual top controls into any fixed positive dimension
power. Every constant is rounded upward to a power of two. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
noncomputable section

def compactTopCountConst (lam : ℝ) : ℝ := compactLayerDyadic (3+1/(lam*Real.log (m:ℝ)))

/-- Actual records, including their loop sentinel, fit any positive dimension
power with a fixed dyadic coefficient. -/
theorem compactTopPcs_length_power (d g K D o R₂ : ℕ) (hd : 1≤d) (hD : D≤d)
    {lam : ℝ} (hlam : 0<lam) :
    (((compactTopPcs d g K D o R₂).length+1:ℕ):ℝ) ≤ compactTopCountConst lam*(d:ℝ)^lam := by
  have hdd : (1:ℝ)≤d := by exact_mod_cast hd
  have hm : (1:ℝ)<m := by exact_mod_cast one_lt_m
  have hlog := IntegerMultBounds.MathlibTM2.Layer.Recurrence.one_add_logb_le hm hdd hlam
  have hpow := Real.one_le_rpow hdd hlam.le
  have hlen := compactTopPcs_length_log d g K D o R₂ hd hD
  have hbound : (((compactTopPcs d g K D o R₂).length+1:ℕ):ℝ) ≤
      (3+1/(lam*Real.log (m:ℝ)))*(d:ℝ)^lam := by
    rw [Nat.cast_add,Nat.cast_one]
    have htwo : (2:ℝ)≤2*(d:ℝ)^lam := by linarith only [hpow]
    calc
      ((compactTopPcs d g K D o R₂).length:ℝ)+1 ≤ (2+Real.logb (m:ℝ) d)+1 := add_le_add hlen (le_refl 1)
      _ = 2+(1+Real.logb (m:ℝ) d) := by ring
      _ ≤ 2+(1+1/(lam*Real.log (m:ℝ)))*(d:ℝ)^lam := add_le_add (le_refl 2) hlog
      _ ≤ 2*(d:ℝ)^lam+(1+1/(lam*Real.log (m:ℝ)))*(d:ℝ)^lam := add_le_add htwo (le_refl _)
      _ = (3+1/(lam*Real.log (m:ℝ)))*(d:ℝ)^lam := by ring
  exact hbound.trans (mul_le_mul_of_nonneg_right (compactLayerDyadic_le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Complete actual top control work, from the concrete serialized reserved
pieces, costs at most a fixed dyadic coefficient times padded volume and any
positive dimension power. No control-cost or record-count premise remains. -/
theorem compactTopControlCost_power {ds : ComplexFramedExecution.Directions}
    (d g K D o R₂ w w' s n a R r ρ q aT : ℕ)
    (hd : 1≤d) (hD : D≤d) {lam : ℝ} (hlam : 0<lam)
    (hR : 1≤R) (hr : 1≤r) (hw' : 1≤w') (hK : 1≤K)
    (hsw : s+w≤w') (hN : n+a≤r*w') (hρo : ρ+o≤n+a)
    (hDK : D*K≤n+a) (hker : aT+K*q≤n+a) (hcap : 2^a*R≤R₂)
    (hpcs : ∀ pc∈compactTopPcs d g K D o R₂,pc.Ok ds K n w' R₂) :
    (compactTopControlCost w w' s n a R r K ρ q aT o D R₂ (compactTopPcs d g K D o R₂):ℝ) ≤
      (16384*compactTopCountConst lam)*((R₂*(2^n*r*w'):ℕ):ℝ)*(d:ℝ)^lam := by
  let pcs := compactTopPcs d g K D o R₂
  let V := R₂*(2^n*r*w')
  have hn := compactTopControlCost_volume w w' s n a R r K ρ q aT o D R₂ pcs
    hR hr hw' hK hsw hN hρo hDK hker hcap hpcs
  have hnat : (compactTopControlCost w w' s n a R r K ρ q aT o D R₂ pcs:ℝ) ≤
      16384*((pcs.length+1:ℕ):ℝ)*(V:ℝ) := by exact_mod_cast hn
  have hcount := compactTopPcs_length_power d g K D o R₂ hd hD hlam
  have hscale := mul_le_mul_of_nonneg_left hcount (show (0:ℝ)≤16384*(V:ℝ) by positivity)
  calc
    (compactTopControlCost w w' s n a R r K ρ q aT o D R₂ pcs:ℝ)
        ≤16384*((pcs.length+1:ℕ):ℝ)*(V:ℝ) := hnat
    _ = (16384*(V:ℝ))*((pcs.length+1:ℕ):ℝ) := by ring
    _ ≤ (16384*(V:ℝ))*(compactTopCountConst lam*(d:ℝ)^lam) := hscale
    _ = (16384*compactTopCountConst lam)*(V:ℝ)*(d:ℝ)^lam := by ring

end
end IntegerMultBounds.MathlibTM2.Cost
