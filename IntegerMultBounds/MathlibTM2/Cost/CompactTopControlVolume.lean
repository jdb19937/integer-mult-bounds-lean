module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopOverhead

/-! Complete actual top controls cost padded volume times the number of records.
The logarithmic record count remains visible for asymptotic absorption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

private theorem compactCfgCost_le (w s a R R₂ q aT K o D V : ℕ)
    (hV : 1≤V) (hw : w≤V) (hs : s≤V) (ha : a≤V) (hR : R≤V) (hR₂ : R₂≤V)
    (hq : q≤V) (haT : aT≤V) (hKq : K*q≤V) (ho : o≤V) (hD : D≤V) :
    topGetCost (topCfg w s a R R₂ q aT K o D) ≤256*V := by
  simp only [topGetCost,topRecLen,topCfg,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- Every actual scan, descriptor read, row operation, piece dispatch and
cleanup is paid by a fixed dyadic coefficient times padded stream volume and
the explicit record count. No unspecified control-cost bound is assumed. -/
theorem compactTopControlCost_volume {ds : ComplexFramedExecution.Directions}
    (w w' s n a R r K ρ q aT o D R₂ : ℕ) (pcs : List TopPc)
    (hR : 1≤R) (hr : 1≤r) (hw' : 1≤w') (hK : 1≤K)
    (hsw : s+w≤w') (hN : n+a≤r*w') (hρo : ρ+o≤n+a)
    (hDK : D*K≤n+a) (hker : aT+K*q≤n+a)
    (hcap : 2^a*R≤R₂) (hpcs : ∀ pc∈pcs,pc.Ok ds K n w' R₂) :
    compactTopControlCost w w' s n a R r K ρ q aT o D R₂ pcs ≤
      16384*(pcs.length+1)*(R₂*(2^n*r*w')) := by
  let V := R₂*(2^n*r*w')
  let cfg := topCfg w s a R R₂ q aT K o D
  have hR₂pos : 1≤R₂ := (Nat.mul_le_mul (Nat.one_le_pow a 2 (by decide)) hR).trans hcap
  have hL : 1≤2^n*r*w' := Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow n 2 (by decide)) hr) hw'
  have hV : 1≤V := Nat.mul_le_mul hR₂pos hL
  have hR₂V : R₂≤V := Nat.le_mul_of_pos_right _ hL
  have hRV : R≤V := (Nat.le_mul_of_pos_left _ (Nat.one_le_pow a 2 (by decide))).trans (hcap.trans hR₂V)
  have hrwV : r*w'≤V := by
    have hs : 1≤R₂*2^n := Nat.mul_le_mul hR₂pos (Nat.one_le_pow n 2 (by decide))
    have hh := Nat.le_mul_of_pos_left (r*w') hs
    dsimp only [V]
    nlinarith only [hh]
  have hwV : w'≤V := (Nat.le_mul_of_pos_left w' hr).trans hrwV
  have hNV : n+a≤V := hN.trans hrwV
  have hD : D≤V := ((Nat.le_mul_of_pos_right D hK).trans hDK).trans hNV
  have hq : q≤V := (Nat.le_mul_of_pos_left q hK).trans (by omega)
  have hget : topGetCost cfg≤256*V := compactCfgCost_le _ _ _ _ _ _ _ _ _ _ V hV
    (by omega) (by omega) (by omega) hRV hR₂V hq (by omega) (by omega) (by omega) hD
  have hc := compactTopControlCost_le w w' s n a R r K ρ q aT o D R₂ pcs
    hR hr hw' hK hsw hN hρo hDK hker hcap hpcs
  change _ ≤2048*V+32*topGetCost cfg+pcs.length*(topGetCost cfg+32*n+2*R₂+32)+4 at hc
  have hheaders : topGetCost cfg+32*n+2*R₂+32≤512*V := by
    omega
  have hlist := Nat.mul_le_mul_left pcs.length hheaders
  change _ ≤16384*(pcs.length+1)*V
  nlinarith only [hc,hget,hlist,hV,Nat.zero_le (pcs.length*V)]

end IntegerMultBounds.MathlibTM2.Cost
