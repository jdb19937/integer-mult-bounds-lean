module

public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerGuardPower
public import IntegerMultBounds.MathlibTM2.Cost.CompactInterimParameters
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters

/-! Quantitative reservation savings for the actual eighth-root compact chunk. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open CompactGadgetReservationCapacity
noncomputable section

/-- Integer-root rounding loses at most a factor of two for positive chunks. -/
theorem compactRetuned_chunk_lower (M : ℕ) (hM : 2≤M) :
    (Mult.Sizes.d M:ℝ)^Mult.CompactSizes.cParam≤2*(Mult.CompactSizes.K M:ℝ) := by
  have hK : (1:ℝ)≤Mult.CompactSizes.K M := by exact_mod_cast Mult.CompactSizes.one_le_K hM
  have hf := Nat.lt_floor_add_one ((Mult.Sizes.d M:ℝ)^Mult.CompactSizes.cParam)
  rw [←Mult.CompactSizes.K_eq_floor] at hf
  linarith

private theorem fieldsRate {d g k f c : ℝ} (hd : 0<d) (hg : 0≤g) (hk : 0<k)
    (hchunk : d^c≤2*k) (hfields : f*k≤3*d*g+2*k) :
    f≤6*g*d^(1-c)+2 := by
  have hdim : d≤2*k*d^(1-c) := by
    have h := mul_le_mul_of_nonneg_right hchunk (Real.rpow_nonneg hd.le (1-c))
    rw [←Real.rpow_add hd,show c+(1-c)=1 by ring,Real.rpow_one] at h
    exact h
  have hscale := mul_le_mul_of_nonneg_right hdim (show 0≤3*g by positivity)
  apply (mul_le_mul_iff_left₀ hk).mp
  nlinarith only [hfields,hscale]

/-- Dyadic coefficient for the complete original row/front/back reservation. -/
def compactRetunedReservationCoeff (a : ℝ) : ℝ :=
  compactLayerDyadic (((Nat.clog 2 NW:ℝ)+8)*
    compactCallerGuardPowerCoeff (a-(1-Mult.CompactSizes.cParam)))

/-- All reserved axes fit every exponent above seven eighths, including the
proposed compact layer exponent. This is stronger than merely sublinear growth. -/
theorem compactRetuned_reservation_power (M : ℕ) (hM : 2≤M) (a : ℝ)
    (ha : 1-Mult.CompactSizes.cParam<a) :
    (CompactGlobalReservation.reservedAxes NW m (Mult.Sizes.d M)
      (Mult.CompactSizes.guard M) (Mult.CompactSizes.K M):ℝ)≤
      compactRetunedReservationCoeff a*(Mult.Sizes.d M:ℝ)^a := by
  let d := Mult.Sizes.d M
  let g := Mult.CompactSizes.guard M
  let K := Mult.CompactSizes.K M
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K+backChunks d g K
  have hd : 1≤d := Mult.Sizes.one_le_d hM
  have hdR : (1:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := by linarith
  have hK : 0<K := lt_of_lt_of_le (by decide : 0<1) (Mult.CompactSizes.one_le_K hM)
  have hg : (1:ℝ)≤g := by
    change (1:ℝ)≤(4*Nat.clog 2 (Mult.Sizes.p M)+6:ℕ)
    exact_mod_cast (by omega : 1≤4*Nat.clog 2 (Mult.Sizes.p M)+6)
  have hfields := fieldsRate hd0 (by positivity : (0:ℝ)≤g)
    (by exact_mod_cast hK) (compactRetuned_chunk_lower M hM)
    (CompactReservationGrowth.fields_bound d g K hK)
  have hdimP : 2*d≤Mult.Sizes.p M := by
    have hdb := Mult.Sizes.d_le_b M
    change 2*Mult.Sizes.d M≤6*Mult.Sizes.b M
    omega
  have hlog : Nat.clog m (2*d)≤Nat.clog 2 (Mult.Sizes.p M) :=
    Nat.clog_mono (by decide : 1<2) (by decide : 2≤m) hdimP
  have hrow : (q:ℝ)≤(Nat.clog 2 NW:ℝ)*(g:ℝ) := by
    have hgp : Nat.clog 2 (Mult.Sizes.p M)≤g := by
      change Nat.clog 2 (Mult.Sizes.p M)≤4*Nat.clog 2 (Mult.Sizes.p M)+6
      omega
    exact_mod_cast Nat.mul_le_mul_left (Nat.clog 2 NW) (hlog.trans hgp)
  have hc : 0≤1-Mult.CompactSizes.cParam := by norm_num [Mult.CompactSizes.cParam,Mult.CompactSizes.cExp]
  have hp : 1≤(d:ℝ)^(1-Mult.CompactSizes.cParam) := Real.one_le_rpow hdR hc
  have hrow' : (q:ℝ)≤(Nat.clog 2 NW:ℝ)*(g:ℝ)*(d:ℝ)^(1-Mult.CompactSizes.cParam) :=
    hrow.trans (le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hp)
  have htwo : (2:ℝ)≤2*(g:ℝ)*(d:ℝ)^(1-Mult.CompactSizes.cParam) := by nlinarith
  have hsum : ((q+f:ℕ):ℝ)≤((Nat.clog 2 NW:ℝ)+8)*(g:ℝ)*(d:ℝ)^(1-Mult.CompactSizes.cParam) := by
    push_cast
    nlinarith only [hrow',hfields,htwo]
  have hguard := compactCaller_guard_power M hM (a-(1-Mult.CompactSizes.cParam)) (by linarith)
  have hscale := mul_le_mul_of_nonneg_left hguard
    (show (0:ℝ)≤((Nat.clog 2 NW:ℝ)+8)*(d:ℝ)^(1-Mult.CompactSizes.cParam) from
      mul_nonneg (add_nonneg (Nat.cast_nonneg _) (by norm_num)) (Real.rpow_nonneg hd0.le _))
  have he : (d:ℝ)^(1-Mult.CompactSizes.cParam)*(d:ℝ)^(a-(1-Mult.CompactSizes.cParam))=(d:ℝ)^a := by
    rw [←Real.rpow_add hd0]; congr 1; ring
  have hbound : ((q+f:ℕ):ℝ)≤((Nat.clog 2 NW:ℝ)+8)*
      compactCallerGuardPowerCoeff (a-(1-Mult.CompactSizes.cParam))*(d:ℝ)^a := by
    calc
      _ ≤ ((Nat.clog 2 NW:ℝ)+8)*(g:ℝ)*(d:ℝ)^(1-Mult.CompactSizes.cParam) := hsum
      _ ≤ ((Nat.clog 2 NW:ℝ)+8)*compactCallerGuardPowerCoeff (a-(1-Mult.CompactSizes.cParam))*
          ((d:ℝ)^(1-Mult.CompactSizes.cParam)*(d:ℝ)^(a-(1-Mult.CompactSizes.cParam))) := by
        nlinarith only [hscale]
      _ = _ := by rw [he]
  have hcoeff := mul_le_mul_of_nonneg_right
    (compactLayerDyadic_le (((Nat.clog 2 NW:ℝ)+8)*compactCallerGuardPowerCoeff (a-(1-Mult.CompactSizes.cParam))))
    (Real.rpow_nonneg hd0.le a)
  simpa only [q,f,d,g,K,CompactGlobalReservation.reservedAxes,Nat.add_assoc,
    compactRetunedReservationCoeff] using hbound.trans hcoeff

end
end IntegerMultBounds.MathlibTM2.Cost
