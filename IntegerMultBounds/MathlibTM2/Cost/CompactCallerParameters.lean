module

import IntegerMultBounds.MathlibTM2.Cost.CompactParameters
public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
public import IntegerMultBounds.Machine.CompactReservationGrowth
import IntegerMultBounds.MathlibTM2.Fast.SynRecB
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Caller size discharge for the shared reserved shape. Actual global padding
and extra outer spectators are counted in the repair address. The eventual
regime here uses `IntegerMultBounds.Sizes`; identifying those sizes with a
separate runtime parameter generator remains a caller obligation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
open Filter
noncomputable section

/-- Padding adds at most one row-address bit; extra outer spectators are retained.
The row count may be any smaller positive descendant count. -/
theorem compactCaller_address_le {axes guard K D payload rows extra : ℕ}
    (hK : 0<K) (hfit : CompactReservationFits axes guard K D)
    (hrows : rows ≤ 2^extra*CompactGlobalRowPadding.initialRows NW m axes K) :
    (compactReservationShape axes guard K D payload).bits + rows.log2 + 2 ≤ extra+K*D+3 := by
  have hc : 0<NW := NW_pos
  have hb := (CompactGlobalRowPadding.initial_bounds NW m axes K hc hK).2.2.1
  have hr : rows ≤ 2^(extra+CompactGlobalRowPadding.rowAxes NW m axes*K+1) := by
    calc
      rows ≤ 2^extra*(2*CompactGlobalRowPadding.originalRows NW m axes K) :=
        hrows.trans (Nat.mul_le_mul_left _ hb)
      _ = _ := by unfold CompactGlobalRowPadding.originalRows; simp only [pow_add,pow_one]; ring
  have hl : rows.log2 ≤ extra+CompactGlobalRowPadding.rowAxes NW m axes*K+1 := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_mono_right (b:=2) hr).trans_eq (Nat.log_pow (by decide) _)
  have hq : CompactGlobalRowPadding.rowAxes NW m axes≤D := by
    unfold CompactReservationFits at hfit
    omega
  have he : K*(D-CompactGlobalRowPadding.rowAxes NW m axes)+
      CompactGlobalRowPadding.rowAxes NW m axes*K=K*D := by
    rw [Nat.mul_comm (CompactGlobalRowPadding.rowAxes NW m axes) K,←Nat.mul_add,
      Nat.sub_add_cancel hq]
  rw [compactReservation_bits hK hfit]
  omega

/-- The same address bound holds at every actual padded recursive row depth. -/
theorem compactCaller_recursive_address_le {axes guard K D payload extra j : ℕ}
    (hK : 0<K) (hfit : CompactReservationFits axes guard K D) :
    (compactReservationShape axes guard K D payload).bits +
      (2^extra*CompactGlobalRowPadding.rowsAt NW m axes K j).log2+2 ≤ extra+K*D+3 :=
  compactCaller_address_le hK hfit (Nat.mul_le_mul_left _
    (CompactGlobalRowPadding.rowsAt_le_initial NW m axes K j))

/-- Actual precision, coefficient capacity and padded rows discharge every repair
premise uniformly over all pieces and recursive children. No per-node density,
address-width or cubic-size hypothesis is supplied. -/
theorem compactCaller_eventually_packed : ∀ᶠ N : ℕ in atTop,
    ∀ (D o r w extra : ℕ)
      (d : Inputs (compactReservationShape (Sizes.d N) (CompactReservationGrowth.guard N)
        (Sizes.K N) D (2^o*(3*(r*w))))),
      D≤Sizes.d N →
      CompactReservationFits (Sizes.d N) (CompactReservationGrowth.guard N) (Sizes.K N) D →
      d.rows≤2^extra*CompactGlobalRowPadding.initialRows NW m (Sizes.d N) (Sizes.K N) →
      extra≤6*Sizes.b N → 2^Sizes.ℓ N≤r → 6*Sizes.b N≤w →
      ActivePrefixStageRuntimeData.Packed d 1 := by
  filter_upwards [CompactScalarAllowances.eventually_guard_fits,
    CompactScalarAllowances.eventually_axis_ge_precision] with N hguard haxis
  intro D o r w extra d hD hfit hrows hextra hr hw
  have hK : 0<Sizes.K N := by omega
  have haddress := compactCaller_address_le (payload:=2^o*(3*(r*w))) hK hfit hrows
  have hp := TimeBound.precision_pos N
  have hp6 := TimeBound.six_le_precision N
  have hs := CompactScalarAllowances.original_axis_size N D hD
  have hwidth : d.stage.f≤Sizes.d N := d.stage.widthFits
  have hf := CompactScalarAllowances.selected_count N d.stage.f hwidth
  have heR : (extra:ℝ)≤TimeBound.precision N := by
    have h : (extra:ℝ)≤(6*Sizes.b N:ℕ) := by exact_mod_cast hextra
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Sizes.precision_eq] using h
  have haddrR : (((compactReservationShape (Sizes.d N) (CompactReservationGrowth.guard N)
      (Sizes.K N) D (2^o*(3*(r*w)))).bits + d.rows.log2+2 : ℕ):ℝ) ≤
      TimeBound.precision N^2+TimeBound.precision N := by
    have ha : (((compactReservationShape (Sizes.d N) (CompactReservationGrowth.guard N)
        (Sizes.K N) D (2^o*(3*(r*w)))).bits + d.rows.log2+2 : ℕ):ℝ) ≤
        ((extra+Sizes.K N*D+3 : ℕ):ℝ) := by exact_mod_cast haddress
    push_cast at ha hs ⊢
    nlinarith only [ha,hs,heR]
  have hrR : TimeBound.precision N≤(r:ℝ) := by
    apply haxis.trans
    have h : ((2^Sizes.ℓ N : ℕ):ℝ)≤r := by exact_mod_cast hr
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Sizes.r] using h
  have hwR : TimeBound.precision N≤(w:ℝ) := by
    have h : ((6*Sizes.b N : ℕ):ℝ)≤w := by exact_mod_cast hw
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Sizes.precision_eq] using h
  have hprod : TimeBound.precision N^2≤(r:ℝ)*w := by
    simpa only [pow_two] using mul_le_mul hrR hwR hp.le (Nat.cast_nonneg r)
  have hfold : 3*((r:ℝ)*w)≤((2^o*(3*(r*w)) : ℕ):ℝ) := by
    have hpow : (1:ℝ)≤(2:ℝ)^o := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hpow (show (0:ℝ)≤3*((r:ℝ)*w) by positivity)
    push_cast
    nlinarith only [hh]
  have hrecord : (compactReservationShape (Sizes.d N) (CompactReservationGrowth.guard N)
      (Sizes.K N) D (2^o*(3*(r*w)))).bits+d.rows.log2+2 ≤ 2^o*(3*(r*w)) := by
    have h : ((((compactReservationShape (Sizes.d N) (CompactReservationGrowth.guard N)
        (Sizes.K N) D (2^o*(3*(r*w)))).bits+d.rows.log2+2 : ℕ):ℝ))≤((2^o*(3*(r*w)) : ℕ):ℝ) := by
      nlinarith only [haddrR,hprod,hfold,hp6]
    exact_mod_cast h
  have hcube : (((compactReservationShape (Sizes.d N) (CompactReservationGrowth.guard N)
      (Sizes.K N) D (2^o*(3*(r*w)))).bits+d.rows.log2+2 : ℕ):ℝ) ≤ TimeBound.precision N^3 := by
    have hmul := mul_le_mul_of_nonneg_left (show (2:ℝ)≤TimeBound.precision N by linarith) (sq_nonneg (TimeBound.precision N))
    nlinarith only [haddrR,hmul,hp6]
  exact compactRuntimePacked_of_dyadic d (TimeBound.precision N) (CompactScalarAllowances.guardLog N)
    hp hf (CompactScalarAllowances.precision_dyadic N) hguard rfl hrecord hcube

end
end IntegerMultBounds.MathlibTM2.Cost
