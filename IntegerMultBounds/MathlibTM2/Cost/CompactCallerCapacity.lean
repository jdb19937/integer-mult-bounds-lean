module

public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
public import IntegerMultBounds.MathlibTM2.Fast.SynRec

/-! Actual integer-root parameters pay the shared reservation for every selected
set above a fixed fractional cutoff. Smaller selected sets retain the explicit
capacity test; no assertion identifies them with the original global dimension. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open CompactGadgetReservationCapacity CompactGlobalRowPadding Filter
noncomputable section

def compactCaller_runtime_reserved (N : ℕ) : ℕ :=
  CompactGlobalReservation.reservedAxes NW m (Mult.Sizes.d N)
    (CompactReservationGrowth.guard N) (Mult.Sizes.K N)

/-- The literal cutoff is exactly the row, front and back reservation count. -/
theorem compactCaller_runtime_fits_iff (N D : ℕ) :
    CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
      (Mult.Sizes.K N) D ↔ compactCaller_runtime_reserved N ≤ D := Iff.rfl

private theorem reservation_scaled_bound {d G K ell q M : ℕ}
    (hK : 0<K) (hKd : K≤d) (hell : 1≤ell) (hG : G≤10*ell)
    (hrow : rowAxes NW m d≤q*ell) (hsmall : M*(q+32)*ell≤K) :
    M*CompactGlobalReservation.reservedAxes NW m d G K≤d := by
  have hfieldsR := CompactReservationGrowth.fields_bound d G K hK
  have hfields : (frontChunks d G K+backChunks d G K)*K≤3*d*G+2*K := by
    exact_mod_cast hfieldsR
  have hKd' : K≤ell*d := hKd.trans (Nat.le_mul_of_pos_left _ hell)
  have hrowK : rowAxes NW m d*K≤q*ell*d :=
    (Nat.mul_le_mul_right K hrow).trans (Nat.mul_le_mul_left _ hKd)
  have hGd : 3*d*G≤3*d*(10*ell) := Nat.mul_le_mul_left _ hG
  have hfields' : (frontChunks d G K+backChunks d G K)*K≤
      3*d*(10*ell)+2*(ell*d) :=
    hfields.trans (Nat.add_le_add hGd (Nat.mul_le_mul_left 2 hKd'))
  have hbound : CompactGlobalReservation.reservedAxes NW m d G K*K≤(q+32)*ell*d := by
    unfold CompactGlobalReservation.reservedAxes
    nlinarith only [hrowK,hfields']
  have hscaled := (Nat.mul_le_mul_left M hbound).trans
    (show M*((q+32)*ell*d)≤K*d by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right d hsmall)
  have hcancel : (M*CompactGlobalReservation.reservedAxes NW m d G K)*K≤d*K := by
    simpa only [Nat.mul_assoc,Nat.mul_comm K d] using hscaled
  exact Nat.le_of_mul_le_mul_right hcancel hK

/-- The actual shared reservation is eventually at most any fixed reciprocal
fraction of the original dimension. No selected-set capacity is assumed. -/
theorem compactCaller_runtime_eventually_reservation (M : ℕ) : ∀ᶠ N : ℕ in atTop,
    M*compactCaller_runtime_reserved N≤Mult.Sizes.d N := by
  filter_upwards [eventually_ge_atTop 2,compactCaller_runtime_eventually_guard,
    Mult.Sizes.eventually_clog_p_le_K (M*(Nat.clog 2 NW+32))] with N hN hguard hsmall
  have hK : 0<Mult.Sizes.K N := by omega
  have hb := Mult.Sizes.one_le_b hN
  have hp : 2≤Mult.Sizes.p N := by unfold Mult.Sizes.p; omega
  have hell : 1≤CompactScalarAllowances.guardLog N := by
    rw [compactCaller_runtime_guardLog hN]
    exact Nat.clog_pos (by decide) hp
  have hG : CompactReservationGrowth.guard N≤10*CompactScalarAllowances.guardLog N := by
    unfold CompactReservationGrowth.guard
    omega
  have hdim : 2*Mult.Sizes.d N≤Mult.Sizes.p N := by
    have hd := Mult.Sizes.d_le_b N
    unfold Mult.Sizes.p
    omega
  have hlog : Nat.clog m (2*Mult.Sizes.d N)≤CompactScalarAllowances.guardLog N := by
    rw [compactCaller_runtime_guardLog hN]
    exact Nat.clog_mono (by decide : 1<2) (by decide : 2≤m) hdim
  have hrow : rowAxes NW m (Mult.Sizes.d N)≤
      Nat.clog 2 NW*CompactScalarAllowances.guardLog N := Nat.mul_le_mul_left _ hlog
  rw [← compactCaller_runtime_guardLog hN] at hsmall
  exact reservation_scaled_bound hK (Mult.Sizes.K_le_d N) hell hG hrow hsmall

/-- Every selected set of at least a fixed fraction of the actual dimension
passes the capacity test eventually. Sets below that cutoff are not certified. -/
theorem compactCaller_runtime_eventually_capacity (M : ℕ) (hM : 0<M) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, Mult.Sizes.d N≤M*D →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D := by
  filter_upwards [compactCaller_runtime_eventually_reservation M] with N h D hD
  rw [compactCaller_runtime_fits_iff]
  exact Nat.le_of_mul_le_mul_left (h.trans hD) hM

/-- Nonterminal synthetic rounds select the complete original axis list. -/
theorem compactCaller_runtime_eventually_synDp : ∀ᶠ N : ℕ in atTop,
    ∀ (es : List ℕ) (ell h : ℕ), es.length=Mult.Sizes.d N → h+1<ell →
      CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) (synDp es ell h) := by
  filter_upwards [compactCaller_runtime_eventually_capacity 1 (by decide)] with N hcap
  intro es ell h hlen hh
  apply hcap
  simp only [synDp,hh,ite_true,hlen,one_mul,le_refl]

end
end IntegerMultBounds.MathlibTM2.Cost
