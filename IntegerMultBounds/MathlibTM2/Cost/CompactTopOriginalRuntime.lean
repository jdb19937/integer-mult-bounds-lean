module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopOriginalGeometry
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters

/-! Runtime integer-root sizes discharge the row-division budget uniformly for
selected intervals at least one chunk long. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer Filter
noncomputable section

theorem compactCaller_runtime_eventually_row_room : ∀ᶠ N : ℕ in atTop,
    2*CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)+4≤Mult.Sizes.K N := by
  filter_upwards [eventually_ge_atTop 2,
    Mult.Sizes.eventually_clog_p_le_K (4*(Nat.clog 2 NW+1))] with N hN hK
  have hp : 2≤Mult.Sizes.p N := by
    have := Mult.Sizes.one_le_b hN
    unfold Mult.Sizes.p
    omega
  have hlog : 1≤Nat.clog 2 (Mult.Sizes.p N) := Nat.clog_pos (by decide) hp
  have hdim : 2*Mult.Sizes.d N≤Mult.Sizes.p N := by
    have := Mult.Sizes.d_le_b N
    unfold Mult.Sizes.p
    omega
  have hm : 2≤m := by norm_num [m]
  have hrow := Nat.mul_le_mul_left (Nat.clog 2 NW)
    (Nat.clog_mono (by decide : 1<2) hm hdim)
  change CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)≤
    Nat.clog 2 NW*Nat.clog 2 (Mult.Sizes.p N) at hrow
  nlinarith

/-- Padding construction pays its actual division work at the runtime sizes;
no separately assumed arithmetic cost or row-division budget remains. -/
theorem compactTopOriginal_runtime_eventually_division : ∀ᶠ N : ℕ in atTop,
    ∀ D o R a r w : ℕ, Mult.Sizes.K N≤D → 0<R → 0<r → 0<w →
    CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)*Mult.Sizes.K N≤a →
    let n := o+Mult.Sizes.K N*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))
    (2^a*R+NW^CompactGlobalRowPadding.depth m (Mult.Sizes.d N)+1)*
      (NW^CompactGlobalRowPadding.depth m (Mult.Sizes.d N)+1)≤
        compactTopRows (Mult.Sizes.d N) R a*2^n*(r*w) := by
  filter_upwards [compactCaller_runtime_eventually_row_room] with N hroom
  intro D o R a r w hD hR hr hw ha
  have hK : 0<Mult.Sizes.K N := by omega
  have hselected : CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)+3≤
      D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N) := by omega
  have hm := Nat.mul_le_mul_left (Mult.Sizes.K N) hselected
  rw [Nat.mul_add] at hm
  apply compactTopOriginal_division_volume (Mult.Sizes.d N) (Mult.Sizes.K N) R a _ r w
    hK hR hr hw ha
  nlinarith

end
end IntegerMultBounds.MathlibTM2.Cost
