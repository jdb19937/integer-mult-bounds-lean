module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopOriginalBound

/-! Volume absorption for the concrete original-input adapter. The unary
division budget remains explicit geometry, rather than an assumed cost bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.LayerMachine
noncomputable section

theorem compactTopConfigRowsCost_volume (d a R V : ℕ)
    (hV : 1≤V) (ha : a≤V) (hR : R≤V) (hR₂ : compactTopRows d R a≤V)
    (hdivision : (2^a*R+NW^CompactGlobalRowPadding.depth m d+1)*
      (NW^CompactGlobalRowPadding.depth m d+1)≤V) :
    compactTopConfigRowsCost d a R≤compactTopConfigDivisorCost d+1024*V := by
  have h := compactTopConfigRowsAfterCost_bound a R
    (NW^CompactGlobalRowPadding.depth m d) (pow_pos NW_pos _)
  have hpad : Compact.Layout.paddedRows (2^a*R)
      (NW^CompactGlobalRowPadding.depth m d)≤V := by
    simpa only [compactTopRows,Nat.mul_comm] using hR₂
  unfold compactTopConfigRowsCost
  omega

/-- Once the actual row-stock arithmetic and scalar fields fit the stream
volume, all adapter work is linear except computing the original divisor. -/
theorem compactTopOriginalAdapterCost_volume (d g W a D q E R aT K o V : ℕ)
    (hV : 1≤V) (hg : g≤V) (hW : W≤V) (ha : a≤V) (hD : D≤V)
    (hq : q≤V) (hE : E≤V) (hR : R≤V) (hR₂ : compactTopRows d R a≤V)
    (haT : aT≤V) (hKq : K*q≤V) (ho : o≤V)
    (hdivision : (2^a*R+NW^CompactGlobalRowPadding.depth m d+1)*
      (NW^CompactGlobalRowPadding.depth m d+1)≤V) :
    compactTopOriginalAdapterCost d g W a D q E R aT K o≤
      compactTopConfigDivisorCost d+8192*V := by
  have := compactTopOriginalAdapterCost_bound d g W a D q E R aT K o
  have := compactTopConfigRowsCost_volume d a R V hV ha hR hR₂ hdivision
  omega

end
end IntegerMultBounds.MathlibTM2.Cost
