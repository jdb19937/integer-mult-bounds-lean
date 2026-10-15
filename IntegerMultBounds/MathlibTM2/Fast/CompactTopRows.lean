module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRows

/-! Actual top-level row padding includes every outside row and high spectator.
One padding to the global recursive divisor costs at most twice the original
row stock. Piece metadata then uses exact quotients of this actual stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.Networks
noncomputable section

noncomputable def compactTopRows (d R a : ℕ) : ℕ :=
  Compact.Layout.paddedRows (R*2^a) (NW^CompactGlobalRowPadding.depth m d)

/-- The reserved row axes pay the global divisor even with outside spectators. -/
theorem compactTopRows_divisor_le {d K R a : ℕ} (hK : 0<K) (hR : 0<R)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K ≤ a) :
    NW^CompactGlobalRowPadding.depth m d ≤ R*2^a := by
  have h := CompactGlobalRowPadding.divisor_le_original NW m d K hK
  change NW^CompactGlobalRowPadding.depth m d ≤ 2^(CompactGlobalRowPadding.rowAxes NW m d*K) at h
  exact h.trans ((Nat.pow_le_pow_right (by decide : 0<2) ha).trans
    (Nat.le_mul_of_pos_left _ hR))

theorem compactTopRows_bounds {d K R a : ℕ} (hK : 0<K) (hR : 0<R)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K ≤ a) :
    R*2^a ≤ compactTopRows d R a ∧
    compactTopRows d R a < R*2^a+NW^CompactGlobalRowPadding.depth m d ∧
    compactTopRows d R a ≤ 2*(R*2^a) ∧
    NW^CompactGlobalRowPadding.depth m d ∣ compactTopRows d R a := by
  exact Compact.Layout.padding_bounds _ _ (pow_pos NW_pos _)
    (compactTopRows_divisor_le hK hR ha)

theorem compactTopRows_positive {d K R a : ℕ} (hK : 0<K) (hR : 0<R)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K ≤ a) :
    0<compactTopRows d R a :=
  (Nat.mul_pos hR (pow_pos (by decide) _)).trans_le (compactTopRows_bounds hK hR ha).1

/-- The unchanged piece records are valid for the actual padded top-level array. -/
theorem compactTopRows_pcs_ok (ds : ComplexFramedExecution.Directions)
    {d K R a oS B activeOffset D n w : ℕ} (hK : 0<K) (hR : 0<R)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K ≤ a) (hD : D≤d)
    (hback : oS+K*B≤n) (hactive : activeOffset+K*D≤n)
    (hw : synE (gateCount (program ds)) (factorCount (program ds)) D D+D≤w) :
    ∀ pc ∈ (compactReservedPcs K 0 oS B activeOffset (CompactGlobalRowPadding.depth m d) D).map
      (compactRebasePc (compactTopRows d R a)),
      pc.Ok ds K n w (compactTopRows d R a) := by
  exact compactRebasedPcs_ok ds (compactTopRows_positive hK hR ha)
    (compactTopRows_bounds hK hR ha).2.2.2 (compactSyn_depth_le hD) hback hactive hw

end
end IntegerMultBounds.MathlibTM2.Fast
