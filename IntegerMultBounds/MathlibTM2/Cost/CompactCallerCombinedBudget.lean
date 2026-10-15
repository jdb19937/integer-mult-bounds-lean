module
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerScalarBudget
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerDivisorPolynomial

/-! One explicit polynomial scalar budget for the actual compact caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

def compactCallerCombinedBudget (c cDiv eDiv p : ℕ) :=
  2^(c+cDiv+2)*(p+1)^(max 2 eDiv)

theorem compactCallerScalarBudget_le_combined (c cDiv eDiv p : ℕ) :
    compactCallerScalarBudget c p≤compactCallerCombinedBudget c cDiv eDiv p :=
  Nat.mul_le_mul
    (Nat.pow_le_pow_right (by decide : 0<2) (by omega : c+2≤c+cDiv+2))
    (Nat.pow_le_pow_right (Nat.succ_pos p) (Nat.le_max_left 2 eDiv))

theorem compactCallerDivisorBudget_le_combined (c cDiv eDiv p : ℕ) :
    2^cDiv*(p+1)^eDiv≤compactCallerCombinedBudget c cDiv eDiv p :=
  Nat.mul_le_mul
    (Nat.pow_le_pow_right (by decide : 0<2) (by omega : cDiv≤c+cDiv+2))
    (Nat.pow_le_pow_right (Nat.succ_pos p) (Nat.le_max_right 2 eDiv))

theorem compactCaller_runtime_eventually_combinedBudget (G F c : ℕ) (hF : F+1≤m^5) :
    ∀ᶠ M : ℕ in atTop, ∀ N D o W h b : ℕ,
    N≤Mult.Sizes.p M → D≤Mult.Sizes.d M →
    CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) (Mult.Sizes.K M) D →
    o+Mult.Sizes.K M*D≤N → Mult.Sizes.p M≤W → W≤2^c*(Mult.Sizes.p M+1) →
    h≤Mult.Sizes.p M → b≤Mult.Sizes.p M →
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let K := Mult.Sizes.K M
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let back := backChunks d g K
    let active := compactReservationActive d g K D
    let E := back+synE G F active active
    let working := W+((D+1)/2+(qrow+f)+E)+D
    CompactCallerScalarBounds N d g K D o W h b qrow f back active E working
      (compactCallerCombinedBudget c (Nat.clog 2 (m+1)*Nat.clog m NW)
        (Nat.clog m NW) (Mult.Sizes.p M)) ∧
    NW^CompactGlobalRowPadding.depth m d≤
      compactCallerCombinedBudget c (Nat.clog 2 (m+1)*Nat.clog m NW)
        (Nat.clog m NW) (Mult.Sizes.p M) := by
  filter_upwards [eventually_ge_atTop 2,compactCaller_runtime_eventually_scalarBudget G F c hF]
    with M hM hs
  intro N D o W h b hN hD hfit haddress hWp hW hh hb
  have hfields := hs N D o W h b hN hD hfit haddress hWp hW hh hb
  constructor
  · exact hfields.mono (compactCallerScalarBudget_le_combined c
      (Nat.clog 2 (m+1)*Nat.clog m NW) (Nat.clog m NW) (Mult.Sizes.p M))
  · exact (compactCaller_runtime_divisor_polynomial M hM).trans
      (compactCallerDivisorBudget_le_combined c (Nat.clog 2 (m+1)*Nat.clog m NW)
        (Nat.clog m NW) (Mult.Sizes.p M))

end
end IntegerMultBounds.MathlibTM2.Cost
