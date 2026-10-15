module

public import IntegerMultBounds.MathlibTM2.Cost.CompactFactor

/-! Actual compact factor costs: the child bound has coefficient one, and every
other stage is paid by local volume and the compact selected-width envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open CompactGadgetReservationShape (Shape)
noncomputable section

/-- Complete actual factor budget. Both compact basis stages and all control,
conjugation, shift, parking and exponent reconstruction costs are included.
Only the child recurrence remains, with coefficient exactly one. -/
theorem compactFactorCost_le {s : Shape} {j u ρ a₀ R₀ n o r w left right : ℕ}
    (ds : ComplexFramedExecution.Directions)
    (layout : CompactRecursiveLayout s n a₀ (bits u j) ρ left right)
    (hr : 1≤r) (hw : 1≤w) (hu : 1≤u) (hR₀ : 1≤R₀)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk)
    (hrecord : s.bits+1≤s.payload) (hpayload : s.payload=2^o*(3*(r*w)))
    (T Ka D : ℕ)
    (hp : ∀ x y (hxy : x≠y),1<bits u j → ActivePrefixStageRuntimeData.Packed
      (compactSlotComputedInputs layout x y hxy (rowsAt R₀ j) hG hGK (rowsAt_pos hR₀ j) hrecord) D)
    (hTw : ∀ i≤j,expZ u ds i≤w) (g : ZMod 4 × BinaryWalsh.Address m) (cc : ℕ) :
    (compactFactorCost T ds j u s.chunk ρ (o+a₀) R₀ (o+n) r w g cc
      (compactFactorBasisCost layout hG hGK (rowsAt_pos hR₀ j) hrecord D hp T Ka o r w g.2) : ℝ) ≤
      (cc:ℝ)+compactFactorConst T D*((2^(n-s.bits)*rowsAt R₀ j)*s.recordWidth : ℕ)*
        ((max 1 ((bits u j-1)*s.guard) : ℕ) : ℝ)^Parameters.tau := by
  let V := (2^(n-s.bits)*rowsAt R₀ j)*s.recordWidth
  let E : ℝ := ((max 1 ((bits u j-1)*s.guard) : ℕ) : ℝ)^Parameters.tau
  let B : ℝ := compactBasisConst T D*(V:ℝ)*E
  have hR := rowsAt_pos hR₀ j
  have hV : 1≤V := by
    have hpayloadPos : 0<s.payload := by omega
    change 0<(2^(n-s.bits)*rowsAt R₀ j)*(2^s.bits*s.payload)
    positivity
  have hE : 1≤E := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 ((bits u j-1)*s.guard)) (by norm_num [Parameters.tau])
  have hB0 : 0≤B := by dsimp [B,compactBasisConst]; positivity
  have hb : ∀ x,compactFactorBasisCost layout hG hGK hR hrecord D hp T Ka o r w g.2 x≤⌈B⌉₊ := by
    intro x
    have hh := compactBasisCost_le layout x hG hGK hR hrecord hpayload T Ka D (hp x) g.2
    exact_mod_cast hh.trans (Nat.le_ceil B)
  have hfit : (o+a₀)+s.chunk*bits u (j+1)≤o+n := by
    have hh := layout.live_fit
    change o+a₀+s.chunk*(m*bits u j)≤o+n
    nlinarith only [hh]
  have hn := compactFactorCost_linear T ds g cc ⌈B⌉₊ _ hu hr hw hR₀
    layout.selectedFits hfit hTw hb
  have hceil : (⌈B⌉₊:ℝ)≤B+1 := (Nat.ceil_lt_add_one hB0).le
  have hwire : rowsAt R₀ j*2^(o+n)*(r*w)≤V := by
    have hv : V=3*(rowsAt R₀ j*2^(o+n)*(r*w)) := by
      rw [show V=(2^(n-s.bits)*rowsAt R₀ j)*s.recordWidth from rfl,
        compactSlotComputed_volume layout (rowsAt R₀ j),hpayload]
      simp only [pow_add]
      ring
    omega
  exact compactFactor_envelope hn hceil hwire hV hE (compactFactorConst_le T D)

end
end IntegerMultBounds.MathlibTM2.Cost
