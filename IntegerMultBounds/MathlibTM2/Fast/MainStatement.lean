module

import IntegerMultBounds.MathlibTM2.Fast.MainCorrect
import IntegerMultBounds.MathlibTM2.Fast.MainTime
public import IntegerMultBounds.MathlibTM2.Fast.MainEmbed
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The statement from the layout programs and the distribution

`statement_of_bundles`: `IntegerMultBounds.MathlibTM2.Statement` holds as soon as, for some alphabet offset `K`, layer
procedure table `Lb`, coefficient width `w` and transform parameter registers `σ`,

* synthetic transforms exist meeting `SynFwdSpec`/`SynOppSpec` on the register file of
  `Fast/MainRegs` with `cF + cO = O(totConv)` (`MnSyn`), and
* a parameter distribution exists meeting `MnDistSpec` with its output file between runs, the
  width conditions and `cost = O(n + (b + 1)^k)` (`MnDist`).

`statement_of_specs`: the transforms are the layer machine's (`Fast/MainEmbed`, `mnSynOfLay`),
so the statement follows from a layout bundle `MnLay w` (the layout programs `layP`, `layQ`
with their contracts `layF`, `layO`, the parameter wires `v₀`, the parking contents `P₀`, and the
transform cost bound) and a distribution `MnDist mnKa mnLb w (mnσL L)`.

The proof runs the fast multiplier `mnFast` (`Fast/MainProg`) through the dispatch of
`Fast/Glue` (`statement_of_dispatch`): correctness beyond the threshold `mnN₀`
(`mn_hostMul_ge`), and the time bound `mnTime ≤ totDirectBound C` (`mnTime_le`) through
`Cost/DirectTotal.tot_direct_htime`, at `κ = totKappa`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- **The statement from the two bundles**: the synthetic transforms (`MnSyn`) and the
parameter distribution (`MnDist`). -/
theorem mulInTime_of_bundles
    (h : ∃ (K : ℕ) (Lb : LProc → MnPr (prime + K)) (w : ℕ → ℕ)
      (σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))),
      Nonempty (MnSyn K Lb w σ) ∧ Nonempty (MnDist K Lb w σ)) :
    IntegerMultBounds.MathlibTM2.MulInTime IntegerMultBounds.MathlibTM2.Cost.totKappa := by
  obtain ⟨K, Lb, w, σ, ⟨Y⟩, ⟨D⟩⟩ := h
  obtain ⟨C, hC⟩ := mnTime_le D Y (mnC D Y)
  exact mulInTime_of_dispatch (mnTable D Y) .main mnV₀ (mnTime D Y (mnC D Y)) (mnN₀ D Y)
    (mn_hostMul_ge D Y) (IntegerMultBounds.MathlibTM2.Cost.tot_direct_htime C hC)

/-- The existential statement, retaining the quantitative bundle theorem. -/
theorem statement_of_bundles
    (h : ∃ (K : ℕ) (Lb : LProc → MnPr (prime + K)) (w : ℕ → ℕ)
      (σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))),
      Nonempty (MnSyn K Lb w σ) ∧ Nonempty (MnDist K Lb w σ)) :
    IntegerMultBounds.MathlibTM2.Statement :=
  ⟨_, IntegerMultBounds.MathlibTM2.Cost.tot_kappa_pos, mulInTime_of_bundles h⟩

/-- **The statement from the layout programs and the distribution.** -/
theorem statement_of_specs
    (h : ∃ (w : ℕ → ℕ) (L : MnLay w), Nonempty (MnDist mnKa mnLb w (mnσL L))) :
    IntegerMultBounds.MathlibTM2.Statement := by
  obtain ⟨w, L, ⟨D⟩⟩ := h
  have hw : ∀ᶠ n in atTop, p n + 2 ≤ w n := by
    filter_upwards [D.widths] with n hn
    have := hn.1
    omega
  exact statement_of_bundles ⟨mnKa, mnLb, w, mnσL L, ⟨mnSynOfLay L hw⟩, ⟨D⟩⟩

end IntegerMultBounds.MathlibTM2.Fast.Main
