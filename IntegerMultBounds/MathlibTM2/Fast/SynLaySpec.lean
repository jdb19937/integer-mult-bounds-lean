module

public import IntegerMultBounds.MathlibTM2.Fast.SynLayOpp
public import IntegerMultBounds.MathlibTM2.Fast.SynFwd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The synthetic transforms with their layout programs

Paper §6, `lem:synthetic-transform-cost`. `synFwd_spec_br` and `synOpp_spec_br`
(`Fast/SynFwd.lean`) at the layout programs `slyFwd`, `slyOpp` (`Fast/SynLayFwd.lean`,
`Fast/SynLayOpp.lean`): the hypothesis `hLay` is discharged, the park predicate is `slyPk W E`
(`park` holds the writer's word width `W` and the axis word `E` of the long axes,
`Fast/SynLayPre.lean`), and the costs are `slyFwdCost`, `slyOppCost`.

## Parameters

* The record length is `B = 2^l w` (`r = 2^l` coefficients of `w` symbols), computed by the
  program from the wires `p .r`, `p .w`.
* The axis word `E` satisfies `ax es i = ℓ - 1 + E / 2^i % 2` for `i < d`: bit `i` of `E` is
  set exactly on the long axes.
* The writer's word width `W` satisfies `(N + 1)^N < 2^W`, `N + B + 4 ≤ W`, `ℓ < 2^W` and
  `E < 2^W` (`N = Σ aᵢ`); `slyW` is such a width (`slyW_ok`): `W = N² + N + B + ℓ + d + 4`,
  quadratic in the sizes (`W ≤ cW p²` in the cost matching).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.Rounds
  IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


/-! ### A word width -/

/-- A word width for the writer: `N² + N + B + ℓ + D + 4`. -/
def slyW (N B ℓ D : ℕ) : ℕ := N * N + N + B + ℓ + D + 4

theorem slyW_ok (N B ℓ D E : ℕ) (hE : E < 2 ^ D) :
    (N + 1) ^ N < 2 ^ slyW N B ℓ D ∧ N + B + 4 ≤ slyW N B ℓ D ∧ ℓ < 2 ^ slyW N B ℓ D ∧
      E < 2 ^ slyW N B ℓ D := by
  have h2 : ∀ x y, x ≤ y → 2 ^ x ≤ 2 ^ y := fun x y h => Nat.pow_le_pow_right (by norm_num) h
  refine ⟨?_, by simp [slyW]; omega, ?_, ?_⟩
  · calc (N + 1) ^ N ≤ (2 ^ N) ^ N := Nat.pow_le_pow_left Nat.lt_two_pow_self N
      _ = 2 ^ (N * N) := by rw [← pow_mul]
      _ < 2 ^ (N * N + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ slyW N B ℓ D := h2 _ _ (by simp [slyW]; omega)
  · exact lt_of_lt_of_le Nat.lt_two_pow_self (h2 _ _ (by simp [slyW]; omega))
  · exact lt_of_lt_of_le hE (h2 _ _ (by simp [slyW]; omega))

/-! ### The transforms -/

section Spec

variable {Q Ka : ℕ} {U : Type} (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
  (hA : 14 ≤ prime + Ka) (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
  (hgate : ∀ g, Instr.gate g ∈ program Cost.brDirs →
    (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
include hA hA9 hNW hgate

/-- **The forward synthetic transform with its layout program.** `synFwd_spec_br` at
`layP := slyFwd`: the precondition parks `W` and `E` (`slyPk W E`); the records have
`B = 2^l w` symbols; the word width `W` satisfies the conditions of the writer. -/
theorem slyFwd_spec_br {d : ℕ} (a : Fin d → ℕ) {ℓ K l w p : ℕ}
    (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a ≤ l + 1) (hpw : p + 2 ≤ w)
    (v₀ : SynW → List (Fin (prime + Ka + 4)))
    (hv₀ : SynV v₀ (List.ofFn a) ℓ K w l 0 (layPerm (List.ofFn a) ℓ K))
    (hvh : v₀ (.p .h) = []) (hvt : v₀ (.p .t) = []) (hvc : (v₀ (.p .c)).length = nRounds a)
    (hcb : blank ∉ v₀ (.p .c)) (W E : ℕ)
    (hE : ∀ i < (List.ofFn a).length, ax (List.ofFn a) i = ℓ - 1 + E / 2 ^ i % 2) (hEW : E < 2 ^ W)
    (hW : ((List.ofFn a).sum + 1) ^ (List.ofFn a).sum < 2 ^ W)
    (hWB : (List.ofFn a).sum + 2 ^ l * w + 4 ≤ W) (hℓW : ℓ < 2 ^ W) :
    SynFwdSpec (layerTable (Ka := Ka) (U := U) hQ Cost.brDirs) (synFwd Cost.brDirs (slyFwd hQ))
      (lreg .io) (synPre (slyPk W E) v₀) w p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (slyFwdCost Ka (List.ofFn a) ℓ K l w W E v₀ +
        synLoopFCost Cost.brDirs (List.ofFn a) ℓ K w l (nRounds a)
          (synStashCostW v₀ synXS + 6 * nRounds a + 6)) :=
  synFwd_spec_br hQ hA hA9 hNW hgate a H hAl hpw v₀ hv₀ hvh hvt hvc hcb (slyPk W E) (slyFwd hQ) _
    (slyFwd_lay hQ Cost.brDirs a H v₀ hv₀ (by omega) (by omega) W E hE hEW hW hWB hℓW)

/-- **The opposite synthetic transform with its layout program.** `synOpp_spec_br` at
`layQ := slyOpp`, with the same parameters. -/
theorem slyOpp_spec_br {d : ℕ} (a : Fin d → ℕ) {ℓ K l w p : ℕ}
    (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a ≤ l + 1) (hpw : p + 2 ≤ w)
    (v₀ : SynW → List (Fin (prime + Ka + 4)))
    (hv₀ : SynV v₀ (List.ofFn a) ℓ K w l 0 (layPerm (List.ofFn a) ℓ K))
    (hvh : v₀ (.p .h) = []) (hvt : v₀ (.p .t) = []) (hvc : (v₀ (.p .c)).length = nRounds a)
    (hcb : blank ∉ v₀ (.p .c)) (W E : ℕ)
    (hE : ∀ i < (List.ofFn a).length, ax (List.ofFn a) i = ℓ - 1 + E / 2 ^ i % 2) (hEW : E < 2 ^ W)
    (hW : ((List.ofFn a).sum + 1) ^ (List.ofFn a).sum < 2 ^ W)
    (hWB : (List.ofFn a).sum + 2 ^ l * w + 4 ≤ W) (hℓW : ℓ < 2 ^ W) :
    SynOppSpec (layerTable (Ka := Ka) (U := U) hQ Cost.brDirs) (synOpp Cost.brDirs (slyOpp hQ))
      (lreg .io) (synPre (slyPk W E) v₀) w p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (synLoopOCost Cost.brDirs (List.ofFn a) ℓ K w l (nRounds a)
          (synStashCostW v₀ synXS + 6 * nRounds a + 6) +
        slyOppCost Ka (List.ofFn a) ℓ K l w W E v₀) :=
  synOpp_spec_br hQ hA hA9 hNW hgate a H hAl hpw v₀ hv₀ hvh hvt hvc hcb (slyPk W E) (slyOpp hQ) _
    (slyOpp_lay hQ Cost.brDirs a H v₀ hv₀ (by omega) (by omega) W E hE hEW hW hWB hℓW)

end Spec

end IntegerMultBounds.MathlibTM2.Fast
