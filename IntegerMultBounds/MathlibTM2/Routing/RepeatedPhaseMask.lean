module

public import IntegerMultBounds.MathlibTM2.Routing.WordRepeatValue
public import IntegerMultBounds.MathlibTM2.Layer.CompactBad

/-! R2's phase classifier mask consists of repeated three-mark blocks and one
final boundary mark. The identity is structural in the number of blocks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open Finset

def phaseBlockValue (G : ℕ) : ℕ := 1 + 2 + 2 ^ (G + 1)

theorem phaseMask_grouped (n G stride offset : ℕ) :
    maskVal (n * 3) (fun j => offset + j / 3 * stride + mOff G (j % 3)) =
      2 ^ offset * repeatBlockValue n stride (phaseBlockValue G) := by
  induction n with
  | zero => simp [maskVal, repeatBlockValue]
  | succ n ih =>
    have ht : (∑ i ∈ range 3, 2 ^ (offset + (n * 3 + i) / 3 * stride + mOff G ((n * 3 + i) % 3))) =
        2 ^ offset * (2 ^ (n * stride) * phaseBlockValue G) := by
      have he : (∑ i ∈ range 3, 2 ^ (offset + (n * 3 + i) / 3 * stride + mOff G ((n * 3 + i) % 3))) =
          ∑ i ∈ range 3, 2 ^ (offset + n * stride + mOff G i) := by
        apply sum_congr rfl
        intro i hi
        have hi3 := mem_range.mp hi
        rw [Nat.add_comm (n * 3) i, Nat.add_mul_div_right _ _ (by decide : 0 < 3),
          Nat.div_eq_of_lt hi3, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi3]
      rw [he]
      simp [sum_range_succ, mOff, phaseBlockValue, pow_add]
      ring
    change (∑ j ∈ range ((n + 1) * 3), 2 ^ (offset + j / 3 * stride + mOff G (j % 3))) = _
    rw [Nat.add_mul, Nat.one_mul, sum_range_add]
    change maskVal (n * 3) (fun j => offset + j / 3 * stride + mOff G (j % 3)) + _ = _
    rw [ih, ht]
    simp only [repeatBlockValue, sum_range_succ]
    ring

theorem phaseMask_repeatBlocks (p : Par) :
    mkV p = 2 ^ p.ρ * (repeatBlockValue p.n p.K (phaseBlockValue p.G) + 2 ^ (p.n * p.K)) := by
  have hg : maskVal (3 * p.n) (posM p) = 2 ^ p.ρ * repeatBlockValue p.n p.K (phaseBlockValue p.G) := by
    change maskVal (3 * p.n) (fun j => p.ρ + j / 3 * p.K + mOff p.G (j % 3)) = _
    rw [Nat.mul_comm 3 p.n]
    exact phaseMask_grouped p.n p.G p.K p.ρ
  have hp : posM p (3 * p.n) = p.ρ + p.n * p.K := by
    simp [posM, posS, mOff]
  unfold mkV
  rw [maskVal, sum_range_succ]
  change maskVal (3 * p.n) (posM p) + 2 ^ posM p (3 * p.n) = _
  rw [hg, hp, pow_add]
  ring

end IntegerMultBounds.MathlibTM2.Routing
