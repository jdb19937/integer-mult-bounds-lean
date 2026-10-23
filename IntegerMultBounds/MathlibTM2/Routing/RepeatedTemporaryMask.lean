module

public import IntegerMultBounds.MathlibTM2.Routing.WordRepeatValue
public import IntegerMultBounds.MathlibTM2.Node.CompactCode

/-! The actual temporary classifier mask is a repeated block value, shifted
by the selected-bit offset. No finite certificate or case enumeration is used. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open Finset

theorem maskVal_grouped (n G stride offset : ℕ) (hG : 0 < G) :
    maskVal (n * G) (fun j => offset + j / G * stride + 1 + j % G) =
      2 ^ (offset + 1) * repeatBlockValue n stride (maskVal G id) := by
  induction n with
  | zero => simp [maskVal, repeatBlockValue]
  | succ n ih =>
    have ht : (∑ i ∈ range G, 2 ^ (offset + (n * G + i) / G * stride + 1 + (n * G + i) % G)) =
        2 ^ (offset + 1) * (2 ^ (n * stride) * maskVal G id) := by
      simp only [maskVal, mul_sum]
      apply sum_congr rfl
      intro i hi
      have hiG := mem_range.mp hi
      rw [Nat.add_comm (n * G) i, Nat.add_mul_div_right _ _ hG, Nat.div_eq_of_lt hiG,
        Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hiG]
      simp only [pow_add, id_eq]
      ring
    change (∑ j ∈ range ((n + 1) * G), 2 ^ (offset + j / G * stride + 1 + j % G)) = _
    rw [Nat.add_mul, Nat.one_mul, sum_range_add]
    change maskVal (n * G) (fun j => offset + j / G * stride + 1 + j % G) + _ = _
    rw [ih, ht]
    simp only [repeatBlockValue, sum_range_succ]
    ring

theorem temporaryMask_repeatBlocks (p : Par) (hG : 0 < p.G) :
    IntegerMultBounds.MathlibTM2.Node.mAV p = 2 ^ (p.ρ + 1) * repeatBlockValue p.n p.K (maskVal p.G id) := by
  exact maskVal_grouped p.n p.G p.K p.ρ hG

end IntegerMultBounds.MathlibTM2.Routing
