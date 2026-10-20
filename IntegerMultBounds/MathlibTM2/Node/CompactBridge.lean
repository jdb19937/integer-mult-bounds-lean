module

public import IntegerMultBounds.MathlibTM2.Node.CompactCore
public import IntegerMultBounds.MathlibTM2.Node.SlotXor

/-!
# From the record index to the slot XOR on an array

`moveRecs_pullAddr`: moving the records of an array `Z` (row by row, `2^n` addresses per row) by a
permutation whose inverse acts on the address of each row as `addrNum σ` gives the records of
`pullAddr σ Z`.

`xorIdx_sxMap`: when slot `y` and slot `x` of the address are the fields `F.y` and `F.x` of the
record index, with column `c` of each at `posS c`, the masked exclusive or with the selected bits
of all `n + 1` columns acts on the address as the slot XOR `sxMap e x y`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.MathlibTM2.Layer (ZArr encZ recList addrBits addrNum pullAddr bitIdx m)

/-- **Moving records by an address map.** -/
theorem moveRecs_pullAddr {A w R r n : ℕ} (σ : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (π : Equiv.Perm (Fin (R * 2 ^ n)))
    (hπ : ∀ j : Fin (R * 2 ^ n), (π.symm j : ℕ) = 2 ^ n * (j / 2 ^ n) + addrNum σ (j % 2 ^ n))
    (Z : ZArr (Fin R × Fin r) n) :
    (moveRecs π ((recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w))).flatten =
      encZ A w (pullAddr σ Z) := by
  rw [sx_encZ_eq_flatten]
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp [length_moveRecs, IntegerMultBounds.MathlibTM2.Layer.length_recList]
  intro j h1 h2
  have hj : j < R * 2 ^ n := by simpa [length_moveRecs] using h1
  have hu : j / 2 ^ n < R := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; linarith [hj]
  have ha : j % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hdec : 2 ^ n * (j / 2 ^ n) + j % 2 ^ n = j := Nat.div_add_mod j (2 ^ n)
  have hlt : 2 ^ n * (j / 2 ^ n) + addrNum σ (j % 2 ^ n) <
      ((recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w)).length := by
    rw [List.length_map, IntegerMultBounds.MathlibTM2.Layer.length_recList]
    have := IntegerMultBounds.MathlibTM2.Layer.addrNum_lt σ (j % 2 ^ n)
    have h3 : 2 ^ n * (j / 2 ^ n + 1) ≤ 2 ^ n * R := Nat.mul_le_mul_left _ hu
    rw [Nat.mul_succ] at h3
    rw [Nat.mul_comm R]; omega
  simp only [moveRecs, List.getElem_ofFn, List.getElem_map]
  rw [hπ ⟨j, hj⟩, List.getD_eq_getElem _ _ hlt, List.getElem_map]
  congr 1
  have := IntegerMultBounds.MathlibTM2.Layer.recList_pull (w := w) σ Z (j / 2 ^ n) hu (j % 2 ^ n) ha
  simp only [hdec] at this
  rw [this]

variable {p : Par} {nf : ℕ} {len : Fin nf → ℕ} {F : Fields nf}

/-- **The selected-bit XOR on the address.** -/
theorem xorIdx_sxMap {k nA : ℕ} (e : Fin (m * k) → Fin nA) (he : Function.Injective e)
    (x y : Fin m) (hK : 0 < p.K) (hk : p.n + 1 = k)
    (hey : ∀ c : Fin k, (e (bitIdx y c) : ℕ) = fieldOff len F.y + posS p c)
    (hex : ∀ c : Fin k, (e (bitIdx x c) : ℕ) = fieldOff len F.x + posS p c)
    (hF : F.Valid p len) (hm : 0 < p.m) (hyA : fieldOff len F.y + len F.y ≤ nA) (i : ℕ) :
    xorIdx len F (Layer.CompactMasks.maskVal (p.n + 1) (posS p)) i =
      2 ^ nA * (i / 2 ^ nA) + addrNum (sxMap e x y) (i % 2 ^ nA) := by
  have hX := hF.xorFields
  have hbit : ∀ (g : Fin nf) (j : ℕ), j < len g →
      (digit len g i).testBit j = i.testBit (fieldOff len g + j) := fun g j hj => by
    rw [digit, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm j]
    simp [hj]
  have hcK : ∀ c : Fin k, posS p c < len F.y := fun c => by
    have := Nat.mul_le_mul_right p.K (show (c : ℕ) ≤ p.n by omega)
    rw [hF.ly]; unfold posS Par.wy; omega
  have hb : ∀ t : Fin nA, addrBits nA (i % 2 ^ nA) t = if i.testBit t then 1 else 0 := fun t => by
    simp only [addrBits, Nat.testBit_mod_two_pow, t.isLt, decide_true, Bool.true_and]
  refine Nat.eq_of_testBit_eq fun t => ?_
  rw [Nat.testBit_two_pow_mul_add _ (IntegerMultBounds.MathlibTM2.Layer.addrNum_lt _ _), xorIdx,
    testBit_setDigit]
  by_cases htA : t < nA
  · simp only [htA, ↓reduceIte]
    rw [sx_testBit_addrNum _ _ _ htA]
    by_cases hy : fieldOff len F.y ≤ t ∧ t < fieldOff len F.y + len F.y
    · simp only [hy, and_self, ↓reduceIte]
      rw [Nat.testBit_xor, Nat.testBit_and,
        Layer.CompactMasks.testBit_maskVal (posS_mono hK), hbit F.y _ (by omega),
        Nat.add_sub_cancel' hy.1]
      by_cases hc : ∃ c < p.n + 1, posS p c = t - fieldOff len F.y
      · obtain ⟨c, hc, hct⟩ := hc
        have ht : e (bitIdx y ⟨c, by omega⟩) = ⟨t, htA⟩ :=
          Fin.ext (by rw [hey]; simp only; omega)
        have hd : decide (∃ c < p.n + 1, posS p c = t - fieldOff len F.y) = true :=
          decide_eq_true ⟨c, hc, hct⟩
        rw [← ht, sxMap_apply_y he, hb, hb, ht, hd, Bool.and_true, sx_zmod2_ite_add,
          hex ⟨c, by omega⟩, ← hbit F.x _ (by rw [hX.len_eq]; exact hcK ⟨c, by omega⟩), ← hct]
      · have hd : decide (∃ c < p.n + 1, posS p c = t - fieldOff len F.y) = false :=
          decide_eq_false hc
        rw [sxMap_apply_ne he _ _ _ _ fun c e' => hc ⟨c, by omega, by
            have h1 : fieldOff len F.y + posS p c = t := by
              rw [← hey]; exact congrArg Fin.val e'
            omega⟩, hb, sx_decide_ite_one, hd, Bool.and_false, Bool.xor_false]
    · simp only [hy, ↓reduceIte]
      rw [sxMap_apply_ne he _ _ _ _ fun c e' => hy (by
          have h1 : fieldOff len F.y + posS p c = t := by
            rw [← hey]; exact congrArg Fin.val e'
          have h2 := hcK c
          omega), hb, sx_decide_ite_one]
  · simp only [htA, ↓reduceIte, show ¬(fieldOff len F.y ≤ t ∧ t < fieldOff len F.y + len F.y) by
      omega]
    rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

end IntegerMultBounds.MathlibTM2.Node
