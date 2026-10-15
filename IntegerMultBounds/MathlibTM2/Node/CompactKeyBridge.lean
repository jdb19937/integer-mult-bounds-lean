module

public import IntegerMultBounds.MathlibTM2.Node.KeyPass
public import IntegerMultBounds.MathlibTM2.Node.RotGen

/-!
# The key pass computes the ideal map of the compact program

The key pass `keyPassAt Y X` (`Node/KeyPass.lean`) prefixes the record at index `i` with the
field digits of `i`, least significant field first, the digit of field `Y` replaced by
`y ⊕ (x ∧ selMask K ρ n)`. The ideal map of the compact slot XOR
(`IntegerMultBounds.MathlibTM2.Layer.CompactXor.idealC`) is `setDig Y i` of the same value, so
the key of record `i` is the numeral of `idealC i` in `∑ len` bits (`keyBitsAt_eq_idealC`), and
the keyed stream is `keyRecs` of the permutation `idealPerm` (`keyedFrom_eq_keyRecs_ideal`).

The field digits of an index are the pieces of its numeral between the field offsets
(`binSyms_sum_fields`): `binSyms_split` splits the numeral at each offset, `binSyms_mod` drops
the modulus of a digit.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer.CompactXor
open IntegerMultBounds.MathlibTM2.Layer.PackedXor (selMask)

variable {A : ℕ}

/-- Splitting a numeral at bit `L`. -/
lemma binSyms_split (L e x : ℕ) :
    (binSyms (L + e) x : List (Fin (A + 4))) = binSyms L x ++ binSyms e (x / 2 ^ L) := by
  induction L generalizing x with
  | zero => simp [binSyms]
  | succ L ih =>
      rw [Nat.add_right_comm, binSyms_succ, binSyms_succ, ih, pow_succ', ← Nat.div_div_eq_div_mul]
      rfl

/-- A digit written in its own width is the shifted index. -/
lemma binSyms_digit (len : Fin 8 → ℕ) (f : Fin 8) (i : ℕ) :
    (binSyms (len f) (digit len f i) : List (Fin (A + 4))) =
      binSyms (len f) (i / 2 ^ fieldOff len f) := by
  rw [digit, binSyms_mod]

/-- The numeral of an index in `∑ len` bits is the concatenation of its field digits, least
significant field first. -/
lemma binSyms_sum_fields (len : Fin 8 → ℕ) (i : ℕ) :
    (binSyms (∑ j, len j) i : List (Fin (A + 4))) =
      (List.finRange 8).flatMap fun j => binSyms (len j) (digit len j i) := by
  simp only [binSyms_digit]
  rw [Fin.sum_univ_eight]
  simp only [binSyms_split, List.append_assoc]
  simp [List.finRange_succ, fieldOff, Finset.sum_filter, Fin.sum_univ_eight, pow_add]

/-- The key of the record at index `i` is the numeral of `idealC i`. -/
lemma keyBitsAt_eq_idealC (len : Fin 8 → ℕ) (X Y : Fin 8) (hLXY : len X = len Y) (K ρ n i : ℕ) :
    keyBitsAt (A := A) Y X len (selMask K ρ n) i =
      binSyms (∑ j, len j) (idealC len X Y K ρ n i) := by
  rw [keyBitsAt, binSyms_sum_fields]
  congr 1
  funext j
  simp only [keyDig, ← dig_eq_digit]
  split_ifs with hj
  · rw [hj, dig_idealC_Y len hLXY]
  · rw [dig_idealC_ne len hLXY hj]

/-- The keyed stream of the key pass is `keyRecs` of the ideal permutation. -/
theorem keyedFrom_eq_keyRecs_ideal (len : Fin 8 → ℕ) (X Y : Fin 8) (hXY : X ≠ Y)
    (hLXY : len X = len Y) (K ρ n R S : ℕ) (hSY : foff len Y + len Y ≤ S)
    (l : List (List (Fin (A + 4)))) (hl : l.length = R * 2 ^ S) :
    keyedFrom (keyBitsAt Y X len (selMask K ρ n)) 0 l =
      keyRecs (∑ j, len j) (idealPerm len K ρ n hXY hLXY hSY (R := R) (S := S)) l := by
  rw [keyedFrom_eq, keyRecs, hl]
  symm
  refine ofFn_eq_range_map _ _ fun j => ?_
  rw [Nat.zero_add, idealPerm_apply, keyBitsAt_eq_idealC len X Y hLXY]

end IntegerMultBounds.MathlibTM2.Node
