module

public import IntegerMultBounds.MathlibTM2.Routing.SourceRot

/-!
# The executed source rotation is the packed modular load

The concrete rank permutation of `sourceRotate_exec` changes its target field by
exactly the signed packed source offset modulo the complete field width. This
identifies both load and unload on every address, without any guard hypothesis.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

private theorem rotv_int (w off a : ℕ) (neg : Bool) (hoff : off < 2 ^ w) :
    (rotv w neg off a : ℤ) =
      ((a : ℤ) + (if neg then -(off : ℤ) else (off : ℤ))) % (2 : ℤ) ^ w := by
  cases neg with
  | false => simp [rotv]
  | true =>
    simp only [rotv, ite_true, Nat.mod_eq_of_lt hoff]
    have hle : off ≤ 2 ^ w := hoff.le
    have hc : ((a + (2 ^ w - off) : ℕ) : ℤ) =
        (a : ℤ) + ((2 : ℤ) ^ w - (off : ℤ)) := by push_cast [hle]; rfl
    rw [Int.natCast_emod, hc]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    rw [show (a : ℤ) + ((2 : ℤ) ^ w - (off : ℤ)) =
      ((a : ℤ) - (off : ℤ)) + (2 : ℤ) ^ w by ring, Int.add_emod_right]
    rfl

/-- The executed compact offset is exactly the packed source digit list. -/
theorem sourceValue_packed {nf W n G : ℕ} (len : Fin nf → ℕ) (fs : Fin nf)
    (s : Fin n → Fin W) (i : ℕ) :
    (sourceValue len fs G s i : ℤ) =
      pack ((2 : ℤ) ^ G) (Coordinates.read s (fun k => (digit len fs i).testBit k.val)) :=
  (readOffset_value s (digit len fs i) G).symm

/-- On every address the executed rank map is a signed modular packed load.
For `neg = false` this loads; for `neg = true` it unloads the current source value. -/
theorem sourceRotation_field {nf W n G : ℕ} (len : Fin nf → ℕ) (fs ft : Fin nf)
    (ht : len ft = n * G) (hG : 0 < G) (s : Fin n → Fin W) (neg : Bool) (i : ℕ) :
    (digit len ft (rotIdx len ft neg (sourceValue len fs G s) i) : ℤ) =
      ((digit len ft i : ℤ) +
        (if neg then -pack ((2 : ℤ) ^ G)
          (Coordinates.read s (fun k => (digit len fs i).testBit k.val))
        else pack ((2 : ℤ) ^ G)
          (Coordinates.read s (fun k => (digit len fs i).testBit k.val)))) %
            ((2 : ℤ) ^ G) ^ n := by
  rw [digit_rotIdx, ht, rotv_int _ _ _ neg (sourceValue_lt fs hG s i), sourceValue_packed]
  rw [← pow_mul, Nat.mul_comm G n]

end IntegerMultBounds.MathlibTM2.Routing
