module

public import IntegerMultBounds.Machine.ArbitraryWidthPieces
public import IntegerMultBounds.MathlibTM2.M8.Machine.Depth

/-!
# Power-width pieces on the network machine

The arbitrary-width partition (`IntegerMultBounds.Machine.ArbitraryWidthPieces`, generic in the
radix) at the radix `width`: every piece of a row field padded to a multiple of `roleCount^k`
meets the power-width shape contract (`piece_shape`), with the parent's logical volume
(`piece_view`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieces
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open IntegerMultBounds.Machine.ArbitraryWidthPieces
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

/-- A common `roleCount^k`-padded row field meets the power-width machine's shape contract for
every depth appearing in the arbitrary-width partition. -/
theorem slice_shape {v : Descriptor} {k j : ℕ} (hp : v.Positive)
    (hrows : roleCount^k ∣ v.rows) (hj : j ≤ k) (offset : ℕ) :
    Depth.Shape j (slice prime v offset (Machine.width^j)) :=
  ⟨slice_positive _ Shared50ModularControl.prime_prime.pos v hp offset _,rfl,
    dvd_trans (pow_dvd_pow roleCount hj) hrows⟩

/-- Every list entry is ready for the power-width shape contract. -/
theorem piece_shape {v : Descriptor} {n k j : ℕ} (hp : v.Positive)
    (hrows : roleCount^k ∣ v.rows) (hj : j ∈ depths Machine.width n k) (offset : ℕ) :
    Depth.Shape j (slice prime v offset (Machine.width^j)) :=
  slice_shape hp hrows (depth_le hj) offset

/-- The power-width shape and logical volume for every arbitrary-width piece. The common
padded row field is retained throughout the piece schedule. -/
theorem piece_view {v : Descriptor} {k : ℕ} (hp : v.Positive)
    (hrows : roleCount^k ∣ v.rows) (hwidth : v.width < Machine.width^(k+1))
    (i : Fin (depths Machine.width v.width k).length) :
    Depth.Shape ((depths Machine.width v.width k)[i])
        (slice prime v (offset Machine.width v.width k i.val)
          (Machine.width^((depths Machine.width v.width k)[i]))) ∧
      volume prime
        (slice prime v (offset Machine.width v.width k i.val)
          (Machine.width^((depths Machine.width v.width k)[i]))) = volume prime v := by
  refine ⟨piece_shape hp hrows (List.getElem_mem i.isLt) _,?_⟩
  exact slice_volume _ v _ _ (offset_fit two_le_width hwidth i)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieces
