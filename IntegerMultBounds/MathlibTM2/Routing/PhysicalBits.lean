module

public import IntegerMultBounds.MathlibTM2.Routing.Coordinates
public import Mathlib.Data.Nat.Bitwise

/-!
# Physical positions of packed target bits

Radix digits of width `K` have their low bits at `K*j`. A prefix shifts those
positions by its width. These identities identify actual binary coordinates;
they do not implement a permutation of fields on the record stream.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.Packed

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

@[simp] theorem parity_natCast (x : ℕ) : parity (x : ℤ) = x.testBit 0 := by
  rw [Nat.testBit_zero]
  change decide (((x % 2 : ℕ) : ℤ) = ((1 : ℕ) : ℤ)) = _
  simp only [Int.natCast_inj]

/-- Digit parities are exactly the evenly spaced physical bits. -/
theorem parities_digits (K : ℕ) (hK : 0 < K) (n x : ℕ) :
    (digits ((2 : ℤ) ^ K) n (x : ℤ)).map parity =
      List.ofFn fun j : Fin n => x.testBit (K * j.val) := by
  induction n generalizing x with
  | zero => simp [digits]
  | succ n ih =>
    rw [digits, List.map_cons, List.ofFn_succ]
    have hmod : (x : ℤ) % (2 : ℤ) ^ K = ((x % 2 ^ K : ℕ) : ℤ) := by
      simp
    have hdiv : (x : ℤ) / (2 : ℤ) ^ K = ((x / 2 ^ K : ℕ) : ℤ) := by
      simp
    rw [hmod, hdiv, parity_natCast, ih]
    congr 1
    · simp [hK]
    · congr 1
      funext j
      simp [Nat.testBit_div_two_pow, Nat.mul_add]

/-- Lower spectators move the selected positions but are not part of the packed digits. -/
theorem parities_digits_offset (ρ K : ℕ) (hK : 0 < K) (n x : ℕ) :
    (digits ((2 : ℤ) ^ K) n ((x / 2 ^ ρ : ℕ) : ℤ)).map parity =
      List.ofFn fun j : Fin n => x.testBit (ρ + K * j.val) := by
  rw [parities_digits K hK]
  congr 1
  funext j
  simp [Nat.testBit_div_two_pow, Nat.add_comm]

/-- The actual packed program toggles the physical target bits by the specified
source coordinates. `hbase` ties the arithmetic radix to the physical digit width. -/
theorem program_physical {σ : Type*} {n : ℕ} (s : Fin n → σ)
    (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) (K : ℕ) (hK : 0 < K)
    (hbase : 2 * L = (2 : ℤ) ^ K)
    (x : (σ → Bool) × LateAddress B L n) (hx : lateGood B L n x.2) (j : Fin n) :
    let y := program B L hB hL (Coordinates.read s) (Coordinates.read_length s) x
    y.2.2.1.val.toNat.testBit (K * j.val) =
      Bool.xor (x.2.2.1.val.toNat.testBit (K * j.val)) (x.1 (s j)) := by
  let y := program B L hB hL (Coordinates.read s) (Coordinates.read_length s) x
  obtain ⟨_, _, _, _, hp⟩ := program_endpoint B L hB hL
    (Coordinates.read s) (Coordinates.read_length s) (Coordinates.read_bits s) x hx
  have dx := parities_digits K hK n x.2.2.1.val.toNat
  have dy := parities_digits K hK n y.2.2.1.val.toNat
  rw [Int.toNat_of_nonneg x.2.2.1.property.1, ← hbase] at dx
  rw [Int.toNat_of_nonneg y.2.2.1.property.1, ← hbase] at dy
  rw [dy, dx, Coordinates.read_parities] at hp
  have hj := congrArg (fun l : List Bool => l[j.val]!) hp
  simpa using hj

/-- The target placement is injective and fits in the specified middle field. -/
theorem positions (ρ K n : ℕ) (hK : 0 < K) :
    Function.Injective (fun j : Fin n => ρ + K * j.val) ∧
      ∀ j : Fin n, ρ ≤ ρ + K * j.val ∧ ρ + K * j.val < ρ + K * n := by
  constructor
  · intro i j hij
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left hK (Nat.add_left_cancel hij)
  · intro j
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left j.isLt hK) _⟩

end IntegerMultBounds.MathlibTM2.Routing.Packed
