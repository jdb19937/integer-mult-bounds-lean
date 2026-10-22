module

public import IntegerMultBounds.MathlibTM2.Routing.SelfRead
public import IntegerMultBounds.MathlibTM2.Routing.PhysicalBits

/-!
# Physical source coordinates inside target digit guards

A descriptor selects a digit and a bit of its upper part. Its source is therefore
at physical position `K * digit + bit + 1`, outside the selected digit low bits.
The list order is arbitrary. This module binds those actual bits to the self-read
address permutation; it makes no claim that a mask scanner implements that order.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.Packed

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

/-- Explicit source reader from the current list of upper target digits. -/
def upperRead {n : ℕ} (s : Fin n → Fin n × ℕ) (us : List ℤ) : List ℤ :=
  Coordinates.read s (fun k => (us[k.1.val]!).toNat.testBit k.2)

@[simp] theorem upperRead_length {n : ℕ} (s : Fin n → Fin n × ℕ) (us : List ℤ) :
    (upperRead s us).length = n := Coordinates.read_length _ _

theorem upperRead_bits {n : ℕ} (s : Fin n → Fin n × ℕ) (us : List ℤ) :
    Bits (upperRead s us) := Coordinates.read_bits _ _

private theorem upper_bit (K x r : ℕ) (hr : r + 1 < K) :
    (((x : ℤ) % (2 : ℤ) ^ K) / 2).toNat.testBit r = x.testBit (r + 1) := by
  have hc : ((x : ℤ) % (2 : ℤ) ^ K) / 2 = (((x % 2 ^ K) / 2 : ℕ) : ℤ) := by
    simp
  rw [hc, Int.toNat_natCast]
  have ht := Nat.testBit_div_two_pow (n := 1) (x % 2 ^ K) r
  simpa [hr] using ht

/-- Observing an upper digit bit is observing the corresponding physical bit. -/
theorem upper_digits_bits (K n x r : ℕ) (hr : r + 1 < K) :
    ((digits ((2 : ℤ) ^ K) n (x : ℤ)).map (fun v => v / 2)).map
      (fun u => u.toNat.testBit r) =
        List.ofFn fun j : Fin n => x.testBit (K * j.val + r + 1) := by
  induction n generalizing x with
  | zero => simp [digits]
  | succ n ih =>
    rw [digits, List.map_cons, List.map_cons, List.ofFn_succ]
    have hd : (x : ℤ) / (2 : ℤ) ^ K = ((x / 2 ^ K : ℕ) : ℤ) := by simp
    rw [hd, ih]
    congr 1
    · simpa using upper_bit K x r hr
    · congr 1
      funext j
      simp [Nat.testBit_div_two_pow, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- The explicit reader selects exactly the described physical source bits. -/
theorem upperRead_physical {n : ℕ} (s : Fin n → Fin n × ℕ)
    (K : ℕ) (hs : ∀ j, (s j).2 + 1 < K) (x : ℕ) :
    (upperRead s ((digits ((2 : ℤ) ^ K) n (x : ℤ)).map (fun v => v / 2))).map parity =
      List.ofFn fun j => x.testBit (K * (s j).1.val + (s j).2 + 1) := by
  rw [upperRead, Coordinates.read_parities]
  congr 1
  funext j
  have hb := upper_digits_bits K n x (s j).2 (hs j)
  have hj := congrArg (fun l : List Bool => l[(s j).1.val]!) hb
  simpa [digits_length] using hj

/-- Arbitrarily ordered upper-bit sources drive the actual packed permutation. -/
theorem selfRead_physical {n : ℕ} (s : Fin n → Fin n × ℕ)
    (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) (K : ℕ) (hK : 0 < K)
    (hbase : 2 * L = (2 : ℤ) ^ K) (hs : ∀ j, (s j).2 + 1 < K)
    (x : LateAddress B L n) (hx : lateGood B L n x) (j : Fin n) :
    let y := selfRead B L hB hL n (upperRead s) x
    y.2.1.val.toNat.testBit (K * j.val) =
      Bool.xor (x.2.1.val.toNat.testBit (K * j.val))
        (x.2.1.val.toNat.testBit (K * (s j).1.val + (s j).2 + 1)) := by
  let y := selfRead B L hB hL n (upperRead s) x
  obtain ⟨_, _, _, hp⟩ := selfRead_endpoint B L hB hL (upperRead s) x hx
    (upperRead_length s _) (upperRead_bits s _)
  have dx := parities_digits K hK n x.2.1.val.toNat
  have dy := parities_digits K hK n y.2.1.val.toNat
  have ds := upperRead_physical s K hs x.2.1.val.toNat
  rw [Int.toNat_of_nonneg x.2.1.property.1, ← hbase] at dx ds
  rw [Int.toNat_of_nonneg y.2.1.property.1, ← hbase] at dy
  rw [dy, dx] at hp
  change _ = List.zipWith Bool.xor _
    ((upperRead s ((digits (2 * L) n x.2.1.val).map (fun v => v / 2))).map parity) at hp
  rw [ds] at hp
  have hj := congrArg (fun l : List Bool => l[j.val]!) hp
  simpa using hj

end IntegerMultBounds.MathlibTM2.Routing.Packed
