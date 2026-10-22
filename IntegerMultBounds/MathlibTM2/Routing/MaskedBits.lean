module

public import IntegerMultBounds.MathlibTM2.Routing.MaskedSelfRead
public import IntegerMultBounds.MathlibTM2.Routing.SourceBits

/-!
# Physical coordinates of masked self-reading shears

A source descriptor names any bit of a packed target digit except the low bit of
an active digit. Inactive low bits are allowed. The reader decodes the preserved
source observation, and the actual masked modular program toggles precisely the
active target coordinates by those physical source bits.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.Packed

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

/-- All bits of a radix digit have their usual physical positions. -/
theorem digits_bits (K n x r : ℕ) (hr : r < K) :
    (digits ((2 : ℤ) ^ K) n (x : ℤ)).map (fun v => v.toNat.testBit r) =
      List.ofFn fun j : Fin n => x.testBit (K * j.val + r) := by
  induction n generalizing x with
  | zero => simp [digits]
  | succ n ih =>
    rw [digits, List.map_cons, List.ofFn_succ]
    have hm : (x : ℤ) % (2 : ℤ) ^ K = ((x % 2 ^ K : ℕ) : ℤ) := by simp
    have hd : (x : ℤ) / (2 : ℤ) ^ K = ((x / 2 ^ K : ℕ) : ℤ) := by simp
    rw [hm, hd, Int.toNat_natCast, ih]
    congr 1
    · simp [hr]
    · congr 1
      funext j
      simp [Nat.testBit_div_two_pow, Nat.mul_add, Nat.add_comm,
        Nat.add_left_comm]

private theorem visible_bit (a : Bool) (v : ℤ) (hv : 0 ≤ v) (r : ℕ)
    (hr : a = true → 0 < r) :
    (if a then v / 2 else v).toNat.testBit (if a then r - 1 else r) = v.toNat.testBit r := by
  cases a with
  | false => rfl
  | true =>
    have hr' : 1 ≤ r := hr rfl
    cases v with
    | ofNat v =>
      change (v / 2).testBit (r - 1) = v.testBit r
      have h := Nat.testBit_div_two_pow (n := 1) v (r - 1)
      simpa [Nat.sub_add_cancel hr'] using h
    | negSucc v => omega

/-- Read physical source bits from the source observation of a masked early pass. -/
def maskedRead {n : ℕ} (active : List Bool) (s : Fin n → Fin n × ℕ)
    (vs : List ℤ) : List ℤ :=
  Coordinates.read s fun k =>
    (vs[k.1.val]!).toNat.testBit (if active[k.1.val]! then k.2 - 1 else k.2)

@[simp] theorem maskedRead_length {n : ℕ} (active : List Bool) (s : Fin n → Fin n × ℕ)
    (vs : List ℤ) : (maskedRead active s vs).length = n := Coordinates.read_length _ _

theorem maskedRead_bits {n : ℕ} (active : List Bool) (s : Fin n → Fin n × ℕ)
    (vs : List ℤ) : Bits (maskedRead active s vs) := Coordinates.read_bits _ _

/-- Source bits may lie at inactive digit starts; active digit starts are excluded. -/
theorem maskedRead_physical {n : ℕ} (active : List Bool) (ha : active.length = n)
    (s : Fin n → Fin n × ℕ) (K : ℕ) (hs : ∀ j, (s j).2 < K)
    (hsource : ∀ j, active[(s j).1.val]! = true → 0 < (s j).2) (x : ℕ) :
    (maskedRead active s (visible active (digits ((2 : ℤ) ^ K) n (x : ℤ)))).map parity =
      List.ofFn fun j => x.testBit (K * (s j).1.val + (s j).2) := by
  rw [maskedRead, Coordinates.read_parities]
  congr 1
  funext j
  have hq : (s j).1.val < (digits ((2 : ℤ) ^ K) n (x : ℤ)).length := by
    simpa only [digits_length] using (s j).1.isLt
  have hmem : (digits ((2 : ℤ) ^ K) n (x : ℤ))[(s j).1.val]! ∈
      digits ((2 : ℤ) ^ K) n (x : ℤ) := by
    rw [getElem!_pos (digits ((2 : ℤ) ^ K) n (x : ℤ)) (s j).1.val hq]
    exact List.getElem_mem hq
  have hv := (digits_bounded ((2 : ℤ) ^ K) (by positivity) n (x : ℤ) _ hmem).1
  have hview : (visible active (digits ((2 : ℤ) ^ K) n (x : ℤ)))[(s j).1.val]! =
      if active[(s j).1.val]! then
        (digits ((2 : ℤ) ^ K) n (x : ℤ))[(s j).1.val]! / 2
      else (digits ((2 : ℤ) ^ K) n (x : ℤ))[(s j).1.val]! := by
    simp [visible, ha, digits_length, (s j).1.isLt]
  rw [hview, visible_bit _ _ hv _ (hsource j)]
  have hb := digits_bits K n x (s j).2 (hs j)
  have hj := congrArg (fun l : List Bool => l[(s j).1.val]!) hb
  simpa [digits_length] using hj

/-- Masking commutes with observing digit parity. -/
theorem parities_maskBits (active : List Bool) (zs : List ℤ) :
    (maskBits active zs).map parity = List.zipWith Bool.and active (zs.map parity) := by
  induction active generalizing zs with
  | nil => simp [maskBits]
  | cons a active ih =>
    cases zs with
    | nil => simp [maskBits]
    | cons z zs =>
      change parity (if a then z else 0) :: (maskBits active zs).map parity =
        (a && parity z) :: List.zipWith Bool.and active (zs.map parity)
      rw [ih]
      cases a <;> simp [parity]

/-- Actual physical selective XOR, including sources at inactive low bits. -/
theorem maskedSelfRead_physical {n : ℕ} (active : List Bool) (ha : active.length = n)
    (s : Fin n → Fin n × ℕ) (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (K : ℕ) (hK : 0 < K) (hbase : 2 * L = (2 : ℤ) ^ K)
    (hs : ∀ j, (s j).2 < K)
    (hsource : ∀ j, active[(s j).1.val]! = true → 0 < (s j).2)
    (x : LateAddress B L n) (hx : lateGood B L n x) (j : Fin n) :
    let y := maskedSelfRead B L hB hL active (maskedRead active s) x
    y.2.1.val.toNat.testBit (K * j.val) =
      Bool.xor (x.2.1.val.toNat.testBit (K * j.val))
        (active[j.val]! && x.2.1.val.toNat.testBit (K * (s j).1.val + (s j).2)) := by
  let y := maskedSelfRead B L hB hL active (maskedRead active s) x
  have hz := maskedRead_bits active s (sourceView B L active x.2)
  have hlen := maskedRead_length active s (sourceView B L active x.2)
  have he := maskedSelfRead_good B L hB hL active ha (maskedRead active s) x hx hlen hz
  have hp : (digits (2 * L) n y.2.1.val).map parity =
      List.zipWith Bool.xor ((digits (2 * L) n x.2.1.val).map parity)
        ((maskBits active (maskedRead active s (sourceView B L active x.2))).map parity) := by
    dsimp only [y]
    rw [he, ideal_digits]
    exact parities_toggleList _ _ (maskBits_bits active _ hz)
  have dx := parities_digits K hK n x.2.1.val.toNat
  have dy := parities_digits K hK n y.2.1.val.toNat
  have ds := maskedRead_physical active ha s K hs hsource x.2.1.val.toNat
  rw [Int.toNat_of_nonneg x.2.1.property.1, ← hbase] at dx ds
  rw [Int.toNat_of_nonneg y.2.1.property.1, ← hbase] at dy
  rw [dy, dx, parities_maskBits] at hp
  change _ = List.zipWith Bool.xor _
    (List.zipWith Bool.and active ((maskedRead active s
      (visible active (digits (2 * L) n x.2.1.val))).map parity)) at hp
  rw [ds] at hp
  have hj := congrArg (fun l : List Bool => l[j.val]!) hp
  simpa [ha, j.isLt] using hj

end IntegerMultBounds.MathlibTM2.Routing.Packed
