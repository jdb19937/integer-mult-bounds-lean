module

public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The primes of a window, in order

The machine search of `Primes/PrimeTest.lean` steps from a candidate to the least prime above
it. This file describes its outputs.

* `nextPrimeAfter x`: the least prime above `x`. `primes_Ioc_nextPrimeAfter`: it is the only
  prime in `(x, nextPrimeAfter x]`.
* `windowPrime lo k = nextPrimeAfter^[k+1] lo`: the `k`-th prime above `lo`, from `0`. The
  sequence is strictly increasing (`windowPrime_strictMono`), and `(lo, windowPrime lo k]` holds
  exactly its first `k + 1` terms (`card_primes_Ioc_windowPrime`).
* `windowPrime_le_of_card`, `windowPrime_mem`: when `(lo, hi]` holds at least `d` primes, the
  first `d` window primes lie in it. `image_windowPrime`: they are all of its primes when `d` is
  their number.
-/

@[expose] public section

namespace IntegerMultBounds.Primes

/-- The least prime above `x`. -/
def nextPrimeAfter (x : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (x + 1))

theorem nextPrimeAfter_spec (x : ℕ) : x + 1 ≤ nextPrimeAfter x ∧ (nextPrimeAfter x).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (x + 1))

theorem lt_nextPrimeAfter (x : ℕ) : x < nextPrimeAfter x := (nextPrimeAfter_spec x).1

theorem nextPrimeAfter_prime (x : ℕ) : (nextPrimeAfter x).Prime := (nextPrimeAfter_spec x).2

/-- No prime lies strictly between `x` and `nextPrimeAfter x`. -/
theorem nextPrimeAfter_le {x q : ℕ} (hxq : x < q) (hq : q.Prime) : nextPrimeAfter x ≤ q :=
  Nat.find_min' _ ⟨hxq, hq⟩

theorem not_prime_of_lt_nextPrimeAfter {x q : ℕ} (hxq : x < q) (hq : q < nextPrimeAfter x) :
    ¬ q.Prime :=
  fun hp => absurd (nextPrimeAfter_le hxq hp) (not_le.mpr hq)

/-- The primes in `(x, nextPrimeAfter x]`: only `nextPrimeAfter x`. -/
theorem primes_Ioc_nextPrimeAfter (x : ℕ) :
    (Finset.Ioc x (nextPrimeAfter x)).filter Nat.Prime = {nextPrimeAfter x} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hxq, hq⟩, hp⟩
    exact le_antisymm hq (nextPrimeAfter_le hxq hp)
  · rintro rfl
    exact ⟨⟨lt_nextPrimeAfter x, le_rfl⟩, nextPrimeAfter_prime x⟩

/-- The `k`-th prime above `lo`, counting from `0`. -/
def windowPrime (lo k : ℕ) : ℕ := nextPrimeAfter^[k + 1] lo

theorem windowPrime_zero (lo : ℕ) : windowPrime lo 0 = nextPrimeAfter lo := rfl

theorem windowPrime_succ (lo k : ℕ) :
    windowPrime lo (k + 1) = nextPrimeAfter (windowPrime lo k) :=
  Function.iterate_succ_apply' _ _ _

theorem windowPrime_prime (lo k : ℕ) : (windowPrime lo k).Prime := by
  cases k with
  | zero => exact nextPrimeAfter_prime lo
  | succ k => rw [windowPrime_succ]; exact nextPrimeAfter_prime _

theorem windowPrime_lt_succ (lo k : ℕ) : windowPrime lo k < windowPrime lo (k + 1) := by
  rw [windowPrime_succ]
  exact lt_nextPrimeAfter _

theorem windowPrime_strictMono (lo : ℕ) : StrictMono (windowPrime lo) :=
  strictMono_nat_of_lt_succ (windowPrime_lt_succ lo)

theorem lo_lt_windowPrime (lo k : ℕ) : lo < windowPrime lo k :=
  (lt_nextPrimeAfter lo).trans_le ((windowPrime_strictMono lo).monotone (Nat.zero_le k))

/-- `(lo, windowPrime lo k]` holds exactly the first `k + 1` window primes. -/
theorem card_primes_Ioc_windowPrime (lo k : ℕ) :
    ((Finset.Ioc lo (windowPrime lo k)).filter Nat.Prime).card = k + 1 := by
  induction k with
  | zero => rw [windowPrime_zero, primes_Ioc_nextPrimeAfter, Finset.card_singleton]
  | succ k ih =>
    have hsplit : Finset.Ioc lo (windowPrime lo (k + 1)) =
        Finset.Ioc lo (windowPrime lo k) ∪ Finset.Ioc (windowPrime lo k) (windowPrime lo (k + 1)) :=
      (Finset.Ioc_union_Ioc_eq_Ioc (lo_lt_windowPrime lo k).le (windowPrime_lt_succ lo k).le).symm
    have hdisj : Disjoint ((Finset.Ioc lo (windowPrime lo k)).filter Nat.Prime)
        ((Finset.Ioc (windowPrime lo k) (windowPrime lo (k + 1))).filter Nat.Prime) := by
      refine Finset.disjoint_left.mpr fun q hq hq' => ?_
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hq hq'
      omega
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih, windowPrime_succ,
      primes_Ioc_nextPrimeAfter, Finset.card_singleton]

/-- If `(lo, hi]` holds at least `k + 1` primes, the `k`-th window prime is at most `hi`. -/
theorem windowPrime_le_of_card {lo hi k : ℕ}
    (h : k + 1 ≤ ((Finset.Ioc lo hi).filter Nat.Prime).card) : windowPrime lo k ≤ hi := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  cases k with
  | zero =>
    have hempty : (Finset.Ioc lo hi).filter Nat.Prime = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun q hq hp => ?_
      obtain ⟨hlo, hqhi⟩ := Finset.mem_Ioc.mp hq
      have := nextPrimeAfter_le hlo hp
      rw [← windowPrime_zero] at this
      omega
    rw [hempty, Finset.card_empty] at h
    omega
  | succ k =>
    have hsub : (Finset.Ioc lo hi).filter Nat.Prime ⊆
        (Finset.Ioc lo (windowPrime lo k)).filter Nat.Prime := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hq ⊢
      obtain ⟨⟨hlo, hqhi⟩, hp⟩ := hq
      refine ⟨⟨hlo, ?_⟩, hp⟩
      by_contra hgt
      replace hgt := not_le.mp hgt
      have := nextPrimeAfter_le hgt hp
      rw [← windowPrime_succ] at this
      omega
    have := Finset.card_le_card hsub
    rw [card_primes_Ioc_windowPrime] at this
    omega

/-- When `(lo, hi]` holds at least `d` primes, its first `d` window primes lie in it. -/
theorem windowPrime_mem {lo hi d : ℕ} (h : d ≤ ((Finset.Ioc lo hi).filter Nat.Prime).card)
    {k : ℕ} (hk : k < d) : windowPrime lo k ∈ (Finset.Ioc lo hi).filter Nat.Prime :=
  Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨lo_lt_windowPrime lo k,
    windowPrime_le_of_card (by omega)⟩, windowPrime_prime lo k⟩

/-- The window primes enumerate all primes of `(lo, hi]` in increasing order. -/
theorem image_windowPrime (lo hi : ℕ) :
    (Finset.range ((Finset.Ioc lo hi).filter Nat.Prime).card).image (windowPrime lo) =
      (Finset.Ioc lo hi).filter Nat.Prime := by
  set c := ((Finset.Ioc lo hi).filter Nat.Prime).card
  have hsub : (Finset.range c).image (windowPrime lo) ⊆ (Finset.Ioc lo hi).filter Nat.Prime := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
    exact windowPrime_mem le_rfl (Finset.mem_range.mp hk)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_image_of_injective _ (windowPrime_strictMono lo).injective, Finset.card_range]

end IntegerMultBounds.Primes
