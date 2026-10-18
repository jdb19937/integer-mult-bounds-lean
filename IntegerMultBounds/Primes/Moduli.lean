module

public import IntegerMultBounds.Primes.WindowLo
public import IntegerMultBounds.Primes.NextPrime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Prime source lengths

The prime moduli of the transform. The first `a` source lengths are the first `a` primes of the
window below `R`, the other `d - a` the first primes of the window below `2R`:
`primeSrc d a R i`. At `R = 2^e` they fit the axis lengths `Moduli.box d a e`.

* `primeSrc_good`: when the two windows hold enough primes, `primeSrc` and `box` are
  `Moduli.Good`: odd, below and coprime to the axis lengths, pairwise coprime, in the axis
  bounds, with `∏ s < ∏ t < 2 ∏ s`.
* `primeSrc_prime`, `three_le_primeSrc`: every value is a prime, above `3` once `R ≥ 8`.
* `winLo_two_pow`, `winHi_two_pow`: the window ends below `2^k` are the real floors of
  `Primes/Window.lean`.
-/

@[expose] public section

namespace IntegerMultBounds.Primes

open IntegerMultBounds.MathlibTM2.Mult Finset

/-- The prime source lengths: the first `a` primes above `winLo d R`, then the first `d - a`
primes above `winLo d (2R)`. -/
def primeSrc (d a R i : ℕ) : ℕ :=
  if i < a then windowPrime (winLo d R) i else windowPrime (winLo d (2 * R)) (i - a)

theorem primeSrc_prime (d a R i : ℕ) : (primeSrc d a R i).Prime := by
  unfold primeSrc
  split_ifs <;> exact windowPrime_prime _ _

theorem three_le_primeSrc {d a R : ℕ} (hd : 1 ≤ d) (hR : 8 ≤ R) (i : ℕ) :
    3 ≤ primeSrc d a R i := by
  unfold primeSrc
  split_ifs
  · exact (three_le_winLo hd hR).trans (lo_lt_windowPrime _ _).le
  · exact (three_le_winLo hd (by omega : 8 ≤ 2 * R)).trans (lo_lt_windowPrime _ _).le

/-- **The prime moduli.** For `d ≥ 2`, `a ≤ d`, `e ≥ 3`, when the window below `2^e` holds at
least `a` primes and the window below `2^(e+1)` at least `d - a`, the prime source lengths and
the axis lengths are `Moduli.Good`. -/
theorem primeSrc_good {d a e : ℕ} (hd : 2 ≤ d) (ha : a ≤ d) (he : 3 ≤ e)
    (h₁ : a ≤ ((Ioc (winLo d (2 ^ e)) (winHi d (2 ^ e))).filter Nat.Prime).card)
    (h₂ : d - a ≤ ((Ioc (winLo d (2 * 2 ^ e)) (winHi d (2 * 2 ^ e))).filter Nat.Prime).card) :
    Moduli.Good (fun i : Fin d => primeSrc d a (2 ^ e) i) (Moduli.box d a e) := by
  have hd1 : 1 ≤ d := by omega
  have hR8 : 8 ≤ 2 ^ e := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hbox : ∀ i : Fin d, Moduli.box d a e i =
      if (i : ℕ) < a then 2 ^ e else 2 * 2 ^ e := by
    intro i
    simp only [Moduli.box, Moduli.axisLen]
    split_ifs <;> ring
  have hmem : ∀ i : Fin d, (primeSrc d a (2 ^ e) i).Prime ∧
      winLo d (Moduli.box d a e i) < primeSrc d a (2 ^ e) i ∧
      primeSrc d a (2 ^ e) i ≤ winHi d (Moduli.box d a e i) := by
    intro i
    rw [hbox i]
    unfold primeSrc
    split_ifs with hi
    · have h := Finset.mem_filter.mp (windowPrime_mem h₁ hi)
      exact ⟨h.2, (Finset.mem_Ioc.mp h.1).1, (Finset.mem_Ioc.mp h.1).2⟩
    · have h := Finset.mem_filter.mp (windowPrime_mem h₂ (by omega : (i : ℕ) - a < d - a))
      exact ⟨h.2, (Finset.mem_Ioc.mp h.1).1, (Finset.mem_Ioc.mp h.1).2⟩
  have hbox8 : ∀ i : Fin d, 8 ≤ Moduli.box d a e i := by
    intro i
    rw [hbox i]
    split_ifs <;> omega
  have hbd : ∀ i : Fin d, Moduli.AxisBounds d (primeSrc d a (2 ^ e) i) (Moduli.box d a e i) :=
    fun i => axisBounds_of_mem hd1 (hmem i).2.1 (hmem i).2.2
  have hpos : ∀ i : Fin d, 0 < Moduli.box d a e i := fun i => by have := hbox8 i; omega
  have hlt : ∀ i : Fin d, primeSrc d a (2 ^ e) i < Moduli.box d a e i :=
    fun i => (hmem i).2.2.trans_lt (winHi_lt hd1 (by have := hbox8 i; omega))
  have hodd : ∀ i : Fin d, Odd (primeSrc d a (2 ^ e) i) := by
    intro i
    have h3 := three_le_winLo hd1 (hbox8 i)
    exact (hmem i).1.odd_of_ne_two (by have := (hmem i).2.1; omega)
  refine ⟨hodd, hlt, ?_, ?_, hbd, ?_, Moduli.prod_gt_of_bounds hd1 hbd hpos⟩
  · intro i
    have ho := hodd i
    simp only [Moduli.box, Moduli.axisLen]
    split_ifs
    · exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho)
    · exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho)
  · intro i j hij
    have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    refine (Nat.coprime_primes (hmem i).1 (hmem j).1).mpr ?_
    have hsep := winHi_le_winLo_two_mul (d := d) (t := 2 ^ e) hd1
    have hmi := hmem i
    have hmj := hmem j
    rw [hbox i] at hmi
    rw [hbox j] at hmj
    unfold primeSrc at hmi hmj ⊢
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;>
      simp only [hi, hj, ↓reduceIte] at hmi hmj ⊢
    · exact (windowPrime_strictMono _).injective.ne hij'
    · omega
    · omega
    · exact (windowPrime_strictMono _).injective.ne (by omega)
  · have hne : (univ : Finset (Fin d)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
    exact prod_lt_prod_of_nonempty₀ (fun i _ => (hmem i).1.pos) (fun i _ => hlt i) hne

/-! ### The windows below `2^k` -/

/-- The window ends below `2^k` in real form. -/
theorem winLo_two_pow {D : ℕ} (hD : 1 ≤ D) (k : ℕ) :
    winLo D (2 ^ k) = ⌊(1 - 1 / (2 * (D : ℝ))) * 2 ^ k⌋₊ := by
  rw [winLo_eq_floor hD]
  push_cast
  rfl

theorem winHi_two_pow {D : ℕ} (hD : 1 ≤ D) (k : ℕ) :
    winHi D (2 ^ k) = ⌊(1 - 1 / (4 * (D : ℝ))) * 2 ^ k⌋₊ := by
  rw [winHi_eq_floor hD]
  push_cast
  rfl

theorem winLo_le_winHi {D : ℕ} (hD : 1 ≤ D) (T : ℕ) : winLo D T ≤ winHi D T := by
  obtain ⟨h2lo, -⟩ := ceil_spec (k := 2 * D) (by omega) T
  obtain ⟨-, h4hi⟩ := ceil_spec (k := 4 * D) (by omega) T
  unfold winLo winHi winFloor
  generalize (T + 2 * D - 1) / (2 * D) = q₂ at *
  generalize (T + 4 * D - 1) / (4 * D) = q₄ at *
  have h : 2 * D * (2 * q₄) < 2 * D * (q₂ + 2) := by nlinarith
  have := Nat.lt_of_mul_lt_mul_left h
  omega

end IntegerMultBounds.Primes
