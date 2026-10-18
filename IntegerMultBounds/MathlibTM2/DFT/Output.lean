module

public import IntegerMultBounds.MathlibTM2.DFT.Pipeline
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The values the pipeline prints

* `unpackVal_eq_fastDFT`: the value of unpacking round `k` is `fastDFT p ω n B a k`, for
  `B = 2 ^ (3 w)` and `a j = as.getD j 0` (`chirpProduct2_digit`, `revPack_chirpedInput`).
* `DFTInstance.n_lt_p`: `n < p`, since a primitive `n`-th root of unity has order dividing
  `p - 1`; `DFTInstance.digit_bound`: `n (p - 1) ^ 2 < 2 ^ (3 w)` for `w = Nat.size p`.
* `pipe_output`: the `n` values are `DFTInstance.transform` (`fastDFT_transform`).
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

theorem unpackVal_eq_fastDFT {p ω w : ℕ} (as : List ℕ) (hp : 0 < p)
    (hB : as.length * ((p - 1) * (p - 1)) < 2 ^ (3 * w)) (k : ℕ) (hk : k < as.length) :
    unpackVal p (ω ^ (as.length - 1) % p) w (pipeZ w p ω as) k =
      fastDFT p ω as.length (2 ^ (3 * w)) (fun j => as.getD j 0) k := by
  have hX : pipeX w p ω as =
      pack (2 ^ (3 * w)) (chirpedInput p ω as.length (fun j => as.getD j 0)) as.length :=
    revPack_chirpedInput p ω as.length _ _
  have hP : (0 + 2 ^ (3 * w) * pipeX w p ω as) * pipeY w p ω as =
      chirpProduct2 p ω as.length (2 ^ (3 * w)) (fun j => as.getD j 0) := by
    rw [hX, pipeY, chirpProduct2, Nat.zero_add, two_mul]
  have hdiv : pipeZ w p ω as / 2 ^ (3 * w * k) =
      chirpProduct2 p ω as.length (2 ^ (3 * w)) (fun j => as.getD j 0) /
        (2 ^ (3 * w)) ^ (as.length + k) := by
    rw [pipeZ, hP, Nat.div_div_eq_div_mul, ← pow_add, ← pow_mul, mul_add]
  rw [unpackVal, hdiv, chirpProduct2_digit p ω as.length _ _ hp hB k hk, fastDFT,
    Nat.mul_comm (chirpProduct p ω as.length (2 ^ (3 * w)) (fun j => as.getD j 0) /
      (2 ^ (3 * w)) ^ (as.length - 1 + k) % 2 ^ (3 * w) % p)]
  rfl

theorem range_map_eq_ofFn {n : ℕ} {f : ℕ → ℕ} {g : Fin n → ℕ} (h : ∀ k : Fin n, f k = g k) :
    (List.range n).map f = List.ofFn g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact h ⟨i, by simpa using h2⟩

theorem DFTInstance.n_lt_p (x : DFTInstance) : x.n < x.p := by
  haveI := x.prime
  have hp := x.prime.out
  rcases Nat.eq_zero_or_pos x.n with h | h
  · rw [h]; exact hp.pos
  · have hω : x.ω ≠ 0 := by
      intro h0
      have := x.primitive.pow_eq_one
      rw [h0, zero_pow (by omega)] at this
      exact zero_ne_one this
    have hdvd := x.primitive.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one hω)
    have := Nat.le_of_dvd (by have := hp.two_le; omega) hdvd
    omega

theorem DFTInstance.digit_bound (x : DFTInstance) :
    x.n * ((x.p - 1) * (x.p - 1)) < 2 ^ (3 * Nat.size x.p) := by
  have hn := x.n_lt_p
  have hpw : x.p < 2 ^ Nat.size x.p := Nat.lt_size_self _
  have h1 : x.p - 1 < 2 ^ Nat.size x.p := by omega
  calc x.n * ((x.p - 1) * (x.p - 1)) < 2 ^ Nat.size x.p * (2 ^ Nat.size x.p * 2 ^ Nat.size x.p) := by
        exact Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.mul_le_mul h1.le h1.le) (by positivity)
    _ = 2 ^ (3 * Nat.size x.p) := by rw [← pow_add, ← pow_add]; congr 1; ring

/-- The printed values are the transform. -/
theorem pipe_output (x : DFTInstance) :
    (List.range x.n).map (unpackVal x.p (x.ω.val ^ (x.n - 1) % x.p) (Nat.size x.p)
      (pipeZ (Nat.size x.p) x.p x.ω.val (List.ofFn fun i => (x.a i).val))) = x.transform := by
  have hp : 0 < x.p := x.prime.out.pos
  have hlen : (List.ofFn fun i => (x.a i).val).length = x.n := List.length_ofFn
  rw [← fastDFT_transform x (2 ^ (3 * Nat.size x.p)) x.digit_bound]
  apply range_map_eq_ofFn
  intro k
  have := unpackVal_eq_fastDFT (ω := x.ω.val) (w := Nat.size x.p)
    (List.ofFn fun i => (x.a i).val) hp (by rw [hlen]; exact x.digit_bound) k
    (by rw [hlen]; exact k.isLt)
  rw [hlen] at this
  exact this

end IntegerMultBounds.MathlibTM2.DFT
