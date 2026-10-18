module

public import IntegerMultBounds.MathlibTM2.DFT.Algorithm
public import IntegerMultBounds.MathlibTM2.DFT.IO
public import IntegerMultBounds.MathlibTM2.Host.BinArithBits
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The arithmetic of the pipeline registers

* `chirp_succ`, `powMod_succ`: the recurrences `c (m+1) = c m · (ω ^ m mod p) mod p` and
  `ω ^ (m+1) mod p = (ω ^ m mod p) (ω mod p) mod p` of the chirp loops.
* `binSyms_pack_succ`: a packed sequence in `s`-bit digits gains its next digit on the high end;
  the chirp register, built most significant bit first, is the reverse of the packed chirp.
* `revPack B x i = x (i - 1) + B (x (i - 2) + …)`: the packed sequence built by pushing
  `x 0, x 1, …` on top (`binSyms_cons_block`); `revPack_eq_pack` turns it into `pack` of the
  reversed sequence, which for the chirped input is `pack B (chirpedInput p ω n a) n`.
* `packProduct_digit'`: `packProduct_digit` for `m ≥ n + k` digits of the second factor, and
  `shiftProduct_digit`: digit `n + k` of `B` times the product is digit `n - 1 + k` of the
  product.
* `natSyms_concat`: the output register after one more `emitNat`.
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

open Finset

variable {A : ℕ}

/-! ### The chirp recurrences -/

theorem chirp_succ (p ω m : ℕ) : chirp p ω (m + 1) = chirp p ω m * (ω ^ m % p) % p := by
  rw [chirp, chirp, choose_two_succ, pow_add, Nat.mul_mod]

theorem powMod_succ (p ω m : ℕ) : ω ^ (m + 1) % p = ω ^ m % p * (ω % p) % p := by
  rw [pow_succ, Nat.mul_mod]

theorem chirp_zero (p ω : ℕ) : chirp p ω 0 = 1 % p := by simp [chirp]

/-! ### Packed registers -/

/-- The next digit of a packed sequence, on the high end. -/
theorem binSyms_pack_succ {s : ℕ} (c : ℕ → ℕ) (hc : ∀ i, c i < 2 ^ s) (M : ℕ) :
    (binSyms (s * (M + 1)) (pack (2 ^ s) c (M + 1)) : List (Fin (A + 4))) =
      binSyms (s * M) (pack (2 ^ s) c M) ++ binSyms s (c M) := by
  have hB : ((2 : ℕ) ^ s) ^ M = 2 ^ (s * M) := by rw [← pow_mul]
  have hlt : pack (2 ^ s) c M < 2 ^ (s * M) := hB ▸ pack_lt c hc M
  rw [show s * (M + 1) = s * M + s by ring, binSyms_append, pack_succ, hB,
    ← binSyms_mod (s * M) (pack (2 ^ s) c M + c M * 2 ^ (s * M)), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hlt, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- Pushing a digit `binSyms s (c M)` most significant bit first onto the reversed register. -/
theorem binSyms_pack_succ_reverse {s : ℕ} (c : ℕ → ℕ) (hc : ∀ i, c i < 2 ^ s) (M : ℕ) :
    ((binSyms s (c M)).reverse ++ (binSyms (s * M) (pack (2 ^ s) c M)).reverse :
      List (Fin (A + 4))) = (binSyms (s * (M + 1)) (pack (2 ^ s) c (M + 1))).reverse := by
  rw [binSyms_pack_succ c hc, List.reverse_append]

/-- The packed sequence built by pushing `x 0, x 1, …` on top. -/
def revPack (B : ℕ) (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => x i + B * revPack B x i

theorem revPack_lt {B : ℕ} (x : ℕ → ℕ) (hx : ∀ i, x i < B) (i : ℕ) : revPack B x i < B ^ i := by
  induction i with
  | zero => simp [revPack]
  | succ i ih =>
    have := hx i
    calc x i + B * revPack B x i < B + B * revPack B x i := by omega
      _ = B * (revPack B x i + 1) := by ring
      _ ≤ B * B ^ i := Nat.mul_le_mul_left _ ih
      _ = B ^ (i + 1) := by ring

theorem revPack_eq_pack (B : ℕ) (x : ℕ → ℕ) (n : ℕ) :
    revPack B x n = pack B (fun t => x (n - 1 - t)) n := by
  induction n with
  | zero => simp [revPack, pack]
  | succ n ih =>
    rw [revPack, ih]
    unfold pack
    rw [Finset.sum_range_succ', Finset.mul_sum, Nat.add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [show n + 1 - 1 - (t + 1) = n - 1 - t by omega, pow_succ]
      ring
    · simp

/-- One digit pushed on top of a packed register. -/
theorem binSyms_cons_block {s a X i : ℕ} (ha : a < 2 ^ s) :
    (binSyms s a ++ binSyms (s * i) X : List (Fin (A + 4))) =
      binSyms (s * (i + 1)) (a + 2 ^ s * X) := by
  rw [show s * (i + 1) = s + s * i by ring, binSyms_append, ← binSyms_mod s (a + 2 ^ s * X),
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt ha, Nat.zero_add]

theorem binSyms_revPack_succ {s i : ℕ} (x : ℕ → ℕ) (hx : x i < 2 ^ s) :
    (binSyms s (x i) ++ binSyms (s * i) (revPack (2 ^ s) x i) : List (Fin (A + 4))) =
      binSyms (s * (i + 1)) (revPack (2 ^ s) x (i + 1)) := by
  rw [binSyms_cons_block hx]
  rfl

/-- The chirped input as pushed by the input loop. -/
theorem revPack_chirpedInput (p ω n B : ℕ) (a : ℕ → ℕ) :
    revPack B (fun j => a j * chirp p (inverseRoot p ω n) j % p) n =
      pack B (chirpedInput p ω n a) n := by
  rw [revPack_eq_pack]
  rfl

/-! ### The digits of the product -/

/-- `packProduct_digit` for any number `m ≥ n + k` of digits in the second factor. -/
theorem packProduct_digit' (u v : ℕ → ℕ) (c n m B : ℕ) (hu : ∀ i, u i ≤ c) (hv : ∀ j, v j ≤ c)
    (hB : n * (c * c) < B) (k : ℕ) (hk : k < n) (hm : n + k ≤ m) :
    pack B u n * pack B v m / B ^ (n - 1 + k) % B =
      ∑ j ∈ range n, u (n - 1 - j) * v (j + k) := by
  have hdigit : ∀ l, conv u n v m l < B := fun l =>
    (conv_le u n v m l c hu hv).trans_lt hB
  rw [pack_mul, pack_div_pow_mod _ hdigit, ite_eq_left (show n - 1 + k < n + m by omega),
    conv_reflect _ n _ m k hm]

/-- Digit `n + k` of `B X` is digit `n - 1 + k` of `X`. -/
theorem shift_digit {B : ℕ} (hB : 0 < B) (X n k : ℕ) (hn : 1 ≤ n) :
    B * X / B ^ (n + k) = X / B ^ (n - 1 + k) := by
  rw [show n + k = n - 1 + k + 1 by omega, pow_succ', Nat.mul_div_mul_left _ _ hB]

/-- The machine's product: `B` times the packed reversed chirped input times `2 n` chirp
digits. -/
def chirpProduct2 (p ω n B : ℕ) (a : ℕ → ℕ) : ℕ :=
  B * pack B (chirpedInput p ω n a) n * pack B (chirp p ω) (2 * n)

/-- Digit `n + k` of `chirpProduct2` is digit `n - 1 + k` of `chirpProduct`. -/
theorem chirpProduct2_digit (p ω n B : ℕ) (a : ℕ → ℕ) (hp : 0 < p)
    (hB : n * ((p - 1) * (p - 1)) < B) (k : ℕ) (hk : k < n) :
    chirpProduct2 p ω n B a / B ^ (n + k) % B = chirpProduct p ω n B a / B ^ (n - 1 + k) % B := by
  have hB0 : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hB
  have hu : ∀ i, chirpedInput p ω n a i ≤ p - 1 := fun _ =>
    Nat.le_sub_one_of_lt (Nat.mod_lt _ hp)
  have hv : ∀ j, chirp p ω j ≤ p - 1 := fun _ => Nat.le_sub_one_of_lt (Nat.mod_lt _ hp)
  rw [chirpProduct2, Nat.mul_assoc, shift_digit hB0 _ n k (by omega),
    packProduct_digit' _ _ (p - 1) n (2 * n) B hu hv hB k hk (by omega),
    chirpProduct_digit p ω n B a hp hB k hk]

/-! ### The output register -/

theorem natSyms_concat (l : List ℕ) (x : ℕ) :
    ((natSyms (l ++ [x])).reverse : List (Fin (A + 4))) =
      separator :: ((binSyms (Nat.size x) x).reverse ++ (natSyms l).reverse) := by
  simp [natSyms, List.flatMap_append, List.reverse_append]

end IntegerMultBounds.MathlibTM2.DFT
