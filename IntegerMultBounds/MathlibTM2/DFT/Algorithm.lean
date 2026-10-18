module

public import IntegerMultBounds.MathlibTM2.DFT.Statement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# The arithmetic of the fast transform

The machine computes the discrete Fourier transform over `ZMod p` from one integer product. This
file defines that computation on naturals (`fastDFT`) and proves that it returns the canonical
representatives of the transform (`fastDFT_transform`).

* `choose_two_add`: `j k + C(j, 2) + C(k, 2) = C(j + k, 2)`. With `ω⁻¹ = ω ^ (n - 1)` this gives
  `ω ^ (j k) = ω⁻¹ ^ C(k, 2) ω⁻¹ ^ C(j, 2) ω ^ C(j + k, 2)` (`chirp_identity`, Bluestein's
  identity in the form that needs no square root of `ω`), so the transform is a correlation of
  the chirped input `a j ω⁻¹ ^ C(j, 2)` with the chirp `ω ^ C(m, 2)`.
* `pack B u n = ∑ i < n, u i B ^ i` (Kronecker substitution). `pack_mul` multiplies two packed
  sequences into the packed convolution, and `pack_div_pow_mod` reads one coefficient back when
  every coefficient is below `B`. Every coefficient of the convolution of `n` residues with any
  number of residues is at most `n (p - 1) ^ 2` (`conv_le`).
* `packProduct_digit`: digit `n - 1 + k` of `pack B u n * pack B v (2 n - 1)` is
  `∑ j < n, u (n - 1 - j) v (j + k)` when all digits fit. `correlation_cast`: if `u` and `v`
  represent the reversed chirped input and the chirp up to factors `c₁`, `c₂` in `ZMod p`, this
  correlation times the inverse chirp is `c₁ c₂ (dft ω x k)`. The machine works with the
  residues themselves (Barrett reduction), so `c₁ = c₂ = 1`.
* `fastDFT p ω n B a k` reduces the input and the chirp mod `p`, packs both in base `B`,
  multiplies, reads coefficient `n - 1 + k`, reduces it mod `p` and multiplies by the inverse
  chirp. `fastDFT_cast` identifies it with the transform in `ZMod p` whenever `ω ^ n = 1` and
  `n (p - 1) ^ 2 < B`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.DFT

open Finset

/-! ### The chirp identity -/

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]
  omega

theorem choose_two_add (j k : ℕ) : j * k + j.choose 2 + k.choose 2 = (j + k).choose 2 := by
  induction k with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ k ih =>
    rw [← Nat.add_assoc, choose_two_succ, choose_two_succ, ← ih]
    ring

/-- Bluestein's identity: for `ω' ω = 1`,
`ω ^ (j k) = ω' ^ C(k, 2) ω' ^ C(j, 2) ω ^ C(j + k, 2)`. -/
theorem chirp_identity {R : Type*} [CommSemiring R] (ω ω' : R) (h : ω' * ω = 1) (j k : ℕ) :
    ω' ^ k.choose 2 * (ω' ^ j.choose 2 * ω ^ (j + k).choose 2) = ω ^ (j * k) := by
  rw [← choose_two_add, pow_add, pow_add]
  calc ω' ^ k.choose 2 * (ω' ^ j.choose 2 * (ω ^ (j * k) * ω ^ j.choose 2 * ω ^ k.choose 2))
      = ω ^ (j * k) * (ω' * ω) ^ j.choose 2 * (ω' * ω) ^ k.choose 2 := by ring
    _ = ω ^ (j * k) := by rw [h, one_pow, one_pow, mul_one, mul_one]

/-! ### Kronecker substitution -/

/-- The sequence `u 0, …, u (n - 1)` as the digits of one number in base `B`. -/
def pack (B : ℕ) (u : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, u i * B ^ i

/-- Coefficient `l` of the product of the polynomials with coefficients `u 0, …, u (n - 1)` and
`v 0, …, v (m - 1)`. -/
def conv (u : ℕ → ℕ) (n : ℕ) (v : ℕ → ℕ) (m l : ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range m, if i + j = l then u i * v j else 0

theorem pack_succ (B : ℕ) (u : ℕ → ℕ) (n : ℕ) : pack B u (n + 1) = pack B u n + u n * B ^ n :=
  Finset.sum_range_succ _ _

theorem pack_add (B : ℕ) (u : ℕ → ℕ) (n m : ℕ) :
    pack B u (n + m) = pack B u n + B ^ n * pack B (fun i => u (n + i)) m := by
  induction m with
  | zero => simp [pack]
  | succ m ih =>
    rw [← Nat.add_assoc, pack_succ, pack_succ, ih, pow_add]
    ring

theorem pack_one (B : ℕ) (u : ℕ → ℕ) : pack B u 1 = u 0 := by simp [pack]

/-- Packed sequences multiply to the packed convolution. -/
theorem pack_mul (B : ℕ) (u : ℕ → ℕ) (n : ℕ) (v : ℕ → ℕ) (m : ℕ) :
    pack B u n * pack B v m = pack B (conv u n v m) (n + m) := by
  have hterm : ∀ i ∈ range n, ∀ j ∈ range m,
      u i * B ^ i * (v j * B ^ j) =
        ∑ l ∈ range (n + m), (if i + j = l then u i * v j else 0) * B ^ l := by
    intro i hi j hj
    rw [Finset.mem_range] at hi hj
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range, pow_add]
    rw [ite_eq_left (show i + j < n + m by omega)]
    ring
  simp only [pack]
  rw [Finset.sum_mul_sum]
  simp only [conv, Finset.sum_mul]
  rw [Finset.sum_comm (s := range (n + m))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm (s := range (n + m))]
  exact Finset.sum_congr rfl fun j hj => hterm i hi j hj

/-- The digits below position `k` add up to less than `B ^ k`. -/
theorem pack_lt {B : ℕ} (u : ℕ → ℕ) (hu : ∀ i, u i < B) (k : ℕ) : pack B u k < B ^ k := by
  induction k with
  | zero => simp [pack]
  | succ k ih =>
    rw [pack_succ, pow_succ]
    calc pack B u k + u k * B ^ k < B ^ k + u k * B ^ k := Nat.add_lt_add_right ih _
      _ = (u k + 1) * B ^ k := by ring
      _ ≤ B * B ^ k := Nat.mul_le_mul_right _ (hu k)
      _ = B ^ k * B := by ring

theorem pack_succ_mod (B : ℕ) (u : ℕ → ℕ) (n : ℕ) : pack B u (n + 1) % B = u 0 % B := by
  rw [Nat.add_comm, pack_add, pack_one, pow_one, Nat.add_mul_mod_self_left]

/-- One digit read back from a packed sequence whose digits are below `B`. -/
theorem pack_div_pow_mod {B : ℕ} (u : ℕ → ℕ) (hu : ∀ i, u i < B) (n k : ℕ) :
    pack B u n / B ^ k % B = if k < n then u k else 0 := by
  have hB : 0 < B := (Nat.zero_le _).trans_lt (hu 0)
  split_ifs with hk
  · obtain ⟨r, rfl⟩ : ∃ r, n = k + (r + 1) := ⟨n - k - 1, by omega⟩
    rw [pack_add, Nat.add_mul_div_left _ _ (pow_pos hB k), Nat.div_eq_of_lt (pack_lt u hu k),
      zero_add, pack_succ_mod]
    exact Nat.mod_eq_of_lt (hu k)
  · have hlt : pack B u n < B ^ k :=
      (pack_lt u hu n).trans_le (Nat.pow_le_pow_right hB (by omega))
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]

/-- A coefficient of the convolution of `n` numbers at most `c` with numbers at most `c`. -/
theorem conv_le (u : ℕ → ℕ) (n : ℕ) (v : ℕ → ℕ) (m l c : ℕ) (hu : ∀ i, u i ≤ c)
    (hv : ∀ j, v j ≤ c) : conv u n v m l ≤ n * (c * c) := by
  calc conv u n v m l ≤ ∑ _i ∈ range n, c * c := by
        unfold conv
        refine Finset.sum_le_sum fun i _ => ?_
        calc ∑ j ∈ range m, (if i + j = l then u i * v j else 0)
            ≤ ∑ j ∈ range m, if l - i = j then c * c else 0 := by
              refine Finset.sum_le_sum fun j _ => ?_
              split_ifs <;> first | exact Nat.mul_le_mul (hu i) (hv j) | omega
          _ ≤ c * c := by
              rw [Finset.sum_ite_eq]
              split_ifs <;> omega
    _ = n * (c * c) := by simp

/-- Coefficient `n - 1 + k` of a convolution with `n + k ≤ m` is a correlation. -/
theorem conv_eq_sum (u : ℕ → ℕ) (n : ℕ) (v : ℕ → ℕ) (m k : ℕ) (hk : n + k ≤ m) :
    conv u n v m (n - 1 + k) = ∑ i ∈ range n, u i * v (n - 1 + k - i) := by
  unfold conv
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hcond : ∀ j ∈ range m, (if i + j = n - 1 + k then u i * v j else 0) =
      if n - 1 + k - i = j then u i * v j else 0 := fun j _ => by
    split_ifs <;> first | rfl | omega
  rw [Finset.sum_congr rfl hcond, Finset.sum_ite_eq,
    ite_eq_left (Finset.mem_range.mpr (show n - 1 + k - i < m by omega))]

/-- The correlation of `u` reversed with `v`. -/
theorem conv_reflect (u : ℕ → ℕ) (n : ℕ) (v : ℕ → ℕ) (m k : ℕ) (hk : n + k ≤ m) :
    conv u n v m (n - 1 + k) = ∑ j ∈ range n, u (n - 1 - j) * v (j + k) := by
  rw [conv_eq_sum u n v m k hk, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  show u (n - 1 - j) * v (n - 1 + k - (n - 1 - j)) = u (n - 1 - j) * v (j + k)
  rw [show n - 1 + k - (n - 1 - j) = j + k by omega]

/-! ### The transform from one product -/

/-- The chirp `ω ^ C(m, 2)`, reduced mod `p`. -/
def chirp (p ω m : ℕ) : ℕ := ω ^ m.choose 2 % p

/-- `ω ^ (n - 1)`, the inverse of an `n`-th root of unity `ω`, reduced mod `p`. -/
def inverseRoot (p ω n : ℕ) : ℕ := ω ^ (n - 1) % p

/-- The input times the inverse chirp, reduced mod `p`, in reverse order. -/
def chirpedInput (p ω n : ℕ) (a : ℕ → ℕ) (i : ℕ) : ℕ :=
  a (n - 1 - i) * chirp p (inverseRoot p ω n) (n - 1 - i) % p

/-- The one integer product: the packed reversed chirped input times the packed chirp. -/
def chirpProduct (p ω n B : ℕ) (a : ℕ → ℕ) : ℕ :=
  pack B (chirpedInput p ω n a) n * pack B (chirp p ω) (2 * n - 1)

/-- Entry `k` of the transform of `a 0, …, a (n - 1)` at `ω` mod `p`, from one product in
base `B`. -/
def fastDFT (p ω n B : ℕ) (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  chirp p (inverseRoot p ω n) k * (chirpProduct p ω n B a / B ^ (n - 1 + k) % B % p) % p

/-- Digit `n - 1 + k` of the product of the packs of `u` (length `n`) and `v` (length
`2 n - 1`) is the correlation of `u` reversed with `v` at `k`, when every digit fits. -/
theorem packProduct_digit (u v : ℕ → ℕ) (c n B : ℕ) (hu : ∀ i, u i ≤ c) (hv : ∀ j, v j ≤ c)
    (hB : n * (c * c) < B) (k : ℕ) (hk : k < n) :
    pack B u n * pack B v (2 * n - 1) / B ^ (n - 1 + k) % B =
      ∑ j ∈ range n, u (n - 1 - j) * v (j + k) := by
  have hdigit : ∀ l, conv u n v (2 * n - 1) l < B := fun l =>
    (conv_le u n v (2 * n - 1) l c hu hv).trans_lt hB
  rw [pack_mul, pack_div_pow_mod _ hdigit, ite_eq_left (show n - 1 + k < n + (2 * n - 1) by omega),
    conv_reflect _ n _ (2 * n - 1) k (by omega)]

/-- The correlation of representatives of the chirped input (reversed) and of the chirp, times
the inverse chirp, is the transform up to the factors `c₁`, `c₂` of the representatives. -/
theorem correlation_cast {p n : ℕ} (ω ω' : ZMod p) (hinv : ω' * ω = 1) (x : Fin n → ZMod p)
    (c₁ c₂ : ZMod p) (u v : ℕ → ℕ)
    (hu : ∀ j (h : j < n), (u (n - 1 - j) : ZMod p) = c₁ * (x ⟨j, h⟩ * ω' ^ j.choose 2))
    (hv : ∀ m, (v m : ZMod p) = c₂ * ω ^ m.choose 2) (k : Fin n) :
    ω' ^ (k : ℕ).choose 2 * ((∑ j ∈ range n, u (n - 1 - j) * v (j + k) : ℕ) : ZMod p) =
      c₁ * c₂ * dft ω x k := by
  rw [Nat.cast_sum, dft, Finset.sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, hu j j.isLt, hv, Fin.eta, ← chirp_identity ω ω' hinv]
  ring

/-- The digit `n - 1 + k` of the product is the correlation of the chirped input with the
chirp at `k`. -/
theorem chirpProduct_digit (p ω n B : ℕ) (a : ℕ → ℕ) (hp : 0 < p)
    (hB : n * ((p - 1) * (p - 1)) < B) (k : ℕ) (hk : k < n) :
    chirpProduct p ω n B a / B ^ (n - 1 + k) % B =
      ∑ j ∈ range n, chirpedInput p ω n a (n - 1 - j) * chirp p ω (j + k) :=
  packProduct_digit (chirpedInput p ω n a) (chirp p ω) (p - 1) n B
    (fun _ => Nat.le_sub_one_of_lt (Nat.mod_lt _ hp))
    (fun _ => Nat.le_sub_one_of_lt (Nat.mod_lt _ hp)) hB k hk

/-- `fastDFT` is the transform in `ZMod p` whenever `ω ^ n = 1` and `n (p - 1) ^ 2 < B`. -/
theorem fastDFT_cast {p n : ℕ} [NeZero p] (ω : ZMod p) (hω : ω ^ n = 1) (x : Fin n → ZMod p)
    (w : ℕ) (hw : (w : ZMod p) = ω) (a : ℕ → ℕ)
    (ha : ∀ j (h : j < n), (a j : ZMod p) = x ⟨j, h⟩) (B : ℕ)
    (hB : n * ((p - 1) * (p - 1)) < B) (k : Fin n) :
    (fastDFT p w n B a k : ZMod p) = dft ω x k := by
  have hp : 0 < p := Nat.pos_of_neZero p
  have hk := k.isLt
  have hinv : (inverseRoot p w n : ZMod p) * ω = 1 := by
    rw [inverseRoot, ZMod.natCast_mod, Nat.cast_pow, hw, ← pow_succ,
      Nat.sub_add_cancel (by omega : 1 ≤ n), hω]
  have hu : ∀ j (h : j < n), (chirpedInput p w n a (n - 1 - j) : ZMod p) =
      1 * (x ⟨j, h⟩ * (inverseRoot p w n : ZMod p) ^ j.choose 2) := fun j h => by
    rw [chirpedInput, show n - 1 - (n - 1 - j) = j by omega, ZMod.natCast_mod, Nat.cast_mul,
      chirp, ZMod.natCast_mod, Nat.cast_pow, ha j h, one_mul]
  have hv : ∀ m, (chirp p w m : ZMod p) = 1 * ω ^ m.choose 2 := fun m => by
    rw [chirp, ZMod.natCast_mod, Nat.cast_pow, hw, one_mul]
  have hchirp : (chirp p (inverseRoot p w n) k : ZMod p) =
      (inverseRoot p w n : ZMod p) ^ (k : ℕ).choose 2 := by
    rw [chirp, ZMod.natCast_mod, Nat.cast_pow]
  rw [fastDFT, chirpProduct_digit p w n B a hp hB k hk, ZMod.natCast_mod, Nat.cast_mul,
    ZMod.natCast_mod, hchirp, correlation_cast ω _ hinv x 1 1 _ _ hu hv k]
  ring

/-- `fastDFT` returns the canonical representatives of the transform. -/
theorem fastDFT_eq_val {p n : ℕ} [NeZero p] (ω : ZMod p) (hω : ω ^ n = 1) (x : Fin n → ZMod p)
    (w : ℕ) (hw : (w : ZMod p) = ω) (a : ℕ → ℕ)
    (ha : ∀ j (h : j < n), (a j : ZMod p) = x ⟨j, h⟩) (B : ℕ)
    (hB : n * ((p - 1) * (p - 1)) < B) (k : Fin n) :
    fastDFT p w n B a k = (dft ω x k).val := by
  have hlt : fastDFT p w n B a k < p := Nat.mod_lt _ (Nat.pos_of_neZero p)
  rw [← fastDFT_cast ω hω x w hw a ha B hB k, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- On an instance, with the entries read from the input list, `fastDFT` is the output. -/
theorem fastDFT_transform (x : DFTInstance) (B : ℕ)
    (hB : x.n * ((x.p - 1) * (x.p - 1)) < B) :
    (List.ofFn fun k : Fin x.n => fastDFT x.p x.ω.val x.n B
      (fun j => (List.ofFn fun i => (x.a i).val).getD j 0) k) = x.transform := by
  have : NeZero x.p := ⟨x.prime.out.ne_zero⟩
  unfold DFTInstance.transform
  congr 1
  funext k
  refine fastDFT_eq_val x.ω x.primitive.pow_eq_one x.a x.ω.val (ZMod.natCast_zmod_val _) _
    (fun j h => ?_) B hB k
  simp [List.getD_eq_getElem?_getD, h]

end IntegerMultBounds.MathlibTM2.DFT
