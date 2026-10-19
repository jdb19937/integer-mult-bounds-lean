module

public import IntegerMultBounds.Swap.LowerTriangular
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Heights through the elimination

The height of a rational is the larger of `|num|` and `den` (`ht`). Heights grow at most
multiplicatively under products (`ht_mul`), by a factor two more under sums (`ht_add`), and not
under negation or inversion. A matrix is `Bounded` by `h` when all its entries have height at most
`h`; a product of matrices over `N` indices then has height at most `(2 a b)^N` (`bounded_mul`).

`exists_bounded`: the elimination of `Swap.LowerTriangular` yields, for a square rational matrix
with entries of height at most `2^α`, a factorization whose four factors have entries of height at
most `2^(FE N n α)`, where `N` is the number of indices and `n` bounds the active rows plus
columns. The exponent satisfies `FE N n α ≤ (16 N⁵)^n (α + 1)` (`FE_le`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Height

open Matrix Finset
open IntegerMultBounds.Swap.Shear (LowerTriangular pivotMatrix)
open IntegerMultBounds.Swap.LowerTriangular

/-! ### Heights of rationals -/

/-- The height of a rational: the larger of `|num|` and `den`. -/
def ht (x : ℚ) : ℕ := max x.num.natAbs x.den

theorem num_le_ht (x : ℚ) : x.num.natAbs ≤ ht x := le_max_left _ _

theorem den_le_ht (x : ℚ) : x.den ≤ ht x := le_max_right _ _

theorem one_le_ht (x : ℚ) : 1 ≤ ht x := le_max_of_le_right x.den_pos

@[simp] theorem ht_zero : ht 0 = 1 := by simp [ht]

@[simp] theorem ht_one : ht 1 = 1 := by simp [ht]

@[simp] theorem ht_neg (x : ℚ) : ht (-x) = ht x := by
  simp [ht]

@[simp] theorem ht_inv (x : ℚ) : ht x⁻¹ = ht x := by
  by_cases hx : x = 0
  · simp [hx]
  · unfold ht
    rw [Rat.den_inv_of_ne_zero hx, Rat.num_inv, Int.natAbs_mul, Int.natAbs_natCast]
    have hs : x.num.sign.natAbs = 1 := by
      rw [Int.natAbs_sign_of_ne_zero (Rat.num_ne_zero.mpr hx)]
    rw [hs, one_mul, max_comm]

theorem ht_divInt (a b : ℤ) (hb : b ≠ 0) : ht (Rat.divInt a b) ≤ max a.natAbs b.natAbs := by
  unfold ht
  apply max_le_max
  · by_cases ha : a = 0
    · subst ha; simp
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd a hb))
  · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hb) (Int.ofNat_dvd_left.mp (Rat.den_dvd a b))

theorem ht_mul (x y : ℚ) : ht (x * y) ≤ ht x * ht y := by
  have hx : (x.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 x.den_pos
  have hy : (y.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 y.den_pos
  have e : x * y = Rat.divInt (x.num * y.num) (x.den * y.den) := by
    conv_lhs => rw [← Rat.num_divInt_den x, ← Rat.num_divInt_den y]
    exact Rat.divInt_mul_divInt _ _
  rw [e]
  refine (ht_divInt _ _ (mul_ne_zero hx hy)).trans (max_le ?_ ?_)
  · rw [Int.natAbs_mul]; exact Nat.mul_le_mul (num_le_ht x) (num_le_ht y)
  · rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.mul_le_mul (den_le_ht x) (den_le_ht y)

theorem ht_add (x y : ℚ) : ht (x + y) ≤ 2 * ht x * ht y := by
  have hx : (x.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 x.den_pos
  have hy : (y.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 y.den_pos
  rw [Rat.add_num_den]
  refine (ht_divInt _ _ (mul_ne_zero hx hy)).trans (max_le ?_ ?_)
  · refine (Int.natAbs_add_le _ _).trans ?_
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    have h1 := Nat.mul_le_mul (num_le_ht x) (den_le_ht y)
    have h2 := Nat.mul_le_mul (den_le_ht x) (num_le_ht y)
    linarith
  · rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    have h1 := Nat.mul_le_mul (den_le_ht x) (den_le_ht y)
    have := one_le_ht x
    nlinarith [Nat.zero_le (ht x * ht y)]

theorem ht_sub (x y : ℚ) : ht (x - y) ≤ 2 * ht x * ht y := by
  rw [sub_eq_add_neg]
  exact (ht_add x (-y)).trans (by rw [ht_neg])

theorem ht_div (x y : ℚ) : ht (x / y) ≤ ht x * ht y := by
  rw [div_eq_mul_inv]
  exact (ht_mul x y⁻¹).trans (by rw [ht_inv])

theorem ht_sum {α : Type*} (s : Finset α) (f : α → ℚ) (c : ℕ) (hc : ∀ i ∈ s, ht (f i) ≤ c) :
    ht (∑ i ∈ s, f i) ≤ (2 * c) ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, card_insert_of_notMem ha, pow_succ]
    have h1 := hc a (mem_insert_self a s)
    have h2 := ih fun i hi => hc i (mem_insert_of_mem hi)
    refine (ht_add _ _).trans ?_
    calc 2 * ht (f a) * ht (∑ i ∈ s, f i) ≤ 2 * c * (2 * c) ^ s.card :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
      _ = (2 * c) ^ s.card * (2 * c) := by ring

/-! ### Bounded matrices -/

section Bounded

variable {ι κ ν : Type*}

/-- Every entry has height at most `h`. -/
def Bounded (A : Matrix ι κ ℚ) (h : ℕ) : Prop := ∀ i j, ht (A i j) ≤ h

theorem Bounded.mono {A : Matrix ι κ ℚ} {h h' : ℕ} (hA : Bounded A h) (hh : h ≤ h') :
    Bounded A h' := fun i j => (hA i j).trans hh

theorem Bounded.pow_mono {A : Matrix ι κ ℚ} {a a' : ℕ} (hA : Bounded A (2 ^ a)) (ha : a ≤ a') :
    Bounded A (2 ^ a') := hA.mono (Nat.pow_le_pow_right (by norm_num) ha)

theorem bounded_neg {A : Matrix ι κ ℚ} {h : ℕ} (hA : Bounded A h) : Bounded (-A) h :=
  fun i j => by rw [neg_apply, ht_neg]; exact hA i j

theorem bounded_add {A B : Matrix ι κ ℚ} {a b : ℕ} (hA : Bounded A (2 ^ a)) (hB : Bounded B (2 ^ b)) :
    Bounded (A + B) (2 ^ (a + b + 1)) := fun i j => by
  rw [add_apply]
  refine (ht_add _ _).trans ?_
  calc 2 * ht (A i j) * ht (B i j) ≤ 2 * 2 ^ a * 2 ^ b :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hA i j)) (hB i j)
    _ = 2 ^ (a + b + 1) := by ring

theorem bounded_sub {A B : Matrix ι κ ℚ} {a b : ℕ} (hA : Bounded A (2 ^ a)) (hB : Bounded B (2 ^ b)) :
    Bounded (A - B) (2 ^ (a + b + 1)) := by
  rw [sub_eq_add_neg]; exact bounded_add hA (bounded_neg hB)

theorem bounded_mul [Fintype κ] {A : Matrix ι κ ℚ} {B : Matrix κ ν ℚ} {a b : ℕ}
    (hA : Bounded A (2 ^ a)) (hB : Bounded B (2 ^ b)) :
    Bounded (A * B) (2 ^ (Fintype.card κ * (a + b + 1))) := fun i j => by
  rw [mul_apply]
  refine (ht_sum _ _ (2 ^ (a + b)) fun k _ => ?_).trans ?_
  · refine (ht_mul _ _).trans ?_
    rw [pow_add]
    exact Nat.mul_le_mul (hA i k) (hB k j)
  · rw [card_univ, ← pow_succ', ← pow_mul, mul_comm]

theorem bounded_transpose {A : Matrix ι κ ℚ} {h : ℕ} (hA : Bounded A h) : Bounded Aᵀ h :=
  fun i j => hA j i

theorem bounded_one [DecidableEq ι] : Bounded (1 : Matrix ι ι ℚ) (2 ^ 0) := fun i j => by
  by_cases h : i = j
  · subst h; simp
  · rw [one_apply_ne h]; simp

theorem bounded_single [DecidableEq ι] [DecidableEq κ] (r : ι) (c : κ) :
    Bounded (single r c (1 : ℚ)) (2 ^ 0) := fun i j => by
  simp only [single, of_apply]
  split_ifs <;> simp

end Bounded

/-! ### The elimination step -/

section Step

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The exponent of `1 ± rowOps` and `afterCols`. -/
def acE (N α : ℕ) : ℕ := N * (α + (2 * α + 1) + 1)
def rowE (N α : ℕ) : ℕ := acE N α + α + 1
def arE (N α : ℕ) : ℕ := N * (rowE N α + acE N α + 1)
def normE (N α : ℕ) : ℕ := N * (α + arE N α + 1)
/-- The exponent of the residual. -/
def resE (N α : ℕ) : ℕ := normE N α + 0 + 1
/-- The exponent of the factors after one step, from the residual's factor exponent `e`. -/
def stepE (N α e : ℕ) : ℕ :=
  max (max (N * (N * (rowE N α + α + 1) + e + 1)) (N * (N * (e + α + 1) + rowE N α + 1)))
    (max (N * (e + (2 * α + 1) + 1)) (N * ((2 * α + 1) + e + 1)))

/-- The factor exponent after `n` steps. -/
def FE (N : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, α => stepE N α (FE N n (resE N α))

variable (S T : Finset ι) (A : Matrix ι ι ℚ) (r c : ι) {α : ℕ}

local notation "N" => Fintype.card ι

omit [Fintype ι] in
lemma bounded_scaleRow {a : ℚ} (ha : ht a ≤ 2 ^ α) : Bounded (scaleRow r a) (2 ^ α) := by
  intro i j
  simp only [scaleRow, diagonal_apply]
  have h1 : 1 ≤ 2 ^ α := Nat.one_le_two_pow
  split_ifs <;> simp_all

omit [Fintype ι] in
lemma bounded_colOps (hA : Bounded A (2 ^ α)) : Bounded (colOps T A r c) (2 ^ (2 * α)) := by
  intro i j
  simp only [colOps, of_apply]
  split_ifs
  · rw [ht_neg, two_mul, pow_add]
    exact (ht_div _ _).trans (Nat.mul_le_mul (hA r j) (hA r c))
  · simp [Nat.one_le_two_pow]

lemma bounded_afterCols (hA : Bounded A (2 ^ α)) : Bounded (afterCols T A r c) (2 ^ acE N α) := by
  have h1 : Bounded (1 + colOps T A r c) (2 ^ (2 * α + 1)) :=
    (bounded_add bounded_one (bounded_colOps T A r c hA)).pow_mono (by omega)
  exact bounded_mul hA h1

lemma bounded_rowOps (hA : Bounded A (2 ^ α)) :
    Bounded (rowOps S T A r c) (2 ^ (acE N α + α)) := by
  intro i j
  simp only [rowOps, of_apply]
  split_ifs
  · rw [ht_neg, pow_add]
    exact (ht_div _ _).trans (Nat.mul_le_mul (bounded_afterCols T A r c hA i c) (hA r c))
  · simp [Nat.one_le_two_pow]

lemma bounded_one_add_rowOps (hA : Bounded A (2 ^ α)) :
    Bounded (1 + rowOps S T A r c) (2 ^ rowE N α) :=
  (bounded_add bounded_one (bounded_rowOps S T A r c hA)).pow_mono (by unfold rowE; omega)

lemma bounded_one_sub_rowOps (hA : Bounded A (2 ^ α)) :
    Bounded (1 - rowOps S T A r c) (2 ^ rowE N α) :=
  (bounded_sub bounded_one (bounded_rowOps S T A r c hA)).pow_mono (by unfold rowE; omega)

lemma bounded_afterRows (hA : Bounded A (2 ^ α)) : Bounded (afterRows S T A r c) (2 ^ arE N α) :=
  bounded_mul (bounded_one_add_rowOps S T A r c hA) (bounded_afterCols T A r c hA)

lemma bounded_normalized (hA : Bounded A (2 ^ α)) :
    Bounded (normalized S T A r c) (2 ^ normE N α) :=
  bounded_mul (bounded_scaleRow r (by rw [ht_inv]; exact hA r c)) (bounded_afterRows S T A r c hA)

lemma bounded_residual (hA : Bounded A (2 ^ α)) :
    Bounded (residual S T A r c) (2 ^ resE N α) := by
  have h := bounded_sub (bounded_normalized S T A r c hA) (bounded_single (ι := ι) (κ := ι) r c)
  exact h

/-- The four factors of one step, from bounds on the residual's factors. -/
lemma bounded_step (hA : Bounded A (2 ^ α)) (hp : IsPivot S T A r c) {e : ℕ}
    (f : Factorization (S.erase r) (T.erase c) (residual S T A r c))
    (h₁ : Bounded f.E₁ (2 ^ e)) (h₁' : Bounded f.E₁' (2 ^ e)) (h₂ : Bounded f.E₂ (2 ^ e))
    (h₂' : Bounded f.E₂' (2 ^ e)) :
    Bounded (step S T A r c hp f).E₁ (2 ^ stepE N α e) ∧
      Bounded (step S T A r c hp f).E₁' (2 ^ stepE N α e) ∧
      Bounded (step S T A r c hp f).E₂ (2 ^ stepE N α e) ∧
      Bounded (step S T A r c hp f).E₂' (2 ^ stepE N α e) := by
  have hc : Bounded (colOps T A r c) (2 ^ (2 * α)) := bounded_colOps T A r c hA
  have hsub : Bounded (1 - colOps T A r c) (2 ^ (2 * α + 1)) :=
    (bounded_sub bounded_one hc).pow_mono (by omega)
  have hadd : Bounded (1 + colOps T A r c) (2 ^ (2 * α + 1)) :=
    (bounded_add bounded_one hc).pow_mono (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (bounded_mul (bounded_mul (bounded_one_sub_rowOps S T A r c hA)
      (bounded_scaleRow r (hA r c))) h₁).pow_mono (le_max_of_le_left (le_max_left _ _))
  · exact (bounded_mul (bounded_mul h₁' (bounded_scaleRow r (by rw [ht_inv]; exact hA r c)))
      (bounded_one_add_rowOps S T A r c hA)).pow_mono (le_max_of_le_left (le_max_right _ _))
  · exact (bounded_mul h₂ hsub).pow_mono (le_max_of_le_right (le_max_left _ _))
  · exact (bounded_mul hadd h₂').pow_mono (le_max_of_le_right (le_max_right _ _))

end Step

/-! ### The bounded elimination -/

section Elimination

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

local notation "N" => Fintype.card ι

/-- All four factors are bounded by `h`. -/
def FactorsBounded {S T : Finset ι} {A : Matrix ι ι ℚ} (f : Factorization S T A) (h : ℕ) : Prop :=
  Bounded f.E₁ h ∧ Bounded f.E₁' h ∧ Bounded f.E₂ h ∧ Bounded f.E₂' h

/-- **Bounded elimination.** A matrix supported on `S × T` with entries of height at most `2^α`
has a factorization on `S × T` whose factors have entries of height at most `2^(FE N n α)`, for
any `n ≥ |S| + |T|`. -/
theorem exists_bounded : ∀ (n : ℕ) (S T : Finset ι) (A : Matrix ι ι ℚ) (α : ℕ),
    S.card + T.card ≤ n → SupportedIn S T A → Bounded A (2 ^ α) →
      ∃ f : Factorization S T A, FactorsBounded f (2 ^ FE N n α) := by
  intro n
  induction n with
  | zero =>
    intro S T A α hn hA _
    have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    have h0 : A = 0 := by
      ext i j
      exact hA i j (Or.inl (by simp [hS]))
    exact ⟨trivialFactorization S T A h0, bounded_one, bounded_one, bounded_one, bounded_one⟩
  | succ n ih =>
  intro S T A α hn hA hB
  classical
  have h1 : 1 ≤ 2 ^ FE N (n + 1) α := Nat.one_le_two_pow
  by_cases h0 : A = 0
  · exact ⟨trivialFactorization S T A h0, bounded_one.mono h1, bounded_one.mono h1,
      bounded_one.mono h1, bounded_one.mono h1⟩
  have hex : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Matrix.ext fun i j => by rw [h i j, zero_apply])
  set R := univ.filter (fun i => ∃ j, A i j ≠ 0) with hRdef
  have hR : R.Nonempty := by
    obtain ⟨i, j, h⟩ := hex
    exact ⟨i, by simp only [hRdef, mem_filter, mem_univ, true_and]; exact ⟨j, h⟩⟩
  set r := R.min' hR with hrdef
  have hrR : r ∈ R := R.min'_mem hR
  obtain ⟨j₀, hj₀⟩ : ∃ j, A r j ≠ 0 := by
    simpa only [hRdef, mem_filter, mem_univ, true_and] using hrR
  set C := univ.filter (fun j => A r j ≠ 0) with hCdef
  have hC : C.Nonempty := ⟨j₀, by simp only [hCdef, mem_filter, mem_univ, true_and]; exact hj₀⟩
  set c := C.max' hC with hcdef
  have hc : A r c ≠ 0 := by
    have := C.max'_mem hC
    simpa only [hCdef, mem_filter, mem_univ, true_and] using this
  have hp : IsPivot S T A r c :=
    { supp := hA
      mem_r := by
        by_contra h
        exact hc (hA r c (Or.inl h))
      mem_c := by
        by_contra h
        exact hc (hA r c (Or.inr h))
      rows := by
        intro i hi j
        by_contra h
        have hiR : i ∈ R := by
          simp only [hRdef, mem_filter, mem_univ, true_and]
          exact ⟨j, h⟩
        exact absurd (R.min'_le i hiR) (not_le.mpr hi)
      cols := by
        intro j hj
        by_contra h
        have hjC : j ∈ C := by
          simp only [hCdef, mem_filter, mem_univ, true_and]
          exact h
        exact absurd (C.le_max' j hjC) (not_le.mpr hj)
      ne := hc }
  have hcard : (S.erase r).card + (T.erase c).card ≤ n := by
    rw [card_erase_of_mem hp.mem_r, card_erase_of_mem hp.mem_c]
    have h1 := card_pos.mpr ⟨r, hp.mem_r⟩
    have h2 := card_pos.mpr ⟨c, hp.mem_c⟩
    omega
  obtain ⟨f, hf₁, hf₁', hf₂, hf₂'⟩ := ih (S.erase r) (T.erase c) (residual S T A r c) (resE N α)
    hcard (residual_supp S T A r c hp) (bounded_residual S T A r c hB)
  exact ⟨step S T A r c hp f, bounded_step S T A r c hB hp f hf₁ hf₁' hf₂ hf₂'⟩

/-- The full factorization of a square matrix with entries of height at most `2^α`. -/
theorem exists_bounded_univ (A : Matrix ι ι ℚ) (α : ℕ) (hB : Bounded A (2 ^ α)) :
    ∃ f : Factorization univ univ A, FactorsBounded f (2 ^ FE N (2 * N) α) :=
  exists_bounded _ univ univ A α (by rw [card_univ]; omega)
    (fun _ _ h => by rcases h with h | h <;> exact absurd (mem_univ _) h) hB

end Elimination

/-! ### The closed bound -/

theorem stepE_le (N α e : ℕ) (hN : 1 ≤ N) : stepE N α e ≤ N ^ 2 * e + 5 * N ^ 3 * (α + 1) := by
  have hN2 : N ≤ N ^ 2 := by nlinarith
  have hN3 : N ^ 2 ≤ N ^ 3 := by nlinarith
  unfold stepE rowE acE
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> nlinarith [Nat.zero_le α, Nat.zero_le e,
    Nat.zero_le (N * e), Nat.zero_le (N * α), Nat.zero_le (N ^ 2 * α)]

theorem resE_le (N α : ℕ) (hN : 1 ≤ N) : resE N α ≤ 8 * N ^ 3 * (α + 1) := by
  have hN2 : N ≤ N ^ 2 := by nlinarith
  have hN3 : N ^ 2 ≤ N ^ 3 := by nlinarith
  unfold resE normE arE rowE acE
  nlinarith [Nat.zero_le α, Nat.zero_le (N * α), Nat.zero_le (N ^ 2 * α)]

/-- The closed bound on the factor exponent. -/
theorem FE_le (N : ℕ) (hN : 1 ≤ N) : ∀ n α, FE N n α ≤ (16 * N ^ 5) ^ n * (α + 1) := by
  intro n
  induction n with
  | zero => intro α; simp [FE]
  | succ n ih =>
    intro α
    have hD : 1 ≤ (16 * N ^ 5) ^ n := Nat.one_le_pow _ _ (by positivity)
    have h1 := stepE_le N α (FE N n (resE N α)) hN
    have h2 := ih (resE N α)
    have h3 := resE_le N α hN
    have hN3 : 1 ≤ N ^ 3 * (α + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc FE N (n + 1) α ≤ N ^ 2 * FE N n (resE N α) + 5 * N ^ 3 * (α + 1) := h1
      _ ≤ N ^ 2 * ((16 * N ^ 5) ^ n * (8 * N ^ 3 * (α + 1) + 1)) + 5 * N ^ 3 * (α + 1) := by
          gcongr
          exact h2.trans (Nat.mul_le_mul_left _ (by omega))
      _ ≤ (16 * N ^ 5) ^ (n + 1) * (α + 1) := by
          set X := (16 * N ^ 5) ^ n
          set Y := N ^ 3 * (α + 1)
          have hNX : 1 ≤ N ^ 2 * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
          have e1 : N ^ 2 * X ≤ N ^ 2 * X * Y := Nat.le_mul_of_pos_right _ hN3
          have e2 : Y ≤ N ^ 2 * X * Y := Nat.le_mul_of_pos_left Y hNX
          calc N ^ 2 * (X * (8 * N ^ 3 * (α + 1) + 1)) + 5 * N ^ 3 * (α + 1)
              = 8 * (N ^ 2 * X * Y) + N ^ 2 * X + 5 * Y := by ring
            _ ≤ 16 * (N ^ 2 * X * Y) := by omega
            _ = (16 * N ^ 5) ^ (n + 1) * (α + 1) := by rw [pow_succ]; ring

end IntegerMultBounds.MathlibTM2.M8.Height
