module
import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Basic
public import IntegerMultBounds.Machine


/-!
# Signed-carry addition, least significant bit first

`carryRun c ss` adds a carry `c` to the column sums `ss` (column `t` has weight `2^t`), emitting
one bit per column. `carryRun_val`: the emitted bits and the final carry satisfy
`value bits + 2^len · carry = c + Σₜ sₜ 2^t` exactly. Hence an integer linear combination of
words, fed column by column, comes out exactly modulo `2^len` (`carryRun_lin`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

/-- Value of a bit list, least significant bit first. -/
def valBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * valBits bs

/-- Column sums with weights `2^t`. -/
def colVal : List ℤ → ℤ
  | [] => 0
  | s :: ss => s + 2 * colVal ss

/-- Emit one bit per column with a signed carry. -/
def carryRun (c : ℤ) : List ℤ → List Bool × ℤ
  | [] => ([], c)
  | s :: ss =>
      let b := (c + s) % 2 = 1
      let r := carryRun ((c + s - (if b then 1 else 0)) / 2) ss
      (b :: r.1, r.2)

lemma carryRun_length (c : ℤ) (ss : List ℤ) : (carryRun c ss).1.length = ss.length := by
  induction ss generalizing c with
  | nil => rfl
  | cons s ss ih => simp [carryRun, ih]

/-- The carry adder is exact. -/
theorem carryRun_val (c : ℤ) (ss : List ℤ) :
    (valBits (carryRun c ss).1 : ℤ) + 2 ^ ss.length * (carryRun c ss).2 = c + colVal ss := by
  induction ss generalizing c with
  | nil => simp [carryRun, valBits, colVal]
  | cons s ss ih =>
      simp only [carryRun, valBits, colVal, List.length_cons]
      have h := ih ((c + s - (if (c + s) % 2 = 1 then 1 else 0)) / 2)
      have hmod : (c + s) % 2 = 0 ∨ (c + s) % 2 = 1 := Int.emod_two_eq_zero_or_one _
      rcases hmod with h0 | h1
      · have hdiv : (c + s - 0) / 2 * 2 = c + s := by omega
        simp only [h0, zero_ne_one, ite_false, decide_false, Bool.toNat_false] at h ⊢
        push_cast
        rw [pow_succ]
        nlinarith [h, hdiv]
      · have hdiv : (c + s - 1) / 2 * 2 = c + s - 1 := by omega
        simp only [h1, ite_true, decide_true, Bool.toNat_true] at h ⊢
        push_cast
        rw [pow_succ]
        nlinarith [h, hdiv]

/-- Column values of a word's bits. -/
lemma colVal_bits (bs : List Bool) : colVal (bs.map fun b => (b.toNat : ℤ)) = valBits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [colVal, valBits, ih]

lemma colVal_ofFn {n : ℕ} (f : Fin n → ℤ) : colVal (List.ofFn f) = ∑ t, f t * 2 ^ (t : ℕ) := by
  induction n with
  | zero => simp [colVal]
  | succ n ih =>
      rw [List.ofFn_succ, colVal, ih, Fin.sum_univ_succ, Finset.mul_sum]
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro t _
        simp only [Fin.val_succ, pow_succ]
        ring

lemma valBits_sum (n : ℕ) (x : List Bool) (hx : x.length = n) :
    (valBits x : ℤ) = ∑ t : Fin n, ((x.getD t false).toNat : ℤ) * 2 ^ (t : ℕ) := by
  subst hx
  induction x with
  | nil => simp [valBits]
  | cons b bs ih =>
      rw [List.length_cons, Fin.sum_univ_succ]
      simp only [valBits, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, List.getD_cons_zero,
        Fin.val_zero, pow_zero, mul_one, Fin.val_succ, List.getD_cons_succ, ih, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      rw [pow_succ]
      ring

/-- The carry adder computes an integer linear combination of words modulo `2^n`. -/
theorem carryRun_lin (n k : ℕ) (a : Fin k → ℤ) (xs : Fin k → List Bool)
    (hlen : ∀ i, (xs i).length = n) :
    ((valBits (carryRun 0 (List.ofFn fun t : Fin n =>
        ∑ i, a i * (((xs i).getD t false).toNat : ℤ))).1 : ℤ) : ZMod (2 ^ n)) =
      ((∑ i, a i * (valBits (xs i) : ℤ) : ℤ) : ZMod (2 ^ n)) := by
  have h := carryRun_val 0 (List.ofFn fun t : Fin n =>
        ∑ i, a i * (((xs i).getD t false).toNat : ℤ))
  have hc : colVal (List.ofFn fun t : Fin n => ∑ i, a i * (((xs i).getD t false).toNat : ℤ)) =
      ∑ i, a i * (valBits (xs i) : ℤ) := by
    rw [colVal_ofFn]
    simp only [valBits_sum n _ (hlen _), Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro t _
    ring
  rw [hc, List.length_ofFn, zero_add] at h
  have h' := congrArg (fun z : ℤ => (z : ZMod (2 ^ n))) h
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h'
  have h2 : (2 : ZMod (2 ^ n)) ^ n = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ n)
  rw [h2, zero_mul, add_zero] at h'
  exact h'

/-- The low `W` bits of a number below `2^W` have its value. -/
lemma valBits_testBit (W n : ℕ) (hn : n < 2 ^ W) :
    valBits (List.ofFn fun t : Fin W => n.testBit t) = n := by
  induction W generalizing n with
  | zero => simp at hn; simp [hn, valBits]
  | succ W ih =>
      rw [List.ofFn_succ, valBits]
      have hs : (fun t : Fin W => n.testBit (Fin.succ t)) = fun t : Fin W => (n / 2).testBit t := by
        funext t; simp [Nat.testBit_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.testBit_succ] at hs ⊢
      rw [ih (n / 2) (by rw [pow_succ] at hn; omega)]
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

lemma valBits_val (W : ℕ) (x : ZMod (2 ^ W)) :
    valBits (List.ofFn fun t : Fin W => x.val.testBit t) = x.val :=
  valBits_testBit W x.val (ZMod.val_lt x)

end IntegerMultBounds.MathlibTM2.Layer
