module

public import IntegerMultBounds.Machine
public import Mathlib.Computability.Encoding
import Mathlib.Data.List.TakeWhile

/-!
# Most-significant-first words and Mathlib's binary encoding

`IntegerMultBounds.Machine.binaryValue` reads a word most significant bit first, with leading
zeroes allowed. Mathlib's `Computability.encodeNat` writes a natural least significant bit
first, with no trailing zeroes. Reversing a word after dropping its leading zeroes gives the
Mathlib encoding of its value.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2

open IntegerMultBounds.Machine Computability

lemma encodeNum_bit0 (x : Num) : encodeNum (Num.bit0 x) = if x = 0 then [] else false :: encodeNum x := by
  cases x <;> rfl

lemma encodeNum_bit1 (x : Num) : encodeNum (Num.bit1 x) = true :: encodeNum x := by
  cases x <;> rfl

lemma encodeNat_eq (n : ℕ) : encodeNat n = encodeNum (Num.ofNat' n) := by
  rw [Num.ofNat'_eq]; rfl

lemma ofNat'_eq_zero {n : ℕ} : Num.ofNat' n = 0 ↔ n = 0 := by
  rw [Num.ofNat'_eq]
  constructor
  · intro h
    have := congrArg (fun x : Num => (x : ℕ)) h
    simpa using this
  · rintro rfl; rfl

/-- Appending a bit below the least significant position. -/
lemma encodeNat_bit (b : Bool) (m : ℕ) :
    encodeNat (Nat.bit b m) = if b then true :: encodeNat m
      else if m = 0 then [] else false :: encodeNat m := by
  rw [encodeNat_eq, Num.ofNat'_bit]
  cases b
  · simp only [Bool.cond_false, encodeNum_bit0, ofNat'_eq_zero, Bool.false_eq_true, ite_false,
      encodeNat_eq]
  · simp only [Bool.cond_true, encodeNum_bit1, ite_true, encodeNat_eq]

lemma binaryValue_append (l : List Bool) (b : Bool) :
    binaryValue (l ++ [b]) = Nat.bit b (binaryValue l) := by
  rw [Nat.bit_val]
  induction l with
  | nil => cases b <;> rfl
  | cons c l ih =>
      simp only [List.cons_append, binaryValue, List.length_append, List.length_singleton, ih,
        pow_succ]
      cases b <;> cases c <;> simp <;> ring

lemma binaryValue_eq_zero_iff (l : List Bool) : binaryValue l = 0 ↔ ∀ x ∈ l, x = false := by
  induction l with
  | nil => simp [binaryValue]
  | cons c l ih =>
      cases c <;> simp [binaryValue, ih]

/-- The Mathlib encoding of a word's value is the reversed word without leading zeroes. -/
theorem encodeNat_binaryValue (l : List Bool) :
    encodeNat (binaryValue l) = (l.dropWhile (fun b => !b)).reverse := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
      rw [binaryValue_append, encodeNat_bit, List.dropWhile_append]
      by_cases hz : binaryValue l = 0
      · have hall := (binaryValue_eq_zero_iff l).1 hz
        have hdrop : l.dropWhile (fun b => !b) = [] := by
          rw [List.dropWhile_eq_nil_iff]; intro x hx; simp [hall x hx]
        rw [hdrop, hz]
        cases b <;> rfl
      · have hdrop : l.dropWhile (fun b => !b) ≠ [] := by
          intro h
          rw [List.dropWhile_eq_nil_iff] at h
          exact hz ((binaryValue_eq_zero_iff l).2 fun x hx => by simpa using h x hx)
        rw [ih]
        simp only [List.isEmpty_iff, hdrop, ite_false, List.reverse_append, List.reverse_singleton,
          List.singleton_append, hz]
        cases b <;> rfl

/-- Reads a bit symbol of the machine alphabet. -/
def decodeBit {a : ℕ} (s : Fin (a + 4)) : Option Bool :=
  if s.val = 1 then some false else if s.val = 2 then some true else none

@[simp] lemma decodeBit_bitSymbol {a : ℕ} (b : Bool) : decodeBit (bitSymbol (a := a) b) = some b := by
  cases b <;> simp [decodeBit, bitSymbol]

@[simp] lemma decodeBit_blank {a : ℕ} : decodeBit (blank (a := a)) = none := by
  simp [decodeBit, blank]

end IntegerMultBounds.MathlibTM2
