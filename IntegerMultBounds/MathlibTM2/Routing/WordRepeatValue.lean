module

public import IntegerMultBounds.MathlibTM2.Routing.WordRepeat
public import IntegerMultBounds.MathlibTM2.Routing.SourceMask
public import IntegerMultBounds.MathlibTM2.Layer.CompactMasks

/-! Numeric meaning of the literal repeated words emitted by the generator.
This supplies the bridge from tape copies to repeated classifier-mask blocks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open Finset

theorem counterValue_append (xs ys : List Bool) :
    Counter.value (xs ++ ys) = Counter.value xs + 2 ^ xs.length * Counter.value ys := by
  induction xs with
  | nil => simp [Counter.value]
  | cons b xs ih =>
    simp only [List.cons_append, Counter.value, List.length_cons, ih, pow_succ]
    cases b <;> simp <;> ring

def repeatBlockValue (n stride value : ℕ) : ℕ :=
  ∑ c ∈ range n, 2 ^ (c * stride) * value

theorem wordCopies_length {α : Type} (word : List α) (n : ℕ) :
    (wordCopies word n).length = n * word.length := by
  induction n with
  | zero => simp [wordCopies]
  | succ n ih => simp [wordCopies, ih, Nat.add_mul]

theorem wordCopies_value (word : List Bool) (n : ℕ) :
    Counter.value (wordCopies word n) = repeatBlockValue n word.length (Counter.value word) := by
  induction n with
  | zero => simp [wordCopies, Counter.value, repeatBlockValue]
  | succ n ih =>
    rw [wordCopies, counterValue_append, wordCopies_length, ih]
    simp [repeatBlockValue, sum_range_succ]

theorem wordCopies_binSyms {A : ℕ} (word : List Bool) (n : ℕ) :
    (wordCopies word n).map (bitSymbol (a := A)) =
      binSyms (n * word.length) (repeatBlockValue n word.length (Counter.value word)) := by
  have hv := binaryBits_value_repr (wordCopies word n)
  rw [wordCopies_length, wordCopies_value] at hv
  rw [binSyms_eq, hv]

theorem maskVal_arithmetic (n offset stride : ℕ) :
    maskVal n (fun c => offset + c * stride) = 2 ^ offset * repeatBlockValue n stride 1 := by
  simp only [maskVal, repeatBlockValue, pow_add, Nat.mul_one, mul_sum]

end IntegerMultBounds.MathlibTM2.Routing
