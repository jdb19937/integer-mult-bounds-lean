module

public import IntegerMultBounds.MathlibTM2.Routing.WordRepeatValue
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalData

/-! Literal repeated arithmetic words are one padded arithmetic register.
Both its exact value and its fit bound follow from structural word semantics. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

theorem wordCopies_map {α β : Type} (f : α → β) (word : List α) (n : ℕ) :
    (wordCopies word n).map f = wordCopies (word.map f) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wordCopies, List.map_append, ih]

theorem wordCopies_binSyms_eq {A : ℕ} (W value n : ℕ) (hvalue : value < 2 ^ W) :
    wordCopies (binSyms (A := A) W value) n = binSyms (n * W) (repeatBlockValue n W value) := by
  conv_lhs => rw [binSyms_eq, ← wordCopies_map]
  rw [wordCopies_binSyms]
  simp only [length_binBits, binaryCanonical_value_binBits W value hvalue]

theorem repeatBlockValue_lt (W value n : ℕ) (hvalue : value < 2 ^ W) :
    repeatBlockValue n W value < 2 ^ (n * W) := by
  have h := Counter.value_lt (wordCopies (binBits W value) n)
  simpa only [wordCopies_value, wordCopies_length, length_binBits,
    binaryCanonical_value_binBits W value hvalue] using h

theorem temporaryBlockValue_lt (K G : ℕ) (hGK : G ≤ K) : maskVal G id < 2 ^ K := by
  have hfit : maskVal G id < 2 ^ G := by
    rw [maskVal_eq_placeVal]
    exact placeVal_lt strictMono_id _ G
  exact hfit.trans_le (Nat.pow_le_pow_right (by decide) hGK)

theorem temporaryRepeatedWord {A : ℕ} (K G n : ℕ) (hGK : G ≤ K) :
    wordCopies (binSyms (A := A) K (maskVal G id)) n =
      binSyms (n * K) (repeatBlockValue n K (maskVal G id)) :=
  wordCopies_binSyms_eq K (maskVal G id) n (temporaryBlockValue_lt K G hGK)

end IntegerMultBounds.MathlibTM2.Routing
