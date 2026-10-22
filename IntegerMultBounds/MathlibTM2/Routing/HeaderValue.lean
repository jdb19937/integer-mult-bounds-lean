module

public import IntegerMultBounds.MathlibTM2.Host.BinArithBits

/-!
# Arithmetic value of a contiguous live header

A structural chain of consecutive physical fields gives exactly the binary
window of the live index, including zero-width fields. This identifies copied
metadata with actual higher address bits without changing the field bank.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {nf A : ℕ}

/-- Consecutive fields beginning at bit offset `o`. -/
def HeaderChain (len : Fin nf → ℕ) : ℕ → List (Fin nf) → Prop
  | _, [] => True
  | o, f :: fs => fieldOff len f = o ∧ HeaderChain len (o + len f) fs

/-- Concatenating the actual counter tapes reads one contiguous index window. -/
theorem headerValue (len : Fin nf → ℕ) (fields : List (Fin nf)) (o i : ℕ)
    (hchain : HeaderChain len o fields) :
    (fields.flatMap fun f => binSyms (A := A) (len f) (digit len f i)) =
      binSyms ((fields.map len).sum) (i / 2 ^ o) := by
  induction fields generalizing o with
  | nil => simp [binSyms]
  | cons f fs ih =>
    obtain ⟨hoff, hrest⟩ := hchain
    rw [List.flatMap_cons, ih (o + len f) hrest, List.map_cons, List.sum_cons,
      binSyms_append]
    congr 1
    · simp only [digit, hoff, binSyms_mod]
    · rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

end IntegerMultBounds.MathlibTM2.Routing
