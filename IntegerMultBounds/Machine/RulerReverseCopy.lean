module

public import IntegerMultBounds.Machine.RulerCopy
public import IntegerMultBounds.Machine.Reflection

/-! A ruler-bounded backward field copy, independent of source delimiters.
Reflecting only the source head of RulerCopy gives a fixed one-state machine:
exactly one transition per field bit, with source and ruler cells preserved.
This can extract an MSB-first field inside a contiguous complex record. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RulerReverseCopy
variable {alphabet : ℕ}

def mask (slot : Fin 3) : Bool := decide (slot = 1)
def program : Program 3 1 alphabet := Reflection.program RulerCopy.program mask

theorem reflected_bank (ruler source destination : ℤ → Fin (alphabet + 4))
    (rulerHead sourceHead destinationHead : ℤ) :
    Reflection.tapes mask (RulerCopy.cfg ruler source destination rulerHead sourceHead destinationHead).tapes =
      (RulerCopy.cfg ruler (fun position => source (-position)) destination rulerHead (-sourceHead) destinationHead).tapes := by
  dsimp only [Reflection.tapes, RulerCopy.cfg, Config.tapes]
  congr 1
  · funext slot; fin_cases slot <;> simp [Reflection.coord, mask]
  · funext slot position; fin_cases slot <;> simp [Reflection.coord, mask]

/-- Arbitrary source cells may be adjacent to the field; the independent
ruler is the stopping condition, so neither a marker nor a blank is needed
at either field boundary. Only the destination interval is overwritten. -/
theorem reverse_hoare (ruler source destination : ℤ → Fin (alphabet + 4))
    (rulerHead sourceHead destinationHead : ℤ) (rulerSymbols : List (Fin (alphabet + 4)))
    (rulerNonblank : ∀ symbol ∈ rulerSymbols, symbol ≠ blank)
    (rulerEnd : ruler (rulerHead + rulerSymbols.length) = blank) :
    HoareTime program
      (· = (RulerCopy.cfg (putWord ruler rulerHead rulerSymbols) source destination
        rulerHead sourceHead destinationHead).tapes)
      (· = (RulerCopy.cfg (putWord ruler rulerHead rulerSymbols) source
        (putWord destination destinationHead
          (CopyCells.cells (fun position => source (-position)) (-sourceHead) rulerSymbols.length))
        (rulerHead + rulerSymbols.length) (sourceHead - rulerSymbols.length)
        (destinationHead + rulerSymbols.length)).tapes) rulerSymbols.length := by
  have forwardCopy := RulerCopy.copy_hoare ruler (fun position => source (-position)) destination
    rulerHead (-sourceHead) destinationHead rulerSymbols rulerNonblank rulerEnd
  have reflectedCopy := Reflection.hoare forwardCopy mask
  apply reflectedCopy.consequence
  · intro bank bankReady
    refine ⟨_, rfl, ?_⟩
    rw [reflected_bank]
    simpa only [neg_neg] using bankReady
  · intro bank ⟨original, originalReady, reflectedReady⟩
    rw [originalReady, reflected_bank] at reflectedReady
    simpa only [neg_neg, neg_add_rev, sub_eq_add_neg, add_comm] using reflectedReady
  · rfl

/-- Copying a physically placed Boolean field from its high end writes the
exact reversed field and preserves every cell outside it. -/
theorem reversed_field (background : ℤ → Fin (alphabet + 4)) (origin : ℤ) (field : List Bool) :
    CopyCells.cells (fun position => putWord background origin (field.map bitSymbol) (-position))
      (-(origin + field.length - 1)) field.length = field.reverse.map bitSymbol := by
  have reflection := Reflection.word background origin (field.map bitSymbol)
  simp only [List.length_map, ← List.map_reverse] at reflection
  rw [reflection]
  have reflectedOrigin : -(origin + (field.length : ℤ) - 1) = -origin - field.length + 1 := by omega
  rw [reflectedOrigin]
  simpa only [List.length_reverse] using CopyCells.cells_putWord
    (fun position => background (-position)) (-origin - field.length + 1) field.reverse

/-- Exact native field transfer: the ruler determines the length, the public
MSB field is read backwards, and a framed destination receives its LSB form. -/
theorem field_hoare (ruler background destination : ℤ → Fin (alphabet + 4))
    (rulerHead origin destinationHead : ℤ) (field : List Bool)
    (rulerSymbols : List (Fin (alphabet + 4)))
    (rulerLength : rulerSymbols.length = field.length)
    (rulerNonblank : ∀ symbol ∈ rulerSymbols, symbol ≠ blank)
    (rulerEnd : ruler (rulerHead + rulerSymbols.length) = blank) :
    HoareTime program
      (· = (RulerCopy.cfg (putWord ruler rulerHead rulerSymbols)
        (putWord background origin (field.map bitSymbol)) destination
        rulerHead (origin + field.length - 1) destinationHead).tapes)
      (· = (RulerCopy.cfg (putWord ruler rulerHead rulerSymbols)
        (putWord background origin (field.map bitSymbol))
        (putWord destination destinationHead (field.reverse.map bitSymbol))
        (rulerHead + field.length) (origin - 1) (destinationHead + field.length)).tapes) field.length := by
  have copiedField := reverse_hoare ruler (putWord background origin (field.map bitSymbol)) destination
    rulerHead (origin + field.length - 1) destinationHead rulerSymbols rulerNonblank rulerEnd
  rw [rulerLength, reversed_field] at copiedField
  have sourceEnd : origin + (field.length : ℤ) - 1 - field.length = origin - 1 := by omega
  simpa only [sourceEnd] using copiedField

end IntegerMultBounds.Machine.RulerReverseCopy
