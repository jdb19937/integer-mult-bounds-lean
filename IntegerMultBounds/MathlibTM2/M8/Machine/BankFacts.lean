module

public import IntegerMultBounds.Machine.Shared50RecursiveBank

/-!
# Header cells of the permanent recursive bank

The six layout headers sit at fixed slots after the role tapes (`RecursiveCallBank.headerSlot`).
With a symbolic role count the bank's cells there do not reduce by `rfl`; `bank_header` reads
them through the `Fin.addCases` simp lemmas.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.BankFacts

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {t u : ℕ}

/-- Header `i` of the bank: head `1`, the encoded header word. -/
theorem bank_header (roles : Tapes t prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime + 4))
    (p : ℤ) (node scalar : Tapes 1 prime) (aux : Tapes u prime) (st : Tapes 2 prime) (i : Fin 6) :
    (Shared50RecursiveBank.bank roles hs f p node scalar aux st).head (RecursiveCallBank.headerSlot i) = 1 ∧
      (Shared50RecursiveBank.bank roles hs f p node scalar aux st).tape (RecursiveCallBank.headerSlot i) =
        RadixZeroFill.encodedBinary (hs i) := by
  simp only [Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
    RecursiveCallBank.headerSlot, Tapes.append, Fin.addCases_left, Fin.addCases_right,
    RecursiveShiftRoleBank.headers]
  constructor <;> trivial

end
end IntegerMultBounds.MathlibTM2.M8.Machine.BankFacts
