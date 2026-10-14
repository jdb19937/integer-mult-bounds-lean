module

public import IntegerMultBounds.Machine.WordTape

/-! Whole-tape representation equality at the raw bit-output boundary. -/
@[expose] public section
namespace IntegerMultBounds.Machine

/-- Writing at the origin of a completely blank tape produces exactly the
canonical word tape, including its negative cells and blank suffix. -/
theorem putWord_blank_origin {alphabet : ℕ} (symbols : List (Fin (alphabet + 4))) :
    putWord (fun _ => blank) 0 symbols = wordTape symbols := by
  funext cell
  simpa using putWord_blank (a := alphabet) 0 cell symbols

end IntegerMultBounds.Machine
