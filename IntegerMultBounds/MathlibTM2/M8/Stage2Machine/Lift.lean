module

public import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-!
# Banks that keep a caller's tapes

`Lift F ℓ`: the bank `F c` holds every tape of the caller `c` at slot `ℓ j`, injectively, and
setting a caller tape sets its slot. Appending a bank lifts by `Fin.castAdd` (`append`), and lifts
compose (`comp`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine

open IntegerMultBounds.Machine
open SharedPlacementAlphabet (setTape)

variable {a t u w : ℕ}

/-- The bank `F c` keeps the caller `c` at the slots `ℓ`. -/
structure Lift (F : Tapes t a → Tapes u a) (ℓ : Fin t → Fin u) : Prop where
  inj : Function.Injective ℓ
  tape : ∀ c j, (F c).tape (ℓ j) = c.tape j
  head : ∀ c j, (F c).head (ℓ j) = c.head j
  set : ∀ c j f p, F (setTape c j f p) = setTape (F c) (ℓ j) f p

namespace Lift

theorem append {n : ℕ} (Y : Tapes n a) : Lift (t := t) (fun c => c.append Y) (Fin.castAdd n) where
  inj := Fin.castAdd_injective _ _
  tape c j := by simp only [Tapes.append, Fin.addCases_left]
  head c j := by simp only [Tapes.append, Fin.addCases_left]
  set c j f p := (SharedPlacementAlphabet.setTape_append_left c Y j f p).symm

theorem comp {F : Tapes t a → Tapes u a} {G : Tapes u a → Tapes w a} {ℓ : Fin t → Fin u} {ℓ' : Fin u → Fin w}
    (h : Lift F ℓ) (h' : Lift G ℓ') : Lift (fun c => G (F c)) (fun j => ℓ' (ℓ j)) where
  inj := h'.inj.comp h.inj
  tape c j := (h'.tape _ _).trans (h.tape c j)
  head c j := (h'.head _ _).trans (h.head c j)
  set c j f p := by rw [h.set, h'.set]

end Lift

end IntegerMultBounds.MathlibTM2.M8.Stage2Machine
