module

public import IntegerMultBounds.Schoenhage.ProgPrim
public import IntegerMultBounds.Machine.Alphabet

/-! Word-program primitives over the four-symbol alphabet run over any larger
alphabet. Word tapes use only the blank, the two bits and the separator, whose
values are the same in every alphabet (`widen_enc`); so the widened program of
a primitive keeps its contract (`Prim.lift`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

variable {q : ℕ}

/-- The four basic symbols inside a larger alphabet. -/
def widen : Alphabet.Encoding 0 q where
  encode x := ⟨x.val, by omega⟩
  decode x := if hx : x.val < 4 then ⟨x.val, hx⟩ else blank
  decode_encode x := by simp [x.isLt]

theorem widen_tape (T : WTape) (j : ℤ) : (widen (q := q)).encode (T.tape (a := 0) j) = T.tape (a := q) j := by
  apply Fin.ext
  simp only [widen, WTape.tape_eq]
  split_ifs
  · cases (syms T.words)[j.toNat]? with
    | none => rfl
    | some o => cases o with
      | none => rfl
      | some b => cases b <;> rfl
  · rfl

theorem widen_enc {t : ℕ} (σ : Fin t → WTape) :
    Alphabet.mapTapes (widen (q := q)) (enc (a := 0) σ) = enc (a := q) σ := by
  simp only [Alphabet.mapTapes, enc, widen_tape]

/-- A four-symbol primitive over a larger alphabet. -/
noncomputable def Prim.lift (P : Prim 0) : Prim q :=
  Prim.ofProgram (Alphabet.program widen (P.M.toProgram P.hs)) P.hs P.pre P.sem P.cost (fun σ hσ =>
    (Alphabet.map_hoare widen (P.spec σ hσ)).consequence
      (fun v hv => ⟨enc σ, rfl, hv.trans (widen_enc σ).symm⟩)
      (fun v ⟨_, ho, hv⟩ => by rw [hv, ho, widen_enc]) le_rfl)

end IntegerMultBounds.Schoenhage
