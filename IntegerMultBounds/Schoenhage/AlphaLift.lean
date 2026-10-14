module

public import IntegerMultBounds.Schoenhage.OfHoare

/-! Word-program primitives over any alphabet run over any larger one: word
tapes use only the blank, the two bits and the separator, whose codes every
alphabet shares (`embed_enc`), so the embedded program keeps the primitive's
contract (`Prim.liftE`, `runs_ofHoare_liftE`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a b t q : ℕ}

/-- The symbols of a smaller alphabet inside a larger one, by their codes. -/
def embed (h : a ≤ b) : Alphabet.Encoding a b where
  encode x := ⟨x.val, by have := x.isLt; omega⟩
  decode y := if hy : y.val < a + 4 then ⟨y.val, hy⟩ else blank
  decode_encode x := by simp [x.isLt]

theorem embed_tape (h : a ≤ b) (T : WTape) (j : ℤ) :
    (embed h).encode (T.tape (a := a) j) = T.tape (a := b) j := by
  apply Fin.ext
  simp only [embed, WTape.tape_eq]
  split_ifs
  · cases (syms T.words)[j.toNat]? with
    | none => rfl
    | some o => cases o with
      | none => rfl
      | some c => cases c <;> rfl
  · rfl

theorem embed_enc (h : a ≤ b) (σ : Fin t → WTape) :
    Alphabet.mapTapes (embed h) (enc (a := a) σ) = enc (a := b) σ := by
  simp only [Alphabet.mapTapes, enc, embed_tape]

/-- A primitive over a smaller alphabet, run over a larger one. -/
noncomputable def Prim.liftE (h : a ≤ b) (P : Prim a) : Prim b :=
  Prim.ofProgram (Alphabet.program (embed h) (P.M.toProgram P.hs)) P.hs P.pre P.sem P.cost (fun σ hσ =>
    (Alphabet.map_hoare (embed h) (P.spec σ hσ)).consequence
      (fun v hv => ⟨enc σ, rfl, hv.trans (embed_enc h σ).symm⟩)
      (fun v ⟨_, ho, hv⟩ => by rw [hv, ho, embed_enc]) le_rfl)

/-- Calling the primitive of a contract over a larger alphabet. -/
theorem runs_ofHoare_liftE (h : a ≤ b) (M : Program t q a) (ht : 0 < t) {s : ℕ} {slot : Fin t → Fin s}
    (hinj : Function.Injective slot) {σ : Fin s → WTape} {τ' : Fin t → WTape} {k : ℕ}
    (hM : HoareTo M (σ ∘ slot) τ' k) :
    Runs (a := b) (.prim (Prim.liftE h (Prim.ofHoare M ht)) slot hinj) σ (· = upd σ slot τ') k := by
  obtain ⟨hpre, hsem, hcost⟩ := ofHoare_spec M ht hM
  exact ⟨_, _, Exec.prim (P := Prim.liftE h (Prim.ofHoare M ht)) hpre, congrArg (upd σ slot) hsem, hcost⟩

end IntegerMultBounds.Schoenhage
