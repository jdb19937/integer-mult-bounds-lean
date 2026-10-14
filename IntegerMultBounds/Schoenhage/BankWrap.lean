module

public import IntegerMultBounds.Schoenhage.ConvPrims

/-! A word program in the paper's four-tape format: seal the header and the input, run the word
program, unseal header, input and output (`wrapProg`). A word program taking header and input on tapes
0 and 1, every other tape empty, to the same plus the output on tape 3 meets the bank contract
(`wrapProg_hoare`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct

variable {a T : ℕ}

/-- Header on tape 0, input on tape 1, `o` on tape 3, every other tape empty. -/
def w4 (T : ℕ) (hdr F : List Bool) (o : WTape) : Fin T → WTape := fun i =>
  if i.val = 0 then reg hdr else if i.val = 1 then reg F else if i.val = 3 then o else emp

/-- Tape `j < 4` of a bank of at least four tapes. -/
def t4 (hT : 4 ≤ T) (j : ℕ) (hj : j < 4) : Fin T := ⟨j, by omega⟩

/-- Seal header and input, run `c`, unseal header, input and output. -/
noncomputable def wrapProg (c : Cmd a T) (hT : 4 ≤ T) :=
  Machine.seq (sealAt (t4 hT 0 (by decide))) <| Machine.seq (sealAt (t4 hT 1 (by decide))) <|
  Machine.seq (compile (by omega) c).2 <|
  Machine.seq (unsealAt (t4 hT 0 (by decide))) <| Machine.seq (unsealAt (t4 hT 1 (by decide)))
    (unsealAt (t4 hT 3 (by decide)))

set_option maxHeartbeats 8000000 in
theorem wrapProg_hoare (c : Cmd a T) (hT : 4 ≤ T) {hdr F O : List Bool} {k : ℕ}
    (hc : Runs c (w4 T hdr F emp) (· = w4 T hdr F (reg O)) k) :
    HoareTime (wrapProg c hT) (· = bank hdr F [] []) (· = bank hdr F [] O)
      (k + 4 * (hdr.length + F.length + O.length) + 40) := by
  obtain ⟨σ', k', hx, hq, hk⟩ := hc
  subst hq
  have hcore := compile_correct (by omega : 0 < T) hx
  have v0 : (t4 hT 0 (by decide)).val = 0 := rfl
  have v1 : (t4 hT 1 (by decide)).val = 1 := rfl
  have v3 : (t4 hT 3 (by decide)).val = 3 := rfl
  have n10 : t4 hT 1 (by decide) ≠ t4 hT 0 (by decide) := Fin.ne_of_val_ne (by rw [v0, v1]; decide)
  have n30 : t4 hT 3 (by decide) ≠ t4 hT 0 (by decide) := Fin.ne_of_val_ne (by rw [v0, v3]; decide)
  have n31 : t4 hT 3 (by decide) ≠ t4 hT 1 (by decide) := Fin.ne_of_val_ne (by rw [v1, v3]; decide)
  set u0 := bank (t := T) (a := a) hdr F [] []
  have h1 := sealAt_hoare (a := a) (t4 hT 0 (by decide)) hdr u0 rfl (by simp [u0, bank, v0])
  set u1 : Tapes T a := ⟨u0.head, Function.update u0.tape (t4 hT 0 (by decide)) (⟨[], [hdr]⟩ : WTape).tape⟩
  have h2 := sealAt_hoare (a := a) (t4 hT 1 (by decide)) F u1 rfl
    (by simp [u1, u0, bank, v1, Function.update_of_ne n10])
  have e2 : (⟨u1.head, Function.update u1.tape (t4 hT 1 (by decide)) (⟨[], [F]⟩ : WTape).tape⟩ : Tapes T a) =
      enc (w4 T hdr F emp) := by
    simp only [u1, u0, bank, enc, Tapes.mk.injEq]
    constructor
    · funext x; simp only [w4]; split_ifs <;> rfl
    · funext i
      simp only [Function.update_apply, w4, Fin.ext_iff, v0, v1]
      split_ifs <;> first | rfl | omega | simp [emp_tape', wordAt_nil', reg]
  set w0 := enc (a := a) (w4 T hdr F (reg O))
  have hw0 : w0.head = fun _ => 0 := by
    funext x; simp only [w0, enc, w4]; split_ifs <;> rfl
  have g1 := unsealAt_hoare (a := a) (t4 hT 0 (by decide)) hdr w0 (by rw [hw0])
    (by simp [w0, enc, w4, v0, reg])
  set w1 : Tapes T a := ⟨w0.head, Function.update w0.tape (t4 hT 0 (by decide)) (wordAt hdr)⟩
  have g2 := unsealAt_hoare (a := a) (t4 hT 1 (by decide)) F w1 (by simp [w1, hw0])
    (by simp [w1, w0, enc, w4, v1, reg, Function.update_of_ne n10])
  set w2 : Tapes T a := ⟨w1.head, Function.update w1.tape (t4 hT 1 (by decide)) (wordAt F)⟩
  have g3 := unsealAt_hoare (a := a) (t4 hT 3 (by decide)) O w2 (by simp [w2, w1, hw0])
    (by simp [w2, w1, w0, enc, w4, v3, reg, Function.update_of_ne n30, Function.update_of_ne n31])
  have e3 : (⟨w2.head, Function.update w2.tape (t4 hT 3 (by decide)) (wordAt O)⟩ : Tapes T a) =
      bank hdr F [] O := by
    simp only [w2, w1, bank, Tapes.mk.injEq]
    refine ⟨hw0, ?_⟩
    funext i
    simp only [Function.update_apply, w0, enc, w4, Fin.ext_iff, v0, v1, v3]
    split_ifs <;> first | rfl | omega | simp [emp_tape', wordAt_nil', reg]
  refine (h1.seq ((h2.consequence (fun v h => h) (fun v h => h.trans e2) le_rfl).seq
    ((hcore.consequence (fun v h => h) (fun v h => h) hk).seq (g1.seq (g2.seq g3))))).consequence
    (fun v h => h) (fun v h => h.trans e3) ?_
  omega

end IntegerMultBounds.Schoenhage
