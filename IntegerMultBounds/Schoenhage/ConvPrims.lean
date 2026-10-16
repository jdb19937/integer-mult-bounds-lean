module

public import IntegerMultBounds.Schoenhage.ConvScaleRun
public import IntegerMultBounds.Spec.SyntheticConvolution
public import IntegerMultBounds.Schoenhage.OfHoare

/-! A program in the paper's raw format with a header on tape 0, an operand
on tape 1 and its output on tape 3 (`bank hdr F [] O`) run between word tapes:
unseal tapes 0 and 1, run, seal tapes 0, 1 and 3 (`prog2_hoare`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct

variable {t q a : ℕ}

theorem emp_tape' : (emp : WTape).tape (a := a) = fun _ => blank := by
  funext j; simp [WTape.tape, wordTape, WTape.words, emp, cells, syms]

theorem wordAt_nil' : wordAt (a := a) [] = fun _ => blank := by
  funext j; simp [wordAt, wordTape]

/-- Header and operand as words on tapes 0 and 1, every other tape empty. -/
def start2 (t : ℕ) (hdr F : List Bool) : Fin t → WTape :=
  fun i => if i.val = 0 then reg hdr else if i.val = 1 then reg F else emp

/-- Tape `j` of a bank with at least four tapes. -/
def tp (ht : 4 ≤ t) (j : ℕ) (hj : j < 4) : Fin t := ⟨j, by omega⟩

/-- Unseal tapes 0 and 1, run `M`, seal tapes 0, 1 and 3. -/
noncomputable def prog2 (M : Program t q a) (ht : 4 ≤ t) :=
  Machine.seq (unsealAt (tp ht 0 (by decide))) <| Machine.seq (unsealAt (tp ht 1 (by decide))) <|
  Machine.seq M <| Machine.seq (sealAt (tp ht 0 (by decide))) <| Machine.seq (sealAt (tp ht 1 (by decide)))
    (sealAt (tp ht 3 (by decide)))

theorem reg_pos (w : List Bool) : (reg w).pos = 0 := rfl
theorem emp_pos : emp.pos = 0 := rfl

set_option maxHeartbeats 4000000 in
theorem prog2_hoare (M : Program t q a) (ht : 4 ≤ t) {hdr F O : List Bool} {k : ℕ}
    (hM : HoareTime M (· = bank hdr F [] []) (· = bank hdr F [] O) k) :
    HoareTime (prog2 M ht) (· = enc (start2 t hdr F))
      (· = enc (Function.update (start2 t hdr F) (tp ht 3 (by decide)) (reg O)))
      (k + 4 * (hdr.length + F.length + O.length) + 40) := by
  have v0 : (tp ht 0 (by decide)).val = 0 := rfl
  have v1 : (tp ht 1 (by decide)).val = 1 := rfl
  have v3 : (tp ht 3 (by decide)).val = 3 := rfl
  have n10 : tp ht 1 (by decide) ≠ tp ht 0 (by decide) := Fin.ne_of_val_ne (by rw [v0, v1]; decide)
  have n30 : tp ht 3 (by decide) ≠ tp ht 0 (by decide) := Fin.ne_of_val_ne (by rw [v0, v3]; decide)
  have n31 : tp ht 3 (by decide) ≠ tp ht 1 (by decide) := Fin.ne_of_val_ne (by rw [v1, v3]; decide)
  set u0 := enc (a := a) (start2 t hdr F)
  have hh0 : u0.head = fun _ => 0 := by
    funext x; simp only [u0, enc, start2]; split_ifs <;> rfl
  have h1 := unsealAt_hoare (a := a) (tp ht 0 (by decide)) hdr u0 (by rw [hh0])
    (by simp [u0, enc, start2, v0, reg])
  set u1 : Tapes t a := ⟨u0.head, Function.update u0.tape (tp ht 0 (by decide)) (wordAt hdr)⟩
  have h2 := unsealAt_hoare (a := a) (tp ht 1 (by decide)) F u1 (by simp [u1, hh0])
    (by simp [u1, u0, enc, start2, v1, reg, Function.update_of_ne n10])
  have e2 : (⟨u1.head, Function.update u1.tape (tp ht 1 (by decide)) (wordAt F)⟩ : Tapes t a) =
      bank hdr F [] [] := by
    simp only [u1, bank, hh0, Tapes.mk.injEq, true_and]
    funext i
    simp only [Function.update_apply, u0, enc, start2, Fin.ext_iff, v0, v1]
    split_ifs <;> first | rfl | omega | simp [emp_tape']
  set u3 := bank (t := t) (a := a) hdr F [] O
  have h4 := sealAt_hoare (a := a) (tp ht 0 (by decide)) hdr u3 rfl (by simp [u3, bank, v0])
  set u4 : Tapes t a := ⟨u3.head, Function.update u3.tape (tp ht 0 (by decide)) (⟨[], [hdr]⟩ : WTape).tape⟩
  have h5 := sealAt_hoare (a := a) (tp ht 1 (by decide)) F u4 rfl
    (by simp [u4, u3, bank, v1, Function.update_of_ne n10])
  set u5 : Tapes t a := ⟨u4.head, Function.update u4.tape (tp ht 1 (by decide)) (⟨[], [F]⟩ : WTape).tape⟩
  have h6 := sealAt_hoare (a := a) (tp ht 3 (by decide)) O u5 rfl
    (by simp [u5, u4, u3, bank, v3, Function.update_of_ne n30, Function.update_of_ne n31])
  have e6 : (⟨u5.head, Function.update u5.tape (tp ht 3 (by decide)) (⟨[], [O]⟩ : WTape).tape⟩ : Tapes t a) =
      enc (Function.update (start2 t hdr F) (tp ht 3 (by decide)) (reg O)) := by
    simp only [u5, u4, u3, bank, enc, Tapes.mk.injEq]
    constructor
    · funext x
      simp only [Function.update_apply, start2]
      split_ifs <;> rfl
    · funext i
      simp only [Function.update_apply, start2, Fin.ext_iff, v0, v1, v3]
      split_ifs <;> first | rfl | omega | simp [emp_tape']
  refine (h1.seq (h2.seq ((hM.consequence (fun v h => h.trans e2) (fun v h => h) le_rfl).seq
    (h4.seq (h5.seq h6))))).consequence (fun v h => h) (fun v h => h.trans e6) ?_
  omega

end IntegerMultBounds.Schoenhage
