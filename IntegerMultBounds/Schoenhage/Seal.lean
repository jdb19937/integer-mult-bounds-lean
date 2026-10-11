module

public import IntegerMultBounds.Schoenhage.Ops
public import IntegerMultBounds.Spec.SignedRingProduct

/-! The boundary between raw bit strings and word tapes. A raw string on a
tape (`wordAt`, bits from cell zero, blank after) becomes one word of the
word-tape layer by writing a separator after its last bit (`Seal`), and back
by erasing that separator (`Unseal`). Both are one-tape machines that end
with the head at cell zero; placed on any tape of a bank they change only
that tape (`sealAt_hoare`, `unsealAt_hoare`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct

variable {a : ℕ}

/-- One word on a word tape is the raw string with a separator after it. -/
theorem sealed_eq (bs : List Bool) :
    (⟨[], [bs]⟩ : WTape).tape (a := a) = Function.update (wordAt bs) (bs.length : ℤ) separator := by
  funext j
  rw [WTape.tape_eq]
  simp only [WTape.words, List.reverse_nil, List.nil_append, syms_cons, syms_nil, List.append_nil]
  by_cases hj : j = bs.length
  · subst hj
    simp [sym]
  · rw [Function.update_of_ne hj]
    unfold wordAt wordTape
    split_ifs with h0
    · rcases lt_or_gt_of_ne (show j.toNat ≠ bs.length by omega) with hl | hl
      · rw [List.getElem?_append_left (by simpa using hl)]
        simp [hl, sym]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        rfl
    · rfl

theorem wordAt_bit (bs : List Bool) (c : ℕ) (hc : c < bs.length) :
    wordAt (a := a) bs c = bitSymbol bs[c] := by
  simp [wordAt, wordTape, hc]

theorem wordAt_end (bs : List Bool) : wordAt (a := a) bs bs.length = blank := by
  simp [wordAt, wordTape]

theorem wordAt_neg (bs : List Bool) : wordAt (a := a) bs (-1) = blank := by
  simp [wordAt, wordTape]

theorem bitSymbol_ne_blank (b : Bool) : bitSymbol (a := a) b ≠ blank := by
  cases b <;> simp [bitSymbol, blank, Fin.ext_iff]

theorem bitSymbol_ne_separator (b : Bool) : bitSymbol (a := a) b ≠ separator := by
  cases b <;> simp [bitSymbol, separator, Fin.ext_iff]

/-! ### Returning to cell zero -/

inductive SealSt where
  | scan | back | done
  deriving DecidableEq

instance : Fintype SealSt := ⟨{.scan, .back, .done}, by intro x; cases x <;> simp⟩

/-- Scan right to the first cell holding `stop`, write `put` there, return to cell zero. -/
abbrev sealMachine (stop put : Fin (a + 4)) : FMachine 1 a where
  S := SealSt
  start := .scan
  δ s syms := match s with
    | .scan => if syms 0 = stop then some (.back, fun _ => (put, .left))
        else some (.scan, fun _ => (syms 0, .right))
    | .back => if syms 0 = blank then some (.done, fun _ => (syms 0, .right))
        else some (.back, fun _ => (syms 0, .left))
    | .done => none

theorem seal_scan (stop put : Fin (a + 4)) (f : ℤ → Fin (a + 4)) :
    ∀ (n : ℕ) (h : ℤ), (∀ c : ℕ, c < n → f (h + c) ≠ stop) → f (h + n) = stop →
      (sealMachine stop put).frun (n + 1) ⟨.scan, one h f⟩ =
        some ⟨.back, one (h + n - 1) (Function.update f (h + n) put)⟩
  | 0, h, _, hb => by
    simp only [Nat.cast_zero, add_zero] at hb ⊢
    rw [FMachine.frun_one, step_write (sealMachine stop put) (s' := .back) put .left (by simp [hb])]
    simp [Move.offset]; ring
  | n + 1, h, hnb, hb => by
    have h0 : f h ≠ stop := by simpa using hnb 0 (by omega)
    have ih := seal_scan stop put f n (h + 1) (fun c hc => by
      have := hnb (c + 1) (by omega); push_cast at this; rwa [show h + 1 + c = h + (c + 1) by ring])
      (by push_cast at hb; rwa [show h + 1 + n = h + (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_one (sealMachine stop put) (s' := .scan) .right (by simp [h0]))) ?_
    convert ih using 4
    · simp [Move.offset]
    · push_cast; ring
    · push_cast; ring

theorem seal_back (stop put : Fin (a + 4)) (f : ℤ → Fin (a + 4)) :
    ∀ (n : ℕ) (h : ℤ), (∀ c : ℕ, c < n → f (h - c) ≠ blank) → f (h - n) = blank →
      (sealMachine stop put).frun (n + 1) ⟨.back, one h f⟩ = some ⟨.done, one (h - n + 1) f⟩
  | 0, h, _, hb => by
    simp only [Nat.cast_zero, sub_zero] at hb
    rw [FMachine.frun_one, step_one (sealMachine stop put) (s' := .done) .right (by simp [hb])]
    simp [Move.offset]
  | n + 1, h, hnb, hb => by
    have h0 : f h ≠ blank := by simpa using hnb 0 (by omega)
    have ih := seal_back stop put f n (h - 1) (fun c hc => by
      have := hnb (c + 1) (by omega); push_cast at this; rwa [show h - 1 - c = h - (c + 1) by ring])
      (by push_cast at hb; rwa [show h - 1 - n = h - (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_one (sealMachine stop put) (s' := .back) .left (by simp [h0]))) ?_
    convert ih using 4
    · simp [Move.offset]; ring
    · push_cast; ring

/-- The whole run: scan to the stop cell at `n`, write, return to zero. -/
theorem seal_run (stop put : Fin (a + 4)) (f : ℤ → Fin (a + 4)) (n : ℕ)
    (hs : ∀ c : ℕ, c < n → f c ≠ stop ∧ f c ≠ blank) (hn : f n = stop) (hneg : f (-1) = blank) :
    (sealMachine stop put).frun (n + 1 + (n + 1)) ⟨.scan, one 0 f⟩ =
      some ⟨.done, one 0 (Function.update f n put)⟩ := by
  have s1 := seal_scan stop put f n 0 (fun c hc => by simpa using (hs c hc).1) (by simpa using hn)
  simp only [zero_add] at s1
  have s2 := seal_back stop put (Function.update f n put) n (n - 1)
    (fun c hc => by
      rw [Function.update_of_ne (by omega), show (n : ℤ) - 1 - c = ((n - 1 - c : ℕ) : ℤ) by omega]
      exact (hs _ (by omega)).2)
    (by rw [show (n : ℤ) - 1 - n = -1 by ring, Function.update_of_ne (by omega)]; exact hneg)
  rw [FMachine.frun_trans _ s1 s2]
  congr 3; ring

theorem seal_halt (stop put : Fin (a + 4)) (v : Tapes 1 a) :
    (sealMachine stop put).fstep ⟨.done, v⟩ = none :=
  halt_one _ (fun _ => rfl)

/-! ### On one tape -/

/-- Write a separator after the raw string. -/
noncomputable def sealProg : Program 1 (Fintype.card SealSt) a :=
  (sealMachine (a := a) blank separator).toProgram (by omega)

/-- Erase the separator after the word. -/
noncomputable def unsealProg : Program 1 (Fintype.card SealSt) a :=
  (sealMachine (a := a) separator blank).toProgram (by omega)

theorem sealProg_hoare (bs : List Bool) :
    HoareTime (sealProg (a := a)) (· = one 0 (wordAt bs)) (· = one 0 (⟨[], [bs]⟩ : WTape).tape)
      (2 * bs.length + 6) := by
  apply FMachine.hoare
  intro v hv; subst hv
  refine ⟨bs.length + 1 + (bs.length + 1), _, by omega, seal_run blank separator (wordAt bs) bs.length
    (fun c hc => by rw [wordAt_bit _ c hc]; exact ⟨bitSymbol_ne_blank _, bitSymbol_ne_blank _⟩)
    (wordAt_end bs) (wordAt_neg bs), seal_halt _ _ _, ?_⟩
  rw [sealed_eq]

theorem unsealProg_hoare (bs : List Bool) :
    HoareTime (unsealProg (a := a)) (· = one 0 (⟨[], [bs]⟩ : WTape).tape) (· = one 0 (wordAt bs))
      (2 * bs.length + 6) := by
  apply FMachine.hoare
  intro v hv; subst hv
  have e : Function.update (Function.update (wordAt (a := a) bs) (bs.length : ℤ) separator)
      (bs.length : ℤ) blank = wordAt bs := by
    rw [Function.update_idem, ← wordAt_end bs, Function.update_eq_self]
  have run := seal_run (a := a) separator blank (Function.update (wordAt bs) (bs.length : ℤ) separator) bs.length
    (fun c hc => by
      rw [Function.update_of_ne (by omega), wordAt_bit _ c hc]
      exact ⟨bitSymbol_ne_separator _, bitSymbol_ne_blank _⟩)
    (by simp) (by rw [Function.update_of_ne (by omega)]; exact wordAt_neg bs)
  rw [e] at run
  refine ⟨bs.length + 1 + (bs.length + 1), ⟨.done, one 0 (wordAt bs)⟩, by omega, ?_, seal_halt _ _ _, rfl⟩
  rw [sealed_eq]; exact run

/-! ### On any tape of a bank -/

variable {t : ℕ}

theorem slot_const_inj (i : Fin t) : Function.Injective (fun _ : Fin 1 => i) := by
  intro x y _; exact Subsingleton.elim x y

theorem one_size (i : Fin t) : 1 + (t - 1) = t := by have := i.isLt; omega

/-- `sealProg` on tape `i`. -/
noncomputable def sealAt (i : Fin t) : Program t (Fintype.card SealSt) a :=
  Placement.placed sealProg (InjectivePlacement.placement (fun _ : Fin 1 => i) (slot_const_inj i) (one_size i))

/-- `unsealProg` on tape `i`. -/
noncomputable def unsealAt (i : Fin t) : Program t (Fintype.card SealSt) a :=
  Placement.placed unsealProg (InjectivePlacement.placement (fun _ : Fin 1 => i) (slot_const_inj i) (one_size i))

theorem place_one (i : Fin t) {q : ℕ} {M : Program 1 q a} {f g : ℤ → Fin (a + 4)} {b : ℕ}
    (h : HoareTime M (· = one 0 f) (· = one 0 g) b) (v : Tapes t a) (hh : v.head i = 0) (hf : v.tape i = f) :
    HoareTime (Placement.placed M (InjectivePlacement.placement (fun _ : Fin 1 => i) (slot_const_inj i)
      (one_size i))) (· = v) (· = ⟨v.head, Function.update v.tape i g⟩) b := by
  refine InjectivePlacement.hoare_exact h _ (slot_const_inj i) (one_size i) v _ ?_ ?_
  · rw [InjectivePlacement.active_bank]
    simp only [one, hh, hf]
  · refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · by_cases hx : x = i
      · subst hx
        have := InjectivePlacement.replace_head_slot (fun _ : Fin 1 => x) (slot_const_inj x) (one_size x) v
          (one 0 g) 0
        simpa [one, hh] using this
      · rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ (fun _ e => hx e.symm)]
    · by_cases hx : x = i
      · subst hx
        have := InjectivePlacement.replace_tape_slot (fun _ : Fin 1 => x) (slot_const_inj x) (one_size x) v
          (one 0 g) 0
        simpa [one] using this
      · rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ (fun _ e => hx e.symm)]
        show _ = Function.update v.tape i g x
        rw [Function.update_of_ne hx]

theorem sealAt_hoare (i : Fin t) (bs : List Bool) (v : Tapes t a) (hh : v.head i = 0)
    (hf : v.tape i = wordAt bs) :
    HoareTime (sealAt i) (· = v) (· = ⟨v.head, Function.update v.tape i (⟨[], [bs]⟩ : WTape).tape⟩)
      (2 * bs.length + 6) :=
  place_one i (sealProg_hoare bs) v hh hf

theorem unsealAt_hoare (i : Fin t) (bs : List Bool) (v : Tapes t a) (hh : v.head i = 0)
    (hf : v.tape i = (⟨[], [bs]⟩ : WTape).tape) :
    HoareTime (unsealAt i) (· = v) (· = ⟨v.head, Function.update v.tape i (wordAt bs)⟩)
      (2 * bs.length + 6) :=
  place_one i (unsealProg_hoare bs) v hh hf

end IntegerMultBounds.Schoenhage
