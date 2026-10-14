module

public import IntegerMultBounds.Schoenhage.Seal

/-! Between a one-word tape and a counter tape. A word tape holds the bits of
`bs` from cell zero and a separator after them, head at cell zero; a counter
tape (the header format of the address-chunk interchange) holds a separator
at cell zero and the bits of `bs` from cell one, head at cell one (`ctr`).
`toCtrProg` shifts the word one cell right behind a separator
(`toCtrProg_hoare`); `fromCtrProg` shifts it back (`fromCtrProg_hoare`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a : ℕ}

/-- The counter tape of `bs`. -/
def ctr (bs : List Bool) : ℤ → Fin (a + 4) :=
  fun j => if j = 0 then separator else wordAt' bs (j - 1)
where wordAt' (bs : List Bool) : ℤ → Fin (a + 4) := wordTape (bs.map bitSymbol)

/-- The word tape of `bs`. -/
def wtp (bs : List Bool) : ℤ → Fin (a + 4) := (⟨[], [bs]⟩ : WTape).tape

theorem wtp_eq (bs : List Bool) : wtp (a := a) bs = wordTape (bs.map bitSymbol ++ [separator]) := by
  simp [wtp, WTape.tape, WTape.words, cells, syms_cons, sym, Function.comp_def]

/-! ### Word to counter -/

inductive TCSt where
  | sh (c : Option Bool) | back | right1 | done
  deriving DecidableEq

instance : Fintype TCSt :=
  ⟨{.sh none, .sh (some false), .sh (some true), .back, .right1, .done}, by
    intro x; rcases x with (_ | ⟨_ | _⟩) | _ | _ | _ <;> simp⟩

/-- Shift the word right behind a separator, then return to cell one. -/
abbrev toCtrMachine : FMachine 1 a where
  S := TCSt
  start := .sh none
  δ s syms := match s with
    | .sh c => if syms 0 = separator then some (.back, fun _ => (sym c, .left))
        else if syms 0 = blank then none
        else some (.sh (some (decide (syms 0 = bitSymbol true))), fun _ => (sym c, .right))
    | .back => if syms 0 = blank then some (.right1, fun _ => (syms 0, .right))
        else some (.back, fun _ => (syms 0, .left))
    | .right1 => some (.done, fun _ => (syms 0, .right))
    | .done => none

theorem putWord_ite (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4))) (j : ℤ) :
    putWord f p xs j = if p ≤ j ∧ j < p + xs.length then wordTape xs (j - p) else f j := by
  induction xs generalizing p with
  | nil => simp [putWord]
  | cons x xs ih =>
    simp only [putWord, Function.update_apply, ih, List.length_cons]
    by_cases hj : j = p
    · subst hj; simp [wordTape]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]
      by_cases h1 : p + 1 ≤ j ∧ j < p + 1 + xs.length
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true (by push_cast; omega))]
        simp only [wordTape, ite_eq_left_of_eq_true _ _ (eq_true (show (0 : ℤ) ≤ j - (p + 1) by omega)),
          ite_eq_left_of_eq_true _ _ (eq_true (show (0 : ℤ) ≤ j - p by omega))]
        rw [show (j - p).toNat = (j - (p + 1)).toNat + 1 by omega]; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false (by push_cast; omega))]

theorem sym_none : sym (a := a) none = separator := rfl
theorem sym_some (b : Bool) : sym (a := a) (some b) = bitSymbol b := rfl

theorem bit_ne_sep (b : Bool) : bitSymbol (a := a) b ≠ separator := bitSymbol_ne_separator b

theorem decide_bit (b : Bool) : decide (bitSymbol (a := a) b = bitSymbol true) = b := by
  cases b <;> simp [bitSymbol, Fin.ext_iff]

theorem tc_shift : ∀ (xs : List Bool) (c : Option Bool) (f : ℤ → Fin (a + 4)) (h : ℤ),
    (∀ k : ℕ, (hk : k < xs.length) → f (h + k) = bitSymbol xs[k]) → f (h + xs.length) = separator →
      (toCtrMachine (a := a)).frun (xs.length + 1) ⟨.sh c, one h f⟩ =
        some ⟨.back, one (h + xs.length - 1) (putWord f h (sym c :: xs.map bitSymbol))⟩
  | [], c, f, h, _, hs => by
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hs ⊢
    rw [FMachine.frun_one, step_write toCtrMachine (s' := .back) (sym c) .left (by simp [hs])]
    simp [Move.offset, putWord]; rfl
  | x :: xs, c, f, h, hb, hs => by
    have h0 : f h = bitSymbol x := by
      have := hb 0 (by simp); simp only [Nat.cast_zero, add_zero, List.getElem_cons_zero] at this; exact this
    have ih := tc_shift xs (some x) (Function.update f h (sym c)) (h + 1)
      (fun k hk => by
        rw [Function.update_of_ne (by omega)]
        have := hb (k + 1) (by simp; omega); push_cast at this; rw [show h + 1 + k = h + (k + 1) by ring]; simpa using this)
      (by rw [Function.update_of_ne (by simp; omega)]; simp at hs; rw [show h + 1 + xs.length = h + (xs.length + 1) by ring]; exact hs)
    rw [List.length_cons, show xs.length + 1 + 1 = 1 + (xs.length + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_write toCtrMachine (s' := .sh (some x)) (sym c) .right (by
        simp [h0, bit_ne_sep, decide_bit, bitSymbol_ne_blank]))) ?_
    convert ih using 4
    · simp [Move.offset]
    · push_cast; ring
    · rw [List.map_cons, putWord_cons]; rfl

theorem tc_back (f : ℤ → Fin (a + 4)) : ∀ (n : ℕ) (h : ℤ), (∀ c : ℕ, c < n → f (h - c) ≠ blank) → f (h - n) = blank →
    (toCtrMachine (a := a)).frun (n + 1) ⟨.back, one h f⟩ = some ⟨.right1, one (h - n + 1) f⟩
  | 0, h, _, hb => by
    simp only [Nat.cast_zero, sub_zero] at hb
    rw [FMachine.frun_one, step_one toCtrMachine (s' := .right1) .right (by simp [hb])]
    simp [Move.offset]
  | n + 1, h, hnb, hb => by
    have h0 : f h ≠ blank := by simpa using hnb 0 (by omega)
    have ih := tc_back f n (h - 1) (fun c hc => by
      have := hnb (c + 1) (by omega); push_cast at this; rwa [show h - 1 - c = h - (c + 1) by ring])
      (by push_cast at hb; rwa [show h - 1 - n = h - (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_one toCtrMachine (s' := .back) .left (by simp [h0]))) ?_
    convert ih using 4
    · simp [Move.offset]; ring
    · push_cast; ring

theorem ctr_eq (bs : List Bool) :
    putWord (wtp (a := a) bs) 0 (separator :: bs.map bitSymbol) = ctr bs := by
  funext j
  rw [putWord_ite, wtp_eq]
  simp only [ctr, ctr.wordAt', List.length_cons, List.length_map]
  rcases lt_trichotomy j 0 with hneg | rfl | hpos
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    simp only [wordTape, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (0 : ℤ) ≤ j by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (0 : ℤ) ≤ j - 1 by omega))]
  · simp [wordTape]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (show j ≠ 0 by omega))]
    by_cases hin : j < 0 + ((bs.length + 1 : ℕ) : ℤ)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hin⟩)]
      simp only [wordTape, ite_eq_left_of_eq_true _ _ (eq_true (show (0 : ℤ) ≤ j - 0 by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show (0 : ℤ) ≤ j - 1 by omega))]
      rw [show (j - 0).toNat = (j - 1).toNat + 1 by omega]; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      simp only [wordTape, ite_eq_left_of_eq_true _ _ (eq_true (show (0 : ℤ) ≤ j by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show (0 : ℤ) ≤ j - 1 by omega))]
      push_cast at hin
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem tc_halt (v : Tapes 1 a) : (toCtrMachine (a := a)).fstep ⟨.done, v⟩ = none := halt_one _ (fun _ => rfl)

/-- Word tape to counter tape. -/
noncomputable def toCtrProg : Program 1 (Fintype.card TCSt) a := (toCtrMachine (a := a)).toProgram (by omega)

theorem toCtrProg_hoare (bs : List Bool) :
    HoareTime (toCtrProg (a := a)) (· = one 0 (wtp bs)) (· = one 1 (ctr bs)) (2 * bs.length + 4) := by
  apply FMachine.hoare
  intro v hv; subst hv
  have hwt : ∀ k : ℕ, (hk : k < bs.length) → wtp (a := a) bs (0 + k) = bitSymbol bs[k] := fun k hk => by
    rw [wtp_eq, zero_add]
    simp only [wordTape, ite_eq_left_of_eq_true _ _ (eq_true (show (0 : ℤ) ≤ k by omega)), Int.toNat_natCast]
    rw [List.getElem?_append_left (by simpa using hk)]; simp [List.getElem?_eq_getElem hk]
  have hsep : wtp (a := a) bs (0 + bs.length) = separator := by rw [wtp_eq, zero_add]; simp [wordTape]
  have s1 := tc_shift bs none (wtp bs) 0 hwt hsep
  rw [sym_none, ctr_eq] at s1
  have s2 := tc_back (ctr (a := a) bs) bs.length ((0 : ℤ) + bs.length - 1)
    (fun c hc => by
      simp only [ctr, ctr.wordAt']
      by_cases h0 : (0 : ℤ) + bs.length - 1 - c = 0
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]; simp [separator, blank]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]; simp only [wordTape]
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
        have hl : bs.length - 1 - c - 1 < bs.length := by omega
        have e : ((0 : ℤ) + bs.length - 1 - c - 1).toNat = bs.length - 1 - c - 1 := by omega
        rw [e, List.getElem?_map, List.getElem?_eq_getElem hl]; simp [bitSymbol_ne_blank])
    (by simp only [ctr, ctr.wordAt']; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; simp [wordTape])
  have s3 : (toCtrMachine (a := a)).frun 1 ⟨.right1, one ((0 : ℤ) + bs.length - 1 - bs.length + 1) (ctr bs)⟩ =
      some ⟨.done, one 1 (ctr bs)⟩ := by
    rw [FMachine.frun_one, step_one toCtrMachine (s' := .done) .right (by simp)]
    congr 3; simp [Move.offset]
  refine ⟨bs.length + 1 + (bs.length + 1) + 1, _, by omega, ?_, tc_halt _, rfl⟩
  exact FMachine.frun_trans _ (FMachine.frun_trans _ s1 s2) s3

/-! ### Counter to word -/

inductive FCSt where
  | fwd | carry (c : Option Bool) | done
  deriving DecidableEq

instance : Fintype FCSt :=
  ⟨{.fwd, .carry none, .carry (some false), .carry (some true), .done}, by
    intro x; rcases x with _ | (_ | ⟨_ | _⟩) | _ <;> simp⟩

/-- Run to the end of the bits, then shift them one cell left onto the separator. -/
abbrev fromCtrMachine : FMachine 1 a where
  S := FCSt
  start := .fwd
  δ s syms := match s with
    | .fwd => if syms 0 = blank then some (.carry none, fun _ => (syms 0, .left))
        else some (.fwd, fun _ => (syms 0, .right))
    | .carry c => if syms 0 = separator then some (.done, fun _ => (sym c, .stay))
        else some (.carry (some (decide (syms 0 = bitSymbol true))), fun _ => (sym c, .left))
    | .done => none

theorem fc_fwd (f : ℤ → Fin (a + 4)) : ∀ (n : ℕ) (h : ℤ), (∀ k : ℕ, k < n → f (h + k) ≠ blank) →
    f (h + n) = blank →
    (fromCtrMachine (a := a)).frun (n + 1) ⟨.fwd, one h f⟩ = some ⟨.carry none, one (h + n - 1) f⟩
  | 0, h, _, hb => by
    simp only [Nat.cast_zero, add_zero] at hb
    rw [FMachine.frun_one, step_one fromCtrMachine (s' := .carry none) .left (by simp [hb])]
    simp [Move.offset]; rfl
  | n + 1, h, hnb, hb => by
    have h0 : f h ≠ blank := by simpa using hnb 0 (by omega)
    have ih := fc_fwd f n (h + 1) (fun k hk => by
      have := hnb (k + 1) (by omega); push_cast at this; rwa [show h + 1 + k = h + (k + 1) by ring])
      (by push_cast at hb; rwa [show h + 1 + n = h + (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_one fromCtrMachine (s' := .fwd) .right (by simp [h0]))) ?_
    convert ih using 4
    · simp [Move.offset]
    · push_cast; ring

/-- The tape after carrying `n` bits one cell left onto the separator at `h - n`. -/
def shiftLeft (f : ℤ → Fin (a + 4)) (h : ℤ) (n : ℕ) (x : Fin (a + 4)) : ℤ → Fin (a + 4) :=
  fun j => if h - n ≤ j ∧ j < h then f (j + 1) else if j = h then x else f j

theorem fc_carry : ∀ (n : ℕ) (c : Option Bool) (f : ℤ → Fin (a + 4)) (h : ℤ),
    (∀ k : ℕ, k < n → ∃ b, f (h - k) = bitSymbol b) → f (h - n) = separator →
    (fromCtrMachine (a := a)).frun (n + 1) ⟨.carry c, one h f⟩ =
      some ⟨.done, one (h - n) (shiftLeft f h n (sym c))⟩
  | 0, c, f, h, _, hs => by
    simp only [Nat.cast_zero, sub_zero] at hs ⊢
    rw [FMachine.frun_one, step_write fromCtrMachine (s' := .done) (sym c) .stay (by simp [hs])]
    congr 3
    · simp [Move.offset]
    · funext j; simp only [shiftLeft, Function.update_apply, Nat.cast_zero, sub_zero]
      split_ifs <;> first | rfl | omega
  | n + 1, c, f, h, hb, hs => by
    obtain ⟨x, hx⟩ := hb 0 (by omega)
    simp only [Nat.cast_zero, sub_zero] at hx
    have ih := fc_carry n (some x) (Function.update f h (sym c)) (h - 1)
      (fun k hk => by
        obtain ⟨b, hb'⟩ := hb (k + 1) (by omega)
        refine ⟨b, ?_⟩
        rw [Function.update_of_ne (by omega)]; push_cast at hb'; rwa [show h - 1 - k = h - (k + 1) by ring])
      (by rw [Function.update_of_ne (by omega)]; push_cast at hs; rwa [show h - 1 - n = h - (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_write fromCtrMachine (s' := .carry (some x)) (sym c) .left (by
        simp [hx, bit_ne_sep, decide_bit]))) ?_
    convert ih using 4
    · simp [Move.offset]; ring
    · push_cast; ring
    · funext j; simp only [shiftLeft, Function.update_apply, sym_some]
      push_cast
      split_ifs <;> first | rfl | (exfalso; omega) | (subst_vars; simp [hx])

theorem fc_halt (v : Tapes 1 a) : (fromCtrMachine (a := a)).fstep ⟨.done, v⟩ = none := halt_one _ (fun _ => rfl)

theorem shiftLeft_ctr (bs : List Bool) :
    shiftLeft (ctr (a := a) bs) bs.length bs.length (sym none) = wtp bs := by
  funext j
  rw [wtp_eq]
  simp only [shiftLeft, ctr, ctr.wordAt', sym_none, sub_self]
  split_ifs with hin hlen hzero
  · omega
  · rw [add_sub_cancel_right]
    simp only [wordTape, ite_eq_left_of_eq_true _ _ (eq_true hin.1)]
    rw [List.getElem?_append_left (by simp; omega)]
  · subst_vars; simp [wordTape]
  · omega
  · simp only [wordTape]
    by_cases hj : 0 ≤ j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true hj),
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false hj)]

/-- Counter tape to word tape. -/
noncomputable def fromCtrProg : Program 1 (Fintype.card FCSt) a := (fromCtrMachine (a := a)).toProgram (by omega)

theorem fromCtrProg_hoare (bs : List Bool) :
    HoareTime (fromCtrProg (a := a)) (· = one 1 (ctr bs)) (· = one 0 (wtp bs)) (2 * bs.length + 2) := by
  apply FMachine.hoare
  intro v hv; subst hv
  have s1 := fc_fwd (ctr (a := a) bs) bs.length 1
    (fun k hk => by
      simp only [ctr, ctr.wordAt', wordTape]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      rw [show ((1 : ℤ) + k - 1).toNat = k by omega, List.getElem?_map, List.getElem?_eq_getElem hk]
      simp [bitSymbol_ne_blank])
    (by
      simp only [ctr, ctr.wordAt', wordTape]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      rw [show ((1 : ℤ) + bs.length - 1).toNat = bs.length by omega, List.getElem?_eq_none (by simp)]; rfl)
  have s2 := fc_carry bs.length none (ctr (a := a) bs) ((1 : ℤ) + bs.length - 1)
    (fun k hk => ⟨bs[bs.length - 1 - k], by
      simp only [ctr, ctr.wordAt', wordTape]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      rw [show ((1 : ℤ) + bs.length - 1 - k - 1).toNat = bs.length - 1 - k by omega, List.getElem?_map,
        List.getElem?_eq_getElem (by omega)]; rfl⟩)
    (by simp only [ctr]; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))])
  rw [show (1 : ℤ) + bs.length - 1 = bs.length by ring, shiftLeft_ctr, sub_self] at s2
  refine ⟨bs.length + 1 + (bs.length + 1), _, by omega, FMachine.frun_trans _ s1 ?_, fc_halt _, rfl⟩
  rw [show (1 : ℤ) + bs.length - 1 = bs.length by ring]; exact s2

end IntegerMultBounds.Schoenhage
