module

public import IntegerMultBounds.Schoenhage.Seal
public import IntegerMultBounds.Machine.OrderedSelect

/-! The boundary between word tapes and blank-separated record tapes. A word
tape holds separator-terminated words from cell zero; a record tape holds the
same bits with a blank after each record. The one-tape machine `desepProg`
scans to the end of a word tape and, walking back, turns every separator into
a blank, ending with the head at cell zero (`desepProg_hoare`). The other
direction packs records with `RecordPack`. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine
open OrderedSelect (flat flat_cons inTape)

variable {a : ℕ}

/-! ### Words and records as symbol lists -/

/-- The symbols of a word list. -/
def cellsOf (ws : List (List Bool)) : List (Fin (a + 4)) := (syms ws).map sym

/-- The records of a word list. -/
def recsOf (ws : List (List Bool)) : List (List (Fin (a + 4))) := ws.map (List.map bitSymbol)

/-- Separator-terminated records. -/
def flatSep (recs : List (List (Fin (a + 4)))) : List (Fin (a + 4)) := (recs.map (· ++ [separator])).flatten

theorem cellsOf_cons (w : List Bool) (ws : List (List Bool)) :
    cellsOf (a := a) (w :: ws) = w.map bitSymbol ++ separator :: cellsOf ws := by
  simp [cellsOf, syms_cons, sym, Function.comp_def]

/-- Separators to blanks. -/
def unsep (x : Fin (a + 4)) : Fin (a + 4) := if x = separator then blank else x

theorem flat_recsOf (ws : List (List Bool)) : (cellsOf (a := a) ws).map unsep = flat (recsOf ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hb : (w.map (bitSymbol (a := a))).map unsep = w.map bitSymbol := by
      rw [List.map_map]; congr 1; funext b; simp [unsep, bitSymbol_ne_separator]
    rw [cellsOf_cons, List.map_append, List.map_cons, ih, hb]
    simp only [recsOf, List.map_cons, flat_cons, unsep]
    rfl

theorem cellsOf_nonblank (ws : List (List Bool)) : ∀ x ∈ cellsOf (a := a) ws, x ≠ blank := by
  intro x hx
  simp only [cellsOf, List.mem_map] at hx
  obtain ⟨o, -, rfl⟩ := hx
  exact sym_ne_blank o

theorem length_cellsOf (ws : List (List Bool)) : (cellsOf (a := a) ws).length = clen ws := by
  simp [cellsOf, length_syms]

theorem wtape_eq (ws : List (List Bool)) : (⟨[], ws⟩ : WTape).tape (a := a) = wordTape (cellsOf ws) := by
  funext j; rw [WTape.tape_eq]; simp [wordTape, cellsOf, WTape.words]

theorem putWord_zero (L : List (Fin (a + 4))) : putWord (fun _ => blank) 0 L = wordTape L := by
  funext j; rw [putWord_blank, sub_zero]

/-! ### Scanning and walking back -/

inductive RelSt where
  | fwd | back | done
  deriving DecidableEq

instance : Fintype RelSt := ⟨{.fwd, .back, .done}, by intro x; cases x <;> simp⟩

/-- Scan right to the first blank; walking back, apply `ρ` to every cell. -/
abbrev relMachine (ρ : Fin (a + 4) → Fin (a + 4)) : FMachine 1 a where
  S := RelSt
  start := .fwd
  δ s syms := match s with
    | .fwd => if syms 0 = blank then some (.back, fun _ => (syms 0, .left))
        else some (.fwd, fun _ => (syms 0, .right))
    | .back => if syms 0 = blank then some (.done, fun _ => (syms 0, .right))
        else some (.back, fun _ => (ρ (syms 0), .left))
    | .done => none

theorem rel_fwd (ρ : Fin (a + 4) → Fin (a + 4)) (f : ℤ → Fin (a + 4)) :
    ∀ (n : ℕ) (h : ℤ), (∀ c : ℕ, c < n → f (h + c) ≠ blank) → f (h + n) = blank →
      (relMachine ρ).frun (n + 1) ⟨.fwd, one h f⟩ = some ⟨.back, one (h + n - 1) f⟩
  | 0, h, _, hb => by
    simp only [Nat.cast_zero, add_zero] at hb ⊢
    rw [FMachine.frun_one, step_one (relMachine ρ) (s' := .back) .left (by simp [hb])]
    simp [Move.offset]; ring_nf
  | n + 1, h, hnb, hb => by
    have h0 : f h ≠ blank := by simpa using hnb 0 (by omega)
    have ih := rel_fwd ρ f n (h + 1) (fun c hc => by
      have := hnb (c + 1) (by omega); push_cast at this; rwa [show h + 1 + c = h + (c + 1) by ring])
      (by push_cast at hb; rwa [show h + 1 + n = h + (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_one (relMachine ρ) (s' := .fwd) .right (by simp [h0]))) ?_
    convert ih using 4
    · simp [Move.offset]
    · push_cast; ring

/-- The cells of `f` in `[lo, hi]` relabelled by `ρ`. -/
def relOn (ρ : Fin (a + 4) → Fin (a + 4)) (f : ℤ → Fin (a + 4)) (lo hi : ℤ) : ℤ → Fin (a + 4) :=
  fun j => if lo ≤ j ∧ j ≤ hi then ρ (f j) else f j

theorem rel_back (ρ : Fin (a + 4) → Fin (a + 4)) :
    ∀ (n : ℕ) (f : ℤ → Fin (a + 4)) (h : ℤ), (∀ c : ℕ, c < n → f (h - c) ≠ blank) → f (h - n) = blank →
      (relMachine ρ).frun (n + 1) ⟨.back, one h f⟩ = some ⟨.done, one (h - n + 1) (relOn ρ f (h - n + 1) h)⟩
  | 0, f, h, _, hb => by
    simp only [Nat.cast_zero, sub_zero] at hb ⊢
    rw [FMachine.frun_one, step_one (relMachine ρ) (s' := .done) .right (by simp [hb])]
    congr 3
    funext j; simp only [relOn]; split_ifs with hj
    · omega
    · rfl
  | n + 1, f, h, hnb, hb => by
    have h0 : f h ≠ blank := by simpa using hnb 0 (by omega)
    have ih := rel_back ρ n (Function.update f h (ρ (f h))) (h - 1)
      (fun c hc => by
        rw [Function.update_of_ne (by omega)]
        have := hnb (c + 1) (by omega); push_cast at this; rwa [show h - 1 - c = h - (c + 1) by ring])
      (by rw [Function.update_of_ne (by omega)]; push_cast at hb; rwa [show h - 1 - n = h - (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_write (relMachine ρ) (s' := .back) (ρ (f h)) .left (by simp [h0]))) ?_
    convert ih using 4
    · simp [Move.offset]; ring
    · push_cast; ring
    · funext j
      simp only [relOn, Function.update_apply]
      by_cases hj : j = h
      · subst hj; simp
      · simp only [hj, ite_false]
        split_ifs <;> first | rfl | omega

theorem relOn_wordTape (ρ : Fin (a + 4) → Fin (a + 4)) (L : List (Fin (a + 4))) :
    relOn ρ (wordTape L) 0 (L.length - 1) = wordTape (L.map ρ) := by
  funext j
  simp only [relOn, wordTape]
  by_cases h0 : 0 ≤ j
  · by_cases h1 : j ≤ L.length - 1
    · have hl : j.toNat < L.length := by omega
      simp [h0, h1, List.getElem?_eq_getElem hl, List.getElem?_map]
    · have hl : L.length ≤ j.toNat := by omega
      simp [h0, h1, List.getElem?_eq_none hl]
  · simp [h0]

theorem rel_run (ρ : Fin (a + 4) → Fin (a + 4)) (L : List (Fin (a + 4))) (hL : ∀ x ∈ L, x ≠ blank) :
    (relMachine ρ).frun (L.length + 1 + (L.length + 1)) ⟨.fwd, one 0 (wordTape L)⟩ =
      some ⟨.done, one 0 (wordTape (L.map ρ))⟩ := by
  have hget : ∀ c : ℕ, c < L.length → wordTape L c ≠ blank := fun c hc => by
    have h0 : (0 : ℤ) ≤ c := by omega
    simp only [wordTape, h0, ↓reduceIte]; simp [List.getElem?_eq_getElem hc]
    exact hL _ (List.getElem_mem hc)
  have hend : wordTape L L.length = blank := by simp [wordTape]
  have s1 := rel_fwd ρ (wordTape L) L.length 0 (fun c hc => by simpa using hget c hc) (by simpa using hend)
  simp only [zero_add] at s1
  have s2 := rel_back ρ L.length (wordTape L) (L.length - 1)
    (fun c hc => by rw [show (L.length : ℤ) - 1 - c = ((L.length - 1 - c : ℕ) : ℤ) by omega]; exact hget _ (by omega))
    (by rw [show (L.length : ℤ) - 1 - L.length = -1 by ring]; simp [wordTape])
  rw [FMachine.frun_trans _ s1 s2]
  congr 3
  · ring
  · rw [show (L.length : ℤ) - 1 - L.length + 1 = 0 by ring, relOn_wordTape]

theorem rel_halt (ρ : Fin (a + 4) → Fin (a + 4)) (v : Tapes 1 a) :
    (relMachine ρ).fstep ⟨.done, v⟩ = none :=
  halt_one _ (fun _ => rfl)

/-- Separators to blanks, ending at cell zero. -/
noncomputable def desepProg : Program 1 (Fintype.card RelSt) a :=
  (relMachine (a := a) unsep).toProgram (by omega)

theorem desepProg_hoare (ws : List (List Bool)) :
    HoareTime (desepProg (a := a)) (· = one 0 (⟨[], ws⟩ : WTape).tape) (· = one 0 (inTape (recsOf ws)))
      (2 * clen ws + 2) := by
  apply FMachine.hoare
  intro v hv; subst hv
  refine ⟨(cellsOf (a := a) ws).length + 1 + ((cellsOf (a := a) ws).length + 1),
    ⟨.done, one 0 (inTape (recsOf ws))⟩, by rw [length_cellsOf]; omega, ?_, rel_halt _ _, rfl⟩
  rw [wtape_eq, rel_run unsep _ (cellsOf_nonblank ws), flat_recsOf, inTape, putWord_zero]

end IntegerMultBounds.Schoenhage
