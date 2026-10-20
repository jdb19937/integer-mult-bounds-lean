module

public import IntegerMultBounds.Machine.WordTape

/-! Tapes holding lists of binary words. A word is written as its bits
followed by one separator; the words of a tape are laid out from cell zero,
blank everywhere else. The abstract tape is a zipper: the words left of the
head (nearest first) and the words from the head on. The head sits on the
first cell of the first right word, or on the blank after the last word. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a : ℕ}

/-- A tape symbol: a bit, or the separator (`none`). -/
def sym : Option Bool → Fin (a + 4)
  | none => separator
  | some b => bitSymbol b

/-- The symbols of a word list. -/
def syms (ws : List (List Bool)) : List (Option Bool) := ws.flatMap fun w => w.map some ++ [none]

@[simp] theorem syms_nil : syms [] = [] := rfl

theorem syms_cons (w : List Bool) (ws : List (List Bool)) :
    syms (w :: ws) = w.map some ++ [none] ++ syms ws := by simp [syms]

theorem syms_append (ws vs : List (List Bool)) : syms (ws ++ vs) = syms ws ++ syms vs := by
  simp [syms]

/-- Split a symbol list into its separator-terminated words. -/
def parseAux : List Bool → List (Option Bool) → List (List Bool)
  | _, [] => []
  | cur, none :: os => cur.reverse :: parseAux [] os
  | cur, some b :: os => parseAux (b :: cur) os

/-- The words of a symbol list. -/
def parse (os : List (Option Bool)) : List (List Bool) := parseAux [] os

theorem parseAux_syms (cur w : List Bool) (ws : List (List Bool)) :
    parseAux cur (w.map some ++ [none] ++ syms ws) = (cur.reverse ++ w) :: parseAux [] (syms ws) := by
  induction w generalizing cur with
  | nil => simp [parseAux]
  | cons b w ih =>
    have := ih (b :: cur)
    simp only [List.map_cons, List.cons_append, parseAux]
    rw [this]; simp

theorem parseAux_some_append (cur w : List Bool) (os : List (Option Bool)) :
    parseAux cur (w.map some ++ os) = parseAux (w.reverse ++ cur) os := by
  induction w generalizing cur with
  | nil => rfl
  | cons b w ih => simp [parseAux, ih]

@[simp] theorem parse_nil : parse [] = [] := rfl

@[simp] theorem parse_some_sep (w : List Bool) (os : List (Option Bool)) :
    parse (w.map some ++ none :: os) = w :: parse os := by
  simp [parse, parseAux_some_append, parseAux]

@[simp] theorem parse_replicate_sep (n : ℕ) (b : Bool) (os : List (Option Bool)) :
    parse (List.replicate n (some b) ++ none :: os) = List.replicate n b :: parse os := by
  have := parse_some_sep (List.replicate n b) os
  simpa [List.map_replicate] using this

@[simp] theorem parse_drop_sep (k : ℕ) (w : List Bool) (os : List (Option Bool)) :
    parse ((w.map some).drop k ++ none :: os) = w.drop k :: parse os := by
  rw [← List.map_drop]; exact parse_some_sep _ os

@[simp] theorem parse_sep (os : List (Option Bool)) : parse (none :: os) = [] :: parse os := rfl

@[simp] theorem parse_bit_sep (b : Bool) (os : List (Option Bool)) :
    parse (some b :: none :: os) = [b] :: parse os := rfl

@[simp] theorem parse_syms (ws : List (List Bool)) : parse (syms ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    unfold parse at ih ⊢
    rw [syms_cons, parseAux_syms, ih]; simp

/-- Total cell length of a word list. -/
def clen (ws : List (List Bool)) : ℕ := (ws.map fun w => w.length + 1).sum

@[simp] theorem clen_nil : clen [] = 0 := rfl

@[simp] theorem clen_cons (w : List Bool) (ws : List (List Bool)) :
    clen (w :: ws) = w.length + 1 + clen ws := by simp [clen]

theorem clen_append (ws vs : List (List Bool)) : clen (ws ++ vs) = clen ws + clen vs := by
  simp [clen]

theorem clen_reverse (ws : List (List Bool)) : clen ws.reverse = clen ws := by
  simp [clen, List.sum_reverse]

theorem length_syms (ws : List (List Bool)) : (syms ws).length = clen ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [syms_cons, ih]; ring

/-- The cells of a word list. -/
def cells (ws : List (List Bool)) : List (Fin (a + 4)) := (syms ws).map sym

theorem length_cells (ws : List (List Bool)) : (cells (a := a) ws).length = clen ws := by
  simp [cells, length_syms]

/-- An abstract tape of words with the head at a word boundary. -/
structure WTape where
  left : List (List Bool)
  right : List (List Bool)

namespace WTape

/-- All words in tape order. -/
def words (T : WTape) : List (List Bool) := T.left.reverse ++ T.right

end WTape

end IntegerMultBounds.Schoenhage
