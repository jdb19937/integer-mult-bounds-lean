module

public import IntegerMultBounds.Schoenhage.Words

/-! A generic streaming primitive over word tapes. Tape `0` is the driver,
tapes `1 … r` are further inputs and tape `r + 1` is the output. For each
bit of the driver's current word, a finite rule reads that bit and the
current bit of every other input (or the information that its word has
ended), updates its state and emits at most one symbol; then the other
inputs skip the rest of their words, the rule's final flush is emitted, and
all inputs step past their separators. In extend mode the first symbol
overwrites the output's last separator, so the output continues the last
word. This file gives the rule language, the abstract output and time (`output`, `time`) and
the word-tape effect (`StreamPre`, `streamSem`); `Host/WordStream` implements it on host stacks.
The multitape machine and its raw run are retired (restore from 3ce5bd58). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

namespace Strm

variable {a r : ℕ}

/-- The bit on a cell, if any. -/
def decode (x : Fin (a + 4)) : Option Bool :=
  if x = bitSymbol true then some true else if x = bitSymbol false then some false else none

@[simp] theorem decode_bit (b : Bool) : decode (a := a) (bitSymbol b) = some b := by
  cases b <;> simp [decode, bitSymbol, Fin.ext_iff]

@[simp] theorem decode_sep : decode (a := a) separator = none := by
  simp [decode, bitSymbol, separator, Fin.ext_iff]

theorem bit_ne_sep (b : Bool) : bitSymbol (a := a) b ≠ separator := by
  cases b <;> simp [bitSymbol, separator, Fin.ext_iff]

/-- A streaming rule with a finite state type. -/
structure Rule (r : ℕ) where
  Q : Type
  [fin : Fintype Q]
  [dec : DecidableEq Q]
  q0 : Q
  step : Q → Bool → (Fin r → Option Bool) → Q × Option (Option Bool) × (Fin r → Bool)
  flush : Q → List (Option Bool)
  B : ℕ
  hB : ∀ q, (flush q).length ≤ B

attribute [instance] Rule.fin Rule.dec

/-- The driver tape. -/
def drv : Fin (r + 2) := ⟨0, by omega⟩
/-- The other input tapes. -/
def oth (j : Fin r) : Fin (r + 2) := ⟨j.val + 1, by omega⟩
/-- The output tape. -/
def out : Fin (r + 2) := ⟨r + 1, by omega⟩

/-- Whether tape `i` advances under the advance flags `adv`. -/
def advOf (adv : Fin r → Bool) (i : Fin (r + 2)) : Bool :=
  if h : 0 < i.val ∧ i.val ≤ r then adv ⟨i.val - 1, by omega⟩ else false

theorem drv_ne_out : (drv : Fin (r + 2)) ≠ out := by simp [drv, out, Fin.ext_iff]
theorem oth_ne_out (j : Fin r) : oth j ≠ out := by simp [oth, out, Fin.ext_iff]; omega
theorem oth_ne_drv (j : Fin r) : oth j ≠ drv := by simp [oth, drv, Fin.ext_iff]

theorem advOf_oth (adv : Fin r → Bool) (j : Fin r) : advOf adv (oth j) = adv j := by
  unfold advOf
  have h : 0 < (oth j).val ∧ (oth j).val ≤ r := by simp [oth]
  simp only [h]
  congr 1

/-- Every tape is the driver, another input or the output. -/
theorem cases_tape (i : Fin (r + 2)) : i = drv ∨ (∃ j, i = oth j) ∨ i = out := by
  rcases i with ⟨i, hi⟩
  rcases Nat.eq_zero_or_pos i with rfl | h
  · left; rfl
  · by_cases h' : i = r + 1
    · right; right; simp [out, h']
    · right; left; exact ⟨⟨i - 1, by omega⟩, by simp [oth, Fin.ext_iff]; omega⟩

/-! ### Abstract semantics -/

/-- Run the rule over the driver bits; the other inputs are consumed in step. -/
def go (R : Rule r) : R.Q → List Bool → (Fin r → List Bool) →
    R.Q × List (Option Bool) × (Fin r → List Bool)
  | q, [], ws => (q, [], ws)
  | q, b :: bs, ws =>
    let p := R.step q b (fun j => (ws j).head?)
    let rest := go R p.1 bs (fun j => if p.2.2 j then (ws j).tail else ws j)
    (rest.1, p.2.1.toList ++ rest.2.1, rest.2.2)

/-- All emitted symbols, flush included. -/
def output (R : Rule r) (w : List Bool) (ws : Fin r → List Bool) : List (Option Bool) :=
  (go R R.q0 w ws).2.1 ++ R.flush (go R R.q0 w ws).1

/-- The longest unread remainder of the other inputs. -/
def rest (R : Rule r) (w : List Bool) (ws : Fin r → List Bool) : ℕ :=
  Finset.univ.sup fun j => ((go R R.q0 w ws).2.2 j).length

/-- Exact number of transitions. -/
def time (R : Rule r) (w : List Bool) (ws : Fin r → List Bool) : ℕ :=
  w.length + rest R w ws + (R.flush (go R R.q0 w ws).1).length + 5

theorem go_rest_le (R : Rule r) : ∀ (q : R.Q) (w : List Bool) (ws : Fin r → List Bool) (j : Fin r),
    ((go R q w ws).2.2 j).length ≤ (ws j).length
  | q, [], ws, j => by simp [go]
  | q, b :: bs, ws, j => by
    simp only [go]
    refine (go_rest_le R _ bs _ j).trans ?_
    split_ifs <;> simp

theorem time_le (R : Rule r) (w : List Bool) (ws : Fin r → List Bool) (L : ℕ)
    (hL : ∀ j, (ws j).length ≤ L) : time R w ws ≤ w.length + L + R.B + 5 := by
  unfold time rest
  have h1 : (Finset.univ.sup fun j => ((go R R.q0 w ws).2.2 j).length) ≤ L :=
    Finset.sup_le fun j _ => (go_rest_le R _ w ws j).trans (hL j)
  have h2 := R.hB (go R R.q0 w ws).1
  omega

end Strm

/-! ### Word-tape effects of a streaming primitive -/

section Spec

open Strm

variable {a r : ℕ}

namespace WTape

/-- The current word (empty at the end). -/
def cur (T : WTape) : List Bool := T.right.headD []

/-- Step past the current word. -/
def next (T : WTape) : WTape := ⟨T.cur :: T.left, T.right.tail⟩

/-- Append words at the end, optionally continuing the last word. -/
def put (T : WTape) (ext : Bool) (vs : List (List Bool)) : WTape :=
  match ext, T.left, vs with
  | true, u :: L, v :: vs' => ⟨vs'.reverse ++ (u ++ v) :: L, []⟩
  | _, L, vs => ⟨vs.reverse ++ L, []⟩

end WTape

/-- The precondition of a streaming primitive. -/
def StreamPre (R : Rule r) (ext : Bool) (σ : Fin (r + 2) → WTape) : Prop :=
  (σ drv).right ≠ [] ∧ (∀ j, (σ (oth j)).right ≠ []) ∧ (σ out).right = [] ∧
  ∃ vs, output R (σ drv).cur (fun j => (σ (oth j)).cur) = syms vs ∧
    (ext = true → (σ out).left ≠ [] ∧ vs ≠ [])

/-- The effect of a streaming primitive. -/
def streamSem (R : Rule r) (ext : Bool) (σ : Fin (r + 2) → WTape) : Fin (r + 2) → WTape :=
  fun i => if i = out then
    (σ out).put ext (parse (output R (σ drv).cur (fun j => (σ (oth j)).cur)))
    else (σ i).next

theorem exists_cons {l : List (List Bool)} (h : l ≠ []) : ∃ w R, l = w :: R := by
  cases l with
  | nil => exact absurd rfl h
  | cons w R => exact ⟨w, R, rfl⟩

end Spec

end IntegerMultBounds.Schoenhage
