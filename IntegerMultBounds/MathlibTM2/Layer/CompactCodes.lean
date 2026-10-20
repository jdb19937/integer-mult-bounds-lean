module

public import IntegerMultBounds.MathlibTM2.Layer.CompactRot

/-!
# Wrap-class automata for rotations by computed offsets

A code automaton reads one bit of each of `k` registers per step, register `0` holding the
rotated value. An offset rule `R : ORule k` computes one offset bit per step from the column and
one bit of auxiliary state (`ORule.ob`); `offv R L a vals` is the offset read over `L` bits from
auxiliary state `a`, with `testBit_offv` describing its bits.

`carryO R` and `borrowO R` track the carry of `vals 0 + off` and the borrow of `vals 0 - off`;
their states pair the carry or borrow with the auxiliary bit (`enc2`). `inC` and `outC` combine
them into the input and output wrap classes of a rotation (`inC_eval`, `outC_eval`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactGadget

open IntegerMultBounds.MathlibTM2.Host

/-- An offset rule: one offset bit and the next auxiliary bit from the auxiliary bit and a column. -/
structure ORule (k : ℕ) where
  ob : Bool → (Fin k → Bool) → Bool × Bool

/-- The offset bits of a rule over `L` columns of `vals`, from auxiliary bit `a`. -/
def offv {k : ℕ} (R : ORule k) : ℕ → Bool → (Fin k → ℕ) → ℕ
  | 0, _, _ => 0
  | L + 1, a, vals => (R.ob a fun r => (vals r).testBit 0).1.toNat +
      2 * offv R L (R.ob a fun r => (vals r).testBit 0).2 fun r => vals r / 2

lemma offv_lt {k : ℕ} (R : ORule k) : ∀ (L : ℕ) (a : Bool) (vals : Fin k → ℕ),
    offv R L a vals < 2 ^ L
  | 0, _, _ => by simp [offv]
  | L + 1, a, vals => by
    have h := offv_lt R L (R.ob a fun r => (vals r).testBit 0).2 fun r => vals r / 2
    have h1 := Bool.toNat_le (R.ob a fun r => (vals r).testBit 0).1
    rw [offv, pow_succ]
    omega

/-- The auxiliary bit before column `q`. -/
def auxAt {k : ℕ} (R : ORule k) : ℕ → Bool → (Fin k → ℕ) → Bool
  | 0, a, _ => a
  | q + 1, a, vals => auxAt R q (R.ob a fun r => (vals r).testBit 0).2 fun r => vals r / 2

/-- **The bits of the offset.** Bit `q < L` is the offset bit of column `q` with the auxiliary
bit reached there. -/
theorem testBit_offv {k : ℕ} (R : ORule k) : ∀ (L : ℕ) (a : Bool) (vals : Fin k → ℕ) (q : ℕ),
    (offv R L a vals).testBit q =
      (decide (q < L) && (R.ob (auxAt R q a vals) fun r => (vals r).testBit q).1)
  | 0, a, vals, q => by simp [offv]
  | L + 1, a, vals, 0 => by
    rw [offv, Nat.testBit_zero]
    simp only [auxAt, Nat.zero_lt_succ, decide_true, Bool.true_and]
    cases (R.ob a fun r => (vals r).testBit 0).1 <;> simp [Nat.add_mod]
  | L + 1, a, vals, q + 1 => by
    rw [offv, Nat.testBit_succ, show ((R.ob a fun r => (vals r).testBit 0).1.toNat +
      2 * offv R L (R.ob a fun r => (vals r).testBit 0).2 fun r => vals r / 2) / 2 =
      offv R L (R.ob a fun r => (vals r).testBit 0).2 (fun r => vals r / 2) by
        have := Bool.toNat_le (R.ob a fun r => (vals r).testBit 0).1
        omega, testBit_offv R L]
    simp only [auxAt, Nat.testBit_div_two]
    congr 1
    simp

/-! ### State encoding -/

/-- The class of a carry or borrow bit. -/
def rotCls (x : Bool) : Fin 2 := if x then 1 else 0

lemma rotCls_inj {x y : Bool} : rotCls x = rotCls y ↔ x = y := by
  cases x <;> cases y <;> decide

/-- A pair of bits as a state symbol. -/
def enc2 {A : ℕ} (c a : Bool) : Fin (A + 4) := ⟨2 * c.toNat + a.toNat, by cases c <;> cases a <;> simp⟩

/-- The pair of bits of a state symbol. -/
def dec2 {A : ℕ} (x : Fin (A + 4)) : Bool × Bool := (x.val.testBit 1, x.val.testBit 0)

lemma dec2_enc2 {A : ℕ} (c a : Bool) : dec2 (enc2 (A := A) c a) = (c, a) := by
  cases c <;> cases a <;> simp [dec2, enc2, Nat.testBit_zero, Nat.testBit_succ]

variable {A k : ℕ} [NeZero k]

/-- The carry automaton of `vals 0 + off`. -/
def carryO (A : ℕ) (R : ORule k) : CAuto A k 2 where
  init := enc2 false false
  step s col :=
    let o := R.ob (dec2 s).2 col
    enc2 ((col 0 && o.1) || ((dec2 s).1 && (col 0 || o.1))) o.2
  out s := rotCls (dec2 s).1

/-- The borrow automaton of `vals 0 - off`. -/
def borrowO (A : ℕ) (R : ORule k) : CAuto A k 2 where
  init := enc2 false false
  step s col :=
    let o := R.ob (dec2 s).2 col
    enc2 ((!col 0 && (o.1 || (dec2 s).1)) || (o.1 && (dec2 s).1)) o.2
  out s := rotCls (dec2 s).1

lemma carryO_run (R : ORule k) : ∀ (L : ℕ) (cy a : Bool) (vals : Fin k → ℕ),
    (dec2 ((carryO A R).run L (enc2 cy a) vals)).1 =
      decide (2 ^ L ≤ vals 0 % 2 ^ L + offv R L a vals + cy.toNat)
  | 0, cy, a, vals => by cases cy <;> simp [CAuto.run, offv, dec2_enc2, Nat.mod_one]
  | L + 1, cy, a, vals => by
    rw [CAuto.run]
    have hstep : (carryO A R).step (enc2 cy a) (fun r => (vals r).testBit 0) =
        enc2 (((vals 0).testBit 0 && (R.ob a fun r => (vals r).testBit 0).1) ||
          (cy && ((vals 0).testBit 0 || (R.ob a fun r => (vals r).testBit 0).1)))
          (R.ob a fun r => (vals r).testBit 0).2 := by
      simp only [carryO, dec2_enc2]
    rw [hstep, carryO_run R L, offv]
    have hx : vals 0 % 2 ^ (L + 1) = vals 0 % 2 + 2 * (vals 0 / 2 % 2 ^ L) := by
      rw [pow_succ', Nat.mod_mul]
    generalize (R.ob a fun r => (vals r).testBit 0) = ob0
    generalize offv R L ob0.2 (fun r => vals r / 2) = O
    obtain ⟨o, a'⟩ := ob0
    simp only
    rw [hx, Nat.testBit_zero]
    generalize vals 0 / 2 % 2 ^ L = y
    rw [pow_succ']
    rcases Nat.mod_two_eq_zero_or_one (vals 0) with h | h <;> rw [h] <;>
      cases o <;> cases cy <;> simp <;> omega

lemma borrowO_run (R : ORule k) : ∀ (L : ℕ) (br a : Bool) (vals : Fin k → ℕ),
    (dec2 ((borrowO A R).run L (enc2 br a) vals)).1 =
      decide (vals 0 % 2 ^ L < offv R L a vals + br.toNat)
  | 0, br, a, vals => by cases br <;> simp [CAuto.run, offv, dec2_enc2, Nat.mod_one]
  | L + 1, br, a, vals => by
    rw [CAuto.run]
    have hstep : (borrowO A R).step (enc2 br a) (fun r => (vals r).testBit 0) =
        enc2 ((!(vals 0).testBit 0 && ((R.ob a fun r => (vals r).testBit 0).1 || br)) ||
          ((R.ob a fun r => (vals r).testBit 0).1 && br))
          (R.ob a fun r => (vals r).testBit 0).2 := by
      simp only [borrowO, dec2_enc2]
    rw [hstep, borrowO_run R L, offv]
    have hx : vals 0 % 2 ^ (L + 1) = vals 0 % 2 + 2 * (vals 0 / 2 % 2 ^ L) := by
      rw [pow_succ', Nat.mod_mul]
    generalize (R.ob a fun r => (vals r).testBit 0) = ob0
    generalize offv R L ob0.2 (fun r => vals r / 2) = O
    obtain ⟨o, a'⟩ := ob0
    simp only
    rw [hx, Nat.testBit_zero]
    generalize vals 0 / 2 % 2 ^ L = y
    rcases Nat.mod_two_eq_zero_or_one (vals 0) with h | h <;> rw [h] <;>
      cases o <;> cases br <;> simp <;> omega

/-- The input class automaton of the rotation by `± off`. -/
def inC (A : ℕ) (neg : Bool) (R : ORule k) : CAuto A k 2 := if neg then borrowO A R else carryO A R

/-- The output class automaton. -/
def outC (A : ℕ) (neg : Bool) (R : ORule k) : CAuto A k 2 := if neg then carryO A R else borrowO A R

lemma carryO_eval (R : ORule k) (L : ℕ) (vals : Fin k → ℕ) :
    (carryO A R).eval L vals = rotCls (decide (2 ^ L ≤ vals 0 % 2 ^ L + offv R L false vals)) := by
  show rotCls (dec2 ((carryO A R).run L (enc2 false false) vals)).1 = _
  rw [carryO_run]
  simp

lemma borrowO_eval (R : ORule k) (L : ℕ) (vals : Fin k → ℕ) :
    (borrowO A R).eval L vals = rotCls (decide (vals 0 % 2 ^ L < offv R L false vals)) := by
  show rotCls (dec2 ((borrowO A R).run L (enc2 false false) vals)).1 = _
  rw [borrowO_run]
  simp

/-- **The input class.** -/
theorem inC_eval (neg : Bool) (R : ORule k) (L : ℕ) (vals : Fin k → ℕ) (h0 : vals 0 < 2 ^ L) :
    (inC A neg R).eval L vals = rotCls (wrapIn L neg (offv R L false vals) (vals 0)) := by
  cases neg
  · simp [inC, wrapIn, carryO_eval, Nat.mod_eq_of_lt h0]
  · simp [inC, wrapIn, borrowO_eval, Nat.mod_eq_of_lt h0]

/-- **The output class.** -/
theorem outC_eval (neg : Bool) (R : ORule k) (L : ℕ) (vals : Fin k → ℕ) (h0 : vals 0 < 2 ^ L) :
    (outC A neg R).eval L vals = rotCls (wrapOut L neg (offv R L false vals) (vals 0)) := by
  cases neg
  · simp [outC, wrapOut, borrowO_eval, Nat.mod_eq_of_lt h0]
  · simp [outC, wrapOut, carryO_eval, Nat.mod_eq_of_lt h0]

end IntegerMultBounds.MathlibTM2.Layer.CompactGadget
