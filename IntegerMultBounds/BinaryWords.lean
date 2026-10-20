module

public import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

/-! The fixed alphabet `Fin (a + 4)` (blank, the two bits, the separator), binary words read most
significant bit first, and the logarithm `lg` of the time bound. -/

@[expose] public section

namespace IntegerMultBounds

variable {a : ℕ}

def blank : Fin (a + 4) := ⟨0, by omega⟩
def bitSymbol (b : Bool) : Fin (a + 4) := ⟨if b then 2 else 1, by split <;> omega⟩
def separator : Fin (a + 4) := ⟨3, by omega⟩

/-- Most-significant bit first, including any leading zeroes. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) * 2 ^ bs.length + binaryValue bs

theorem binaryValue_lt (bs : List Bool) : binaryValue bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp only [binaryValue, List.length_cons, Nat.pow_succ,
      Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.one_mul, Nat.zero_add] <;> omega

theorem product_fits {x y : List Bool} {n : ℕ}
    (hx : x.length = n) (hy : y.length = n) :
    binaryValue x * binaryValue y < 2 ^ (2 * n) := by
  have hx' := binaryValue_lt x
  have hy' := binaryValue_lt y
  rw [hx] at hx'
  rw [hy] at hy'
  calc
    _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_lt_of_lt hx' hy'
    _ = _ := by rw [← Nat.pow_add, Nat.two_mul]

def lg (n : ℕ) : ℕ := max (Nat.clog 2 n) 1

end IntegerMultBounds
