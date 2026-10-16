module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-!
# Bit-serial transducers on binary numerals

Pure bit-level facts behind the binary register arithmetic of `Host/BinArith*.lean`. A value `a`
held in width `L` is the bit list `binBits L a` (least significant bit first); on a register it is
`binSyms L a = (binBits L a).map bitSymbol`, least significant bit on top.

**Transducers.** A `BitFn` steps a state bit on one bit of each of two operands and emits an
output bit. Run over two bit lists in parallel from state `s`, `zipOut f s xs ys` is the list of
outputs and `zipFin f s xs ys` the final state.
* `addF` (carry): `zipOut_addF` gives `binBits L (x + y + c)`, `zipFin_addF` the carry out.
* `subF` (borrow): from borrow `false`, `zipOut_subF_binBits` gives `binBits L (x + 2 ^ L - y)`
  (the low `L` bits of `x - y` modulo `2 ^ L`) and `zipFin_subF_binBits` the borrow `x < y`.
* `ltF`, `eqF`: the final state is `x < y`, `x = y` modulo `2 ^ L` (`zipFin_ltF`, `zipFin_eqF`).

**Numerals.** `binSyms_append`, `binSyms_pad` (high zeros), `binSyms_shift` (shift in a bit at
the bottom and drop the top bit), `binSyms_dropLast`, indexing (`getElem_binSyms`,
`getElem_reverse_binSyms`), the high-part recursion `div_two_pow_eq` and the restoring division
step `div_step`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Node


/-- A bit-serial transducer: from the state bit and one bit of each operand, the new state and
the output bit. -/
abbrev BitFn := Bool → Bool → Bool → Bool × Bool

/-- The outputs of `f` run over `xs` and `ys` in parallel from state `s`. -/
def zipOut (f : BitFn) : Bool → List Bool → List Bool → List Bool
  | _, [], _ => []
  | _, _ :: _, [] => []
  | s, p :: xs, q :: ys => (f s p q).2 :: zipOut f (f s p q).1 xs ys

/-- The final state of `f` run over `xs` and `ys` in parallel from state `s`. -/
def zipFin (f : BitFn) : Bool → List Bool → List Bool → Bool
  | s, [], _ => s
  | s, _ :: _, [] => s
  | s, p :: xs, q :: ys => zipFin f (f s p q).1 xs ys

/-- Addition: the state is the carry. -/
def addF : BitFn := fun c p q => (p && q || c && xor p q, xor (xor p q) c)

/-- Subtraction of the second operand: the state is the borrow. -/
def subF : BitFn := fun β p q => (!p && q || !(xor p q) && β, xor (xor p q) β)

/-- Comparison `<`, least significant bit first: the highest differing bit decides. The output
is constantly `false`. -/
def ltF : BitFn := fun s p q => (!p && q || (p == q) && s, false)

/-- Equality. The output is constantly `false`. -/
def eqF : BitFn := fun s p q => (s && (p == q), false)

lemma length_zipOut (f : BitFn) : ∀ (s : Bool) (xs ys : List Bool), xs.length = ys.length →
    (zipOut f s xs ys).length = xs.length
  | _, [], _, _ => rfl
  | _, _ :: _, [], h => by simp at h
  | s, p :: xs, q :: ys, h => by
      simp only [zipOut, List.length_cons]
      rw [length_zipOut f _ xs ys (by simpa using h)]

/-! ### Addition and subtraction -/

lemma add_bits (c : Bool) (x y : ℕ) :
    (x + y + c.toNat).testBit 0 = xor (xor (x.testBit 0) (y.testBit 0)) c ∧
      (x + y + c.toNat) / 2 =
        x / 2 + y / 2 + (x.testBit 0 && y.testBit 0 || c && xor (x.testBit 0) (y.testBit 0)).toNat := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> cases c <;>
    simp [Nat.testBit_zero, hx, hy] <;> omega

/-- The sum bits: only the low `L` bits of `x + y + c` are produced. -/
theorem zipOut_addF (c : Bool) (L x y : ℕ) :
    zipOut addF c (binBits L x) (binBits L y) = binBits L (x + y + c.toNat) := by
  induction L generalizing x y c with
  | zero => rfl
  | succ L ih =>
      obtain ⟨h0, h1⟩ := add_bits c x y
      rw [binBits_succ, binBits_succ, zipOut, ih, binBits_succ, h0, h1]
      rfl

/-- The carry out of the low `L` bits. -/
theorem zipFin_addF (c : Bool) (L x y : ℕ) :
    (zipFin addF c (binBits L x) (binBits L y)).toNat + x / 2 ^ L + y / 2 ^ L =
      (x + y + c.toNat) / 2 ^ L := by
  induction L generalizing x y c with
  | zero => simp [zipFin, binBits]; omega
  | succ L ih =>
      obtain ⟨_, h1⟩ := add_bits c x y
      rw [binBits_succ, binBits_succ, zipFin, pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul,
        ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h1, ← ih]
      rfl

/-- The carry out of an `L`-bit sum is `2 ^ L ≤ x + y + c`. -/
theorem zipFin_addF_lt (c : Bool) (L x y : ℕ) (hx : x < 2 ^ L) (hy : y < 2 ^ L) :
    zipFin addF c (binBits L x) (binBits L y) = decide (2 ^ L ≤ x + y + c.toNat) := by
  have h := zipFin_addF c L x y
  rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy] at h
  have hc := Bool.toNat_le c
  by_cases hs : 2 ^ L ≤ x + y + c.toNat
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)] at h
    cases hz : zipFin addF c (binBits L x) (binBits L y) <;> simp_all
  · rw [Nat.div_eq_of_lt (by omega)] at h
    cases hz : zipFin addF c (binBits L x) (binBits L y) <;> simp_all

lemma binBits_not (L y : ℕ) (hy : y < 2 ^ L) :
    (binBits L y).map not = binBits L (2 ^ L - 1 - y) := by
  induction L generalizing y with
  | zero => rfl
  | succ L ih =>
      have hP : 0 < 2 ^ L := Nat.two_pow_pos L
      rw [pow_succ] at hy ⊢
      rw [binBits_succ, binBits_succ, List.map_cons, ih (y / 2) (by omega)]
      congr 1
      · rcases Nat.mod_two_eq_zero_or_one y with h | h <;>
          simp [Nat.testBit_zero, h] <;> omega
      · congr 1; omega

lemma subF_eq (β p q : Bool) : subF β p q = (!(addF (!β) p (!q)).1, (addF (!β) p (!q)).2) := by
  cases β <;> cases p <;> cases q <;> rfl

lemma zipOut_subF : ∀ (β : Bool) (xs ys : List Bool),
    zipOut subF β xs ys = zipOut addF (!β) xs (ys.map not)
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | β, p :: xs, q :: ys => by
      simp only [zipOut, List.map_cons, subF_eq]
      rw [zipOut_subF, Bool.not_not]

lemma zipFin_subF : ∀ (β : Bool) (xs ys : List Bool),
    zipFin subF β xs ys = !zipFin addF (!β) xs (ys.map not)
  | _, [], _ => by simp [zipFin]
  | _, _ :: _, [] => by simp [zipFin]
  | β, p :: xs, q :: ys => by
      simp only [zipFin, List.map_cons, subF_eq]
      rw [zipFin_subF, Bool.not_not]

/-- The difference bits: the low `L` bits of `x + 2 ^ L - y`, that is of `x - y` modulo
`2 ^ L`. -/
theorem zipOut_subF_binBits (L x y : ℕ) (hy : y < 2 ^ L) :
    zipOut subF false (binBits L x) (binBits L y) = binBits L (x + 2 ^ L - y) := by
  rw [zipOut_subF, binBits_not L y hy, Bool.not_false, zipOut_addF]
  congr 1
  simp only [Bool.toNat_true]
  omega

/-- The borrow out of an `L`-bit difference is `x < y`. -/
theorem zipFin_subF_binBits (L x y : ℕ) (hx : x < 2 ^ L) (hy : y < 2 ^ L) :
    zipFin subF false (binBits L x) (binBits L y) = decide (x < y) := by
  rw [zipFin_subF, binBits_not L y hy, Bool.not_false,
    zipFin_addF_lt true L x _ hx (by omega)]
  simp only [Bool.toNat_true]
  by_cases hxy : x < y
  · simp [hxy]; omega
  · simp [hxy]; omega

/-! ### Comparison -/

lemma mod_two_pow_succ' (x L : ℕ) : x % 2 ^ (L + 1) = 2 * (x / 2 % 2 ^ L) + x % 2 := by
  rw [pow_succ, Nat.mul_comm, Nat.mod_mul]
  ring

theorem zipFin_ltF (s : Bool) (L x y : ℕ) :
    zipFin ltF s (binBits L x) (binBits L y) =
      (decide (x % 2 ^ L < y % 2 ^ L) || decide (x % 2 ^ L = y % 2 ^ L) && s) := by
  induction L generalizing x y s with
  | zero => simp [zipFin, binBits, Nat.mod_one]
  | succ L ih =>
      rw [binBits_succ, binBits_succ, zipFin, ih, mod_two_pow_succ' x, mod_two_pow_succ' y]
      have := Nat.mod_lt (x / 2) (Nat.two_pow_pos L)
      have := Nat.mod_lt (y / 2) (Nat.two_pow_pos L)
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
        rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> cases s <;>
        simp [ltF, Nat.testBit_zero, hx, hy]
      all_goals (try rw [Bool.eq_iff_iff])
      all_goals (try simp only [Bool.or_eq_true, decide_eq_true_eq] at *)
      all_goals omega

theorem zipFin_eqF (s : Bool) (L x y : ℕ) :
    zipFin eqF s (binBits L x) (binBits L y) = (s && decide (x % 2 ^ L = y % 2 ^ L)) := by
  induction L generalizing x y s with
  | zero => simp [zipFin, binBits, Nat.mod_one]
  | succ L ih =>
      rw [binBits_succ, binBits_succ, zipFin, ih, mod_two_pow_succ' x, mod_two_pow_succ' y]
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
        rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> cases s <;>
        simp [eqF, Nat.testBit_zero, hx, hy] <;> omega

/-! ### Numerals -/

lemma getElem_binSyms (L x j : ℕ) (h : j < (binSyms L x : List (Fin (A + 4))).length) :
    (binSyms L x : List (Fin (A + 4)))[j] = bitSymbol (x.testBit j) := by
  simp [binSyms]

lemma getElem_reverse_binSyms (L x j : ℕ)
    (h : j < (binSyms L x : List (Fin (A + 4))).reverse.length) :
    (binSyms L x : List (Fin (A + 4))).reverse[j] = bitSymbol (x.testBit (L - 1 - j)) := by
  rw [List.getElem_reverse, getElem_binSyms, length_binSyms]

/-- Splitting a numeral at bit `L`. -/
lemma binSyms_append (L e x : ℕ) :
    (binSyms (L + e) x : List (Fin (A + 4))) = binSyms L x ++ binSyms e (x / 2 ^ L) := by
  induction L generalizing x with
  | zero => simp [binSyms]
  | succ L ih =>
      rw [Nat.add_right_comm, binSyms_succ, binSyms_succ, ih, pow_succ', ← Nat.div_div_eq_div_mul]
      rfl

/-- High zeros: an `L`-bit value written in width `L + e`. -/
lemma binSyms_pad (L e x : ℕ) (hx : x < 2 ^ L) :
    (binSyms (L + e) x : List (Fin (A + 4))) = binSyms L x ++ List.replicate e (bitSymbol false) := by
  rw [binSyms_append, Nat.div_eq_of_lt hx, binSyms_zero_right]

/-- Dropping the top bit. -/
lemma binSyms_dropLast (W y : ℕ) :
    (binSyms (W + 1) y : List (Fin (A + 4))).dropLast = binSyms W y := by
  rw [binSyms_succ', List.dropLast_concat]

/-- Shifting the bit `b` in at the bottom and dropping the top bit: `y ↦ 2 y + b` in width `W`. -/
lemma binSyms_shift (b : Bool) (W y : ℕ) :
    (bitSymbol b :: binSyms W y : List (Fin (A + 4))).dropLast = binSyms W (2 * y + b.toNat) := by
  cases W with
  | zero => rfl
  | succ W =>
      rw [binSyms_succ', ← List.cons_append, List.dropLast_concat, binSyms_succ]
      congr 2
      · cases b <;> simp [Nat.testBit_zero]
      · cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The high part `x / 2 ^ k` gains bit `k` below the high part `x / 2 ^ (k + 1)`. -/
lemma div_two_pow_eq (x k : ℕ) : x / 2 ^ k = 2 * (x / 2 ^ (k + 1)) + (x.testBit k).toNat := by
  have h1 : x / 2 ^ (k + 1) = x / 2 ^ k / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have h2 : x.testBit k = (x / 2 ^ k).testBit 0 := by rw [Nat.testBit_div_two_pow, Nat.zero_add]
  rw [h1, h2]
  generalize x / 2 ^ k = n
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.testBit_zero, h] <;> omega

/-- One step of restoring division: shifting the bit `b` into `n` doubles the quotient and adds
one exactly when the doubled remainder plus `b` reaches the divisor, which it then loses. -/
lemma div_step (y n : ℕ) (b : Bool) (hy : 0 < y) :
    (2 * n + b.toNat) / y = 2 * (n / y) + (decide (y ≤ 2 * (n % y) + b.toNat)).toNat ∧
      (2 * n + b.toNat) % y = if y ≤ 2 * (n % y) + b.toNat then 2 * (n % y) + b.toNat - y
        else 2 * (n % y) + b.toNat := by
  have hn := Nat.div_add_mod n y
  have hr := Nat.mod_lt n hy
  have hb := Bool.toNat_le b
  have hm : y * (2 * (n / y) + 1) = 2 * (y * (n / y)) + y := by ring
  have hm' : y * (2 * (n / y)) = 2 * (y * (n / y)) := by ring
  by_cases h : y ≤ 2 * (n % y) + b.toNat
  · simp only [h, decide_true, Bool.toNat_true, ↓reduceIte]
    exact (Nat.div_mod_unique hy).2 ⟨by omega, by omega⟩
  · simp only [h, decide_false, Bool.toNat_false, ↓reduceIte, Nat.add_zero]
    exact (Nat.div_mod_unique hy).2 ⟨by omega, by omega⟩

end IntegerMultBounds.MathlibTM2.Host
