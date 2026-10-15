module

public import IntegerMultBounds.MathlibTM2.Node.Rect
public import IntegerMultBounds.MathlibTM2.Host.IndexRoute

/-!
# The host pass of one controlled rotation

`rotPass neg b` runs the instruction `Instr.rot neg b` of the packed program
(`IntegerMultBounds.MathlibTM2.Layer.PackedXor`) on a stream of records: the record at physical address `(s, c)` moves
to the address whose slot `c₂` is `c₂ + off` (`neg = false`) or `c₂ - off` (`neg = true`) modulo
`2^L`, with `off = offMag K ρ (f - 1) b c₀ c₁`.

**Stream.** Register `src` holds `l.flatten` for `M = rectSize N₀ N₁ N₂ N₃ L` records of `B ≥ 1`
symbols in rank order (`PackedXor.rank`), with `N₀ = R 2^n₀`, `N₁ = 2^n₁`, `N₂ = 2^n₂`,
`N₃ = 2^n₃`. The binary digits of the index of a record are, least significant first, `s₃`
(`n₃` bits), `c₂` (`L`), `s₂` (`n₂`), `c₁` (`L`), `s₁` (`n₁`), `c₀` (`L`) and `s₀`. The field
counter of `IntegerMultBounds.MathlibTM2.Host.Index` with the field lengths `rotLen = [n₃, L, n₂, L, n₁, L, n₀]`
(zero lengths included) holds `c₂`, `c₁`, `c₀` in its fields `1`, `3`, `5` (`rotLen_digit_rank`);
it wraps after `2^(n₃ + 3L + n₂ + n₁ + n₀)` records, a divisor of `M` (`rotLen_digit_rect`).

**Codes.** The input class of a record is whether its rotation wraps around `2^L` (`wrapIn`:
`c₂ + off ≥ 2^L` for `+`, `c₂ < off` for `-`); the output class of an index is the input class
of its preimage (`wrapOut`: `c₂' < off` for `+`, `c₂' + off ≥ 2^L` for `-`). Both are
least-significant-first carry or borrow automata (`carryA`, `borrowA`, combined in `inCode` and
`outCode`) on the fields `c₀`, `c₁`, `c₂` and a parameter register holding the mask
`selMask K ρ (f - 1)`: bit `t` of the offset is `mask_t ∧ c₀_t ∧ (c₁_t = b)` (`offBit`), which
sums to `offMag` when `K ≥ 1` (`offMag_eq_offLow`). `inCode_eval` and `outCode_eval` identify the
automata with the classes.

**Order.** The rotation fixes the coordinates `(s₀, c₀, s₁, c₁, s₂)` of an address and adds one
shift (`rotShift`) to every slot value `c₂` of one class, so it matches the codes
(`wrapOut_rotAddr`) and keeps the rank order within each class (`rank_rotAddr_lt`).
`mergeIdxList_perm` then gives the list semantics `rot_merge`.

**Pass.** `routeIdx` moves the records onto `dst 0`, `dst 1` by input code; `revEach` reverses
them onto `aux 0`, `aux 1`; `mergeIdx` merges them onto `out` by output code; `moveR` moves `out`
onto `src`. The registers are named by `RotReg` and placed by an injective `ι : RotReg → Fin T`;
the code state and the carry live in the scan slot `st`. `rotPass_exec`: `src` ends holding
`(moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) [Instr.rot neg b]) l).flatten`, every other stack
ends as it started, and `user` is kept, in at most
`M * (12 * B + 12 * (n₃ + 3 * L + n₂ + n₁ + n₀) + 84) + 13` steps (`rotPass_exec_exact` has the
exact count).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Layer.PackedXor IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

set_option linter.unusedSimpArgs false

/-! ### The offset read bit by bit -/

/-- Bit `t` of a rotation offset: mask bit `t` of `m`, control bit `t` of `c`, and bit `t` of the
tested field `w` equal to `b`. -/
def offBit (b : Bool) (c w m t : ℕ) : Bool := m.testBit t && c.testBit t && (w.testBit t == b)

/-- The offset assembled from its bits `t < L`. -/
def offLow (L : ℕ) (b : Bool) (c w m : ℕ) : ℕ :=
  ∑ t ∈ Finset.range L, if offBit b c w m t then 2 ^ t else 0

lemma offLow_succ (L : ℕ) (b : Bool) (c w m : ℕ) :
    offLow (L + 1) b c w m =
      (offBit b c w m 0).toNat + 2 * offLow L b (c / 2) (w / 2) (m / 2) := by
  unfold offLow
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  congr 1
  · cases offBit b c w m 0 <;> simp
  · apply Finset.sum_congr rfl
    intro t _
    simp only [offBit, Nat.testBit_div_two, pow_succ]
    split_ifs <;> ring

lemma offLow_lt (b : Bool) : ∀ (L c w m : ℕ), offLow L b c w m < 2 ^ L := by
  intro L
  induction L with
  | zero => intro c w m; simp [offLow]
  | succ L ih =>
    intro c w m
    rw [offLow_succ, pow_succ]
    have h1 := ih (c / 2) (w / 2) (m / 2)
    have h2 : (offBit b c w m 0).toNat ≤ 1 := Bool.toNat_le _
    omega

/-- With `K ≥ 1` the selected positions are distinct, and for an `L`-bit control `c` the packed
offset is the offset read from bits `t < L` against the mask `selMask K ρ n`. -/
lemma offMag_eq_offLow {K ρ n L : ℕ} (hK : 0 < K) (b : Bool) {c : ℕ} (hc : c < 2 ^ L) (w : ℕ) :
    offMag K ρ n b c w = offLow L b c w (selMask K ρ n) := by
  set g : ℕ → ℕ := fun j => if c.testBit j = true ∧ w.testBit j = b then 2 ^ j else 0 with hg
  have h1 : offMag K ρ n b c w = ∑ j ∈ (Finset.range n).image (fun i => ρ + i * K), g j := by
    rw [Finset.sum_image]
    · rfl
    · intro x _ y _ hxy
      simp only at hxy
      exact Nat.eq_of_mul_eq_mul_right hK (by omega)
  have h2 : offLow L b c w (selMask K ρ n) =
      ∑ j ∈ (Finset.range L).filter (IsSel K ρ n), g j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    simp only [offBit, hg]
    by_cases hs : IsSel K ρ n t
    · have h := (testBit_selMask K ρ n t).2 hs
      by_cases hc' : c.testBit t = true <;> by_cases hw : w.testBit t = b <;> simp [h, hs, hc', hw]
    · have h := selMask_false K ρ n hs
      simp [h, hs]
  rw [h1, h2]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨_, i, hi, rfl⟩ := hj
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  · intro j hj hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hj'
    have hL : L ≤ ρ + i * K := by
      by_contra h
      exact hj' (by omega) ⟨i, Finset.mem_range.1 hi, rfl⟩
    have : c.testBit (ρ + i * K) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hL))
    simp [hg, this]

/-! ### Carry and borrow automata -/

variable {A : ℕ}

/-- The class of a carry or borrow bit. -/
def rotCls (x : Bool) : Fin 2 := if x then 1 else 0

lemma rotCls_inj {x y : Bool} : rotCls x = rotCls y ↔ x = y := by
  cases x <;> cases y <;> decide

/-- Carry automaton of `x + off`, reading `c₀, c₁, x, m` in registers `0, 1, 2, 3`, where bit
`t` of `off` is `offBit b c₀ c₁ m t`; the state is the carry. -/
def carryA (A : ℕ) (b : Bool) : CAuto A 4 2 where
  init := bitSymbol false
  step s x := bitSymbol (if x 2 then (x 3 && x 0 && (x 1 == b)) || symBit s
    else (x 3 && x 0 && (x 1 == b)) && symBit s)
  out s := rotCls (symBit s)

/-- Borrow automaton of `x - off`, with the registers of `carryA`; the state is the borrow. -/
def borrowA (A : ℕ) (b : Bool) : CAuto A 4 2 where
  init := bitSymbol false
  step s x := bitSymbol (if x 2 then (x 3 && x 0 && (x 1 == b)) && symBit s
    else (x 3 && x 0 && (x 1 == b)) || symBit s)
  out s := rotCls (symBit s)

lemma carryA_run (b : Bool) : ∀ (L : ℕ) (cy : Bool) (vals : Fin 4 → ℕ),
    symBit ((carryA A b).run L (bitSymbol cy) vals) =
      decide (2 ^ L ≤ vals 2 % 2 ^ L + offLow L b (vals 0) (vals 1) (vals 3) + cy.toNat) := by
  intro L
  induction L with
  | zero => intro cy vals; cases cy <;> simp [CAuto.run, offLow, Nat.mod_one]
  | succ L ih =>
    intro cy vals
    have hstep : ∀ s x, (carryA A b).step s x = bitSymbol (if x 2 then
        (x 3 && x 0 && (x 1 == b)) || symBit s else (x 3 && x 0 && (x 1 == b)) && symBit s) :=
      fun _ _ => rfl
    rw [CAuto.run, hstep, ih, offLow_succ]
    have hx : vals 2 % 2 ^ (L + 1) = vals 2 % 2 + 2 * (vals 2 / 2 % 2 ^ L) := by
      rw [pow_succ', Nat.mod_mul]
    have ho : ((vals 3).testBit 0 && (vals 0).testBit 0 && ((vals 1).testBit 0 == b)) =
        offBit b (vals 0) (vals 1) (vals 3) 0 := rfl
    simp only [symBit_bitSymbol]
    rw [ho]
    simp only [hx, Nat.testBit_zero]
    generalize offBit b (vals 0) (vals 1) (vals 3) 0 = o
    generalize offLow L b (vals 0 / 2) (vals 1 / 2) (vals 3 / 2) = O
    generalize vals 2 / 2 % 2 ^ L = y
    have hP : 2 ^ (L + 1) = 2 * 2 ^ L := pow_succ' 2 L
    rw [hP]
    rcases Nat.mod_two_eq_zero_or_one (vals 2) with h | h <;> rw [h] <;>
      cases o <;> cases cy <;> simp <;> omega

lemma borrowA_run (b : Bool) : ∀ (L : ℕ) (br : Bool) (vals : Fin 4 → ℕ),
    symBit ((borrowA A b).run L (bitSymbol br) vals) =
      decide (vals 2 % 2 ^ L < offLow L b (vals 0) (vals 1) (vals 3) + br.toNat) := by
  intro L
  induction L with
  | zero => intro br vals; cases br <;> simp [CAuto.run, offLow, Nat.mod_one]
  | succ L ih =>
    intro br vals
    have hstep : ∀ s x, (borrowA A b).step s x = bitSymbol (if x 2 then
        (x 3 && x 0 && (x 1 == b)) && symBit s else (x 3 && x 0 && (x 1 == b)) || symBit s) :=
      fun _ _ => rfl
    rw [CAuto.run, hstep, ih, offLow_succ]
    have hx : vals 2 % 2 ^ (L + 1) = vals 2 % 2 + 2 * (vals 2 / 2 % 2 ^ L) := by
      rw [pow_succ', Nat.mod_mul]
    have ho : ((vals 3).testBit 0 && (vals 0).testBit 0 && ((vals 1).testBit 0 == b)) =
        offBit b (vals 0) (vals 1) (vals 3) 0 := rfl
    simp only [symBit_bitSymbol]
    rw [ho]
    simp only [hx, Nat.testBit_zero]
    generalize offBit b (vals 0) (vals 1) (vals 3) 0 = o
    generalize offLow L b (vals 0 / 2) (vals 1 / 2) (vals 3 / 2) = O
    generalize vals 2 / 2 % 2 ^ L = y
    rcases Nat.mod_two_eq_zero_or_one (vals 2) with h | h <;> rw [h] <;>
      cases o <;> cases br <;> simp <;> omega

/-! ### Wrap classes of a rotation -/

/-- Input class of the slot value `c₂` under `c₂ ↦ c₂ + off` (`neg = false`) or
`c₂ ↦ c₂ - off` (`neg = true`) modulo `2^L`: the rotation wraps around. -/
def wrapIn (L : ℕ) (neg : Bool) (off c₂ : ℕ) : Bool :=
  if neg then decide (c₂ < off) else decide (2 ^ L ≤ c₂ + off)

/-- Output class of the slot value `c₂'`: its preimage under the rotation wraps around. -/
def wrapOut (L : ℕ) (neg : Bool) (off c₂' : ℕ) : Bool :=
  if neg then decide (2 ^ L ≤ c₂' + off) else decide (c₂' < off)

/-- The input code: the carry of `c₂ + off` or the borrow of `c₂ - off`. -/
def inCode (A : ℕ) (neg b : Bool) : CAuto A 4 2 := if neg then borrowA A b else carryA A b

/-- The output code: the borrow of `c₂' - off` or the carry of `c₂' + off`. -/
def outCode (A : ℕ) (neg b : Bool) : CAuto A 4 2 := if neg then carryA A b else borrowA A b

lemma carryA_eval (b : Bool) (L : ℕ) (vals : Fin 4 → ℕ) :
    (carryA A b).eval L vals =
      rotCls (decide (2 ^ L ≤ vals 2 % 2 ^ L + offLow L b (vals 0) (vals 1) (vals 3))) := by
  show rotCls (symBit ((carryA A b).run L (bitSymbol false) vals)) = _
  rw [carryA_run]
  simp

lemma borrowA_eval (b : Bool) (L : ℕ) (vals : Fin 4 → ℕ) :
    (borrowA A b).eval L vals =
      rotCls (decide (vals 2 % 2 ^ L < offLow L b (vals 0) (vals 1) (vals 3))) := by
  show rotCls (symBit ((borrowA A b).run L (bitSymbol false) vals)) = _
  rw [borrowA_run]
  simp

/-- **The input code computes the input class.** -/
theorem inCode_eval {K ρ n L : ℕ} (hK : 0 < K) (neg b : Bool) {c₀ c₂ : ℕ} (h₀ : c₀ < 2 ^ L)
    (h₂ : c₂ < 2 ^ L) (c₁ : ℕ) :
    (inCode A neg b).eval L ![c₀, c₁, c₂, selMask K ρ n] =
      rotCls (wrapIn L neg (offMag K ρ n b c₀ c₁) c₂) := by
  rw [offMag_eq_offLow hK b h₀]
  cases neg
  · simp [inCode, wrapIn, carryA_eval, Nat.mod_eq_of_lt h₂]
  · simp [inCode, wrapIn, borrowA_eval, Nat.mod_eq_of_lt h₂]

/-- **The output code computes the output class.** -/
theorem outCode_eval {K ρ n L : ℕ} (hK : 0 < K) (neg b : Bool) {c₀ c₂ : ℕ} (h₀ : c₀ < 2 ^ L)
    (h₂ : c₂ < 2 ^ L) (c₁ : ℕ) :
    (outCode A neg b).eval L ![c₀, c₁, c₂, selMask K ρ n] =
      rotCls (wrapOut L neg (offMag K ρ n b c₀ c₁) c₂) := by
  rw [offMag_eq_offLow hK b h₀]
  cases neg
  · simp [outCode, wrapOut, borrowA_eval, Nat.mod_eq_of_lt h₂]
  · simp [outCode, wrapOut, carryA_eval, Nat.mod_eq_of_lt h₂]

/-- The shift of a rotation by `± off` on a value of wrap class `w`. -/
def rotShift (L : ℕ) (neg : Bool) (off : ℕ) (w : Bool) : ℤ :=
  (if neg then -(off : ℤ) else off) + (if w then (if neg then 2 ^ L else -2 ^ L) else 0)

private lemma emod_of_bounds (x d k : ℤ) (h1 : 0 ≤ x - k * d) (h2 : x - k * d < d) :
    x % d = x - k * d := by
  have : x = (x - k * d) + d * k := by ring
  rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h1 h2]
  ring

/-- A rotation by `± off` adds the shift of the wrap class. -/
lemma rot_eq_shift (L : ℕ) (neg : Bool) (v : Fin (2 ^ L)) {off : ℕ} (ho : off < 2 ^ L) :
    (((rot L v (sgn neg * off) : Fin (2 ^ L)) : ℕ) : ℤ) =
      (v : ℤ) + rotShift L neg off (wrapIn L neg off v) := by
  rw [rot_val]
  have hv : ((v : ℕ) : ℤ) < 2 ^ L := by exact_mod_cast v.isLt
  have ho' : (off : ℤ) < 2 ^ L := by exact_mod_cast ho
  cases neg
  · by_cases hw : 2 ^ L ≤ (v : ℕ) + off
    · have hw' : (2 : ℤ) ^ L ≤ v + off := by exact_mod_cast hw
      simp only [sgn, wrapIn, rotShift, Bool.false_eq_true, ite_false, hw, decide_true, ite_true,
        one_mul]
      rw [emod_of_bounds _ _ 1 (by linarith) (by linarith)]
      ring
    · have hw' : ((v : ℕ) : ℤ) + off < 2 ^ L := by exact_mod_cast not_le.mp hw
      simp only [sgn, wrapIn, rotShift, Bool.false_eq_true, ite_false, hw, decide_false, one_mul]
      rw [emod_of_bounds _ _ 0 (by simp; positivity) (by linarith)]
      ring
  · by_cases hw : (v : ℕ) < off
    · have hw' : ((v : ℕ) : ℤ) < off := by exact_mod_cast hw
      simp only [sgn, wrapIn, rotShift, ite_true, hw, decide_true]
      rw [emod_of_bounds _ _ (-1) (by linarith) (by linarith)]
      ring
    · have hw' : (off : ℤ) ≤ (v : ℕ) := by exact_mod_cast not_lt.mp hw
      simp only [sgn, wrapIn, rotShift, ite_true, hw, decide_false, Bool.false_eq_true, ite_false]
      rw [emod_of_bounds _ _ 0 (by linarith) (by linarith)]
      ring

/-- The output class of a rotated value is the input class of the value. -/
lemma wrapOut_rot (L : ℕ) (neg : Bool) (v : Fin (2 ^ L)) {off : ℕ} (ho : off < 2 ^ L) :
    wrapOut L neg off (rot L v (sgn neg * off)) = wrapIn L neg off v := by
  have h := rot_eq_shift L neg v ho
  have hr := (rot L v (sgn neg * off)).isLt
  have hv := v.isLt
  generalize ((rot L v (sgn neg * off) : Fin (2 ^ L)) : ℕ) = r at h hr ⊢
  have hP : ((2 : ℤ) ^ L) = ((2 ^ L : ℕ) : ℤ) := by push_cast; rfl
  cases neg <;> cases hw : wrapIn L _ off v <;>
    simp only [wrapIn, Bool.false_eq_true, ite_false, ite_true, decide_eq_true_eq,
      decide_eq_false_iff_not] at hw <;>
    simp only [rotShift, hw, Bool.false_eq_true, ite_false, ite_true, wrapOut, decide_eq_true_eq,
      decide_eq_false_iff_not, hP] at h ⊢ <;> omega

/-! ### Ranks -/

private lemma lex_lt {N a a' x y : ℕ} (ha : a < N) (h : x < y) : a + N * x < a' + N * y := by
  have : N * x + N ≤ N * y := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
  omega

private lemma lex_le {N a a' x y : ℕ} (ha' : a' < N) (h : a + N * x < a' + N * y) : x ≤ y := by
  by_contra hc
  have := lex_lt (a' := a) ha' (not_le.mp hc)
  omega

private lemma lex_eq {N a a' x y : ℕ} (ha : a < N) (ha' : a' < N) (h : a + N * x = a' + N * y) :
    a = a' ∧ x = y := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have := lex_lt (a' := a') ha hxy; omega
  · omega
  · have := lex_lt (a' := a) ha' hxy; omega

private lemma div_lex {a N x : ℕ} (ha : a < N) : (a + N * x) / N = x := by
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ha, Nat.zero_add]

private lemma mod_lex {a N x : ℕ} (ha : a < N) : (a + N * x) % N = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

section Rank

variable {N₀ N₁ N₂ N₃ L : ℕ}

/-- The part of a rank above `s₃` and `c₂`: the coordinates `(s₀, c₀, s₁, c₁, s₂)`. -/
private def hiPart (p : Addr N₀ N₁ N₂ N₃ L) : ℕ :=
  (p.1.2.2.1 : ℕ) + N₂ * ((p.2 1 : ℕ) + 2 ^ L * ((p.1.2.1 : ℕ) + N₁ * ((p.2 0 : ℕ) +
    2 ^ L * (p.1.1 : ℕ))))

private lemma rank_eq_hiPart (p : Addr N₀ N₁ N₂ N₃ L) :
    rank N₀ N₁ N₂ N₃ L p = (p.1.2.2.2 : ℕ) + N₃ * ((p.2 2 : ℕ) + 2 ^ L * hiPart p) := rfl

/-- Equal high parts have equal `c₀` and `c₁`. -/
private lemma hiPart_inj {p q : Addr N₀ N₁ N₂ N₃ L} (h : hiPart p = hiPart q) :
    p.2 0 = q.2 0 ∧ p.2 1 = q.2 1 := by
  unfold hiPart at h
  obtain ⟨_, h1⟩ := lex_eq p.1.2.2.1.isLt q.1.2.2.1.isLt h
  obtain ⟨hc1, h2⟩ := lex_eq (p.2 1).isLt (q.2 1).isLt h1
  obtain ⟨_, h3⟩ := lex_eq p.1.2.1.isLt q.1.2.1.isLt h2
  obtain ⟨hc0, _⟩ := lex_eq (p.2 0).isLt (q.2 0).isLt h3
  exact ⟨Fin.ext hc0, Fin.ext hc1⟩

variable (K ρ n : ℕ) (neg b : Bool)

/-- The address after the rotation `Instr.rot neg b`. -/
def rotAddr (p : Addr N₀ N₁ N₂ N₃ L) : Addr N₀ N₁ N₂ N₃ L :=
  (p.1, crot L 2 0 1 (fun c₀ c₁ => sgn neg * offMag K ρ n b c₀ c₁) p.2)

lemma rotAddr_0 (p : Addr N₀ N₁ N₂ N₃ L) : (rotAddr K ρ n neg b p).2 0 = p.2 0 := by
  simp [rotAddr, crot, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)]

lemma rotAddr_1 (p : Addr N₀ N₁ N₂ N₃ L) : (rotAddr K ρ n neg b p).2 1 = p.2 1 := by
  simp [rotAddr, crot, Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

lemma rotAddr_2 (p : Addr N₀ N₁ N₂ N₃ L) :
    (rotAddr K ρ n neg b p).2 2 = rot L (p.2 2) (sgn neg * offMag K ρ n b (p.2 0) (p.2 1)) := by
  simp [rotAddr, crot]

private lemma hiPart_rotAddr (p : Addr N₀ N₁ N₂ N₃ L) :
    hiPart (rotAddr K ρ n neg b p) = hiPart p := by
  simp only [hiPart, rotAddr_0, rotAddr_1]
  rfl

private lemma rank_rotAddr (p : Addr N₀ N₁ N₂ N₃ L) :
    rank N₀ N₁ N₂ N₃ L (rotAddr K ρ n neg b p) =
      (p.1.2.2.2 : ℕ) + N₃ * ((rotAddr K ρ n neg b p).2 2 + 2 ^ L * hiPart p) := by
  rw [rank_eq_hiPart, hiPart_rotAddr]
  rfl

/-- The offset of an address. -/
def rotOff (p : Addr N₀ N₁ N₂ N₃ L) : ℕ := offMag K ρ n b (p.2 0) (p.2 1)

lemma rotOff_lt (hK : 0 < K) (p : Addr N₀ N₁ N₂ N₃ L) : rotOff K ρ n b p < 2 ^ L := by
  rw [rotOff, offMag_eq_offLow hK b (p.2 0).isLt]
  exact offLow_lt _ _ _ _ _

/-- **Code match.** The output class of a rotated address is the input class of the address. -/
lemma wrapOut_rotAddr (hK : 0 < K) (p : Addr N₀ N₁ N₂ N₃ L) :
    wrapOut L neg (rotOff K ρ n b (rotAddr K ρ n neg b p)) ((rotAddr K ρ n neg b p).2 2) =
      wrapIn L neg (rotOff K ρ n b p) (p.2 2) := by
  simp only [rotOff, rotAddr_0, rotAddr_1, rotAddr_2]
  exact wrapOut_rot L neg (p.2 2) (rotOff_lt K ρ n b hK p)

/-- **Order match.** Within one wrap class the rotation preserves the rank order. -/
lemma rank_rotAddr_lt (hK : 0 < K) {p q : Addr N₀ N₁ N₂ N₃ L}
    (hpq : rank N₀ N₁ N₂ N₃ L p < rank N₀ N₁ N₂ N₃ L q)
    (hw : wrapIn L neg (rotOff K ρ n b p) (p.2 2) = wrapIn L neg (rotOff K ρ n b q) (q.2 2)) :
    rank N₀ N₁ N₂ N₃ L (rotAddr K ρ n neg b p) < rank N₀ N₁ N₂ N₃ L (rotAddr K ρ n neg b q) := by
  rw [rank_eq_hiPart, rank_eq_hiPart] at hpq
  rw [rank_rotAddr, rank_rotAddr]
  have hs := p.1.2.2.2.isLt
  have hs' := q.1.2.2.2.isLt
  have hu := lex_le hs' hpq
  rcases Nat.lt_or_eq_of_le hu with hu | hu
  · apply lex_lt hs
    have hH := lex_le (q.2 2).isLt hu
    rcases Nat.lt_or_eq_of_le hH with hH | hH
    · exact lex_lt ((rotAddr K ρ n neg b p).2 2).isLt hH
    · rw [hH]
      apply Nat.add_lt_add_right
      obtain ⟨h0, h1⟩ := hiPart_inj hH
      have hoff : rotOff K ρ n b p = rotOff K ρ n b q := by simp [rotOff, h0, h1]
      have hc : (p.2 2 : ℕ) < q.2 2 := by rw [hH] at hu; omega
      rw [← hoff] at hw
      have e1 : (((rotAddr K ρ n neg b p).2 2 : ℕ) : ℤ) = ((p.2 2 : ℕ) : ℤ) +
          rotShift L neg (rotOff K ρ n b p) (wrapIn L neg (rotOff K ρ n b p) (p.2 2)) := by
        rw [rotAddr_2]; exact rot_eq_shift L neg (p.2 2) (rotOff_lt K ρ n b hK p)
      have e2 : (((rotAddr K ρ n neg b q).2 2 : ℕ) : ℤ) = ((q.2 2 : ℕ) : ℤ) +
          rotShift L neg (rotOff K ρ n b p) (wrapIn L neg (rotOff K ρ n b p) (p.2 2)) := by
        rw [rotAddr_2, hw, hoff]; exact rot_eq_shift L neg (q.2 2) (rotOff_lt K ρ n b hK q)
      have : (((rotAddr K ρ n neg b p).2 2 : ℕ) : ℤ) < (((rotAddr K ρ n neg b q).2 2 : ℕ) : ℤ) := by
        rw [e1, e2]
        have : ((p.2 2 : ℕ) : ℤ) < ((q.2 2 : ℕ) : ℤ) := by exact_mod_cast hc
        linarith
      exact_mod_cast this
  · obtain ⟨hc, hH⟩ := lex_eq (p.2 2).isLt (q.2 2).isLt hu
    obtain ⟨h0, h1⟩ := hiPart_inj hH
    have h2 : p.2 2 = q.2 2 := Fin.ext hc
    rw [rotAddr_2, rotAddr_2, h0, h1, h2, hH]
    rw [hu] at hpq
    omega

end Rank

/-! ### Index fields and codes -/

/-- Field lengths of the index counter, least significant first: `s₃, c₂, s₂, c₁, s₁, c₀, s₀`. -/
def rotLen (n₀ n₁ n₂ n₃ L : ℕ) : Fin 7 → ℕ := ![n₃, L, n₂, L, n₁, L, n₀]

/-- Sources of the code-pass registers `0, 1, 2, 3`: the fields of `c₀`, `c₁`, `c₂`, and the mask
parameter. -/
def rotSrc (mask : ℕ) : Fin 4 → Fin 7 ⊕ ℕ := ![.inl 5, .inl 3, .inl 1, .inr mask]

lemma rotLen_sum (n₀ n₁ n₂ n₃ L : ℕ) :
    ∑ g, rotLen n₀ n₁ n₂ n₃ L g = n₃ + 3 * L + n₂ + n₁ + n₀ := by
  simp [rotLen, Fin.sum_univ_succ]; ring

lemma fieldOff_rotLen (n₀ n₁ n₂ n₃ L : ℕ) :
    fieldOff (rotLen n₀ n₁ n₂ n₃ L) 1 = n₃ ∧ fieldOff (rotLen n₀ n₁ n₂ n₃ L) 3 = n₃ + L + n₂ ∧
    fieldOff (rotLen n₀ n₁ n₂ n₃ L) 5 = n₃ + L + n₂ + L + n₁ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [fieldOff, Finset.sum_filter, Fin.sum_univ_succ, rotLen] <;> ring

section Codes

variable {N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ : ℕ}

/-- The counter fields of `c₂`, `c₁`, `c₀` hold the slot values of the rank. -/
lemma rotLen_digit_rank (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃)
    (p : Addr N₀ N₁ N₂ N₃ L) :
    digit (rotLen n₀ n₁ n₂ n₃ L) 1 (rank N₀ N₁ N₂ N₃ L p) = p.2 2 ∧
    digit (rotLen n₀ n₁ n₂ n₃ L) 3 (rank N₀ N₁ N₂ N₃ L p) = p.2 1 ∧
    digit (rotLen n₀ n₁ n₂ n₃ L) 5 (rank N₀ N₁ N₂ N₃ L p) = p.2 0 := by
  subst hN₁ hN₂ hN₃
  obtain ⟨h1, h3, h5⟩ := fieldOff_rotLen n₀ n₁ n₂ n₃ L
  have hs₃ := p.1.2.2.2.isLt
  have hc₂ := (p.2 2).isLt
  have hs₂ := p.1.2.2.1.isLt
  have hc₁ := (p.2 1).isLt
  have hs₁ := p.1.2.1.isLt
  have hc₀ := (p.2 0).isLt
  have hl1 : rotLen n₀ n₁ n₂ n₃ L 1 = L := rfl
  have hl3 : rotLen n₀ n₁ n₂ n₃ L 3 = L := rfl
  have hl5 : rotLen n₀ n₁ n₂ n₃ L 5 = L := rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp only [digit, h1, h3, h5, hl1, hl3, hl5, pow_add,
    ← Nat.div_div_eq_div_mul, rank]
  · rw [div_lex hs₃, mod_lex hc₂]
  · rw [div_lex hs₃, div_lex hc₂, div_lex hs₂, mod_lex hc₁]
  · rw [div_lex hs₃, div_lex hc₂, div_lex hs₂, div_lex hc₁, div_lex hs₁, mod_lex hc₀]

lemma rotSrc_regVal_rank (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (mask : ℕ)
    (p : Addr N₀ N₁ N₂ N₃ L) :
    regVal (rotLen n₀ n₁ n₂ n₃ L) (rotSrc mask) (rank N₀ N₁ N₂ N₃ L p) =
      ![(p.2 0 : ℕ), p.2 1, p.2 2, mask] := by
  obtain ⟨h1, h3, h5⟩ := rotLen_digit_rank (n₀ := n₀) hN₁ hN₂ hN₃ p
  funext r
  fin_cases r <;> simp [regVal, rotSrc, h1, h3, h5]

variable (K ρ n : ℕ) (neg b : Bool)

lemma inCode_rank (hK : 0 < K) (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃)
    (p : Addr N₀ N₁ N₂ N₃ L) :
    idxCode (inCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n))
        (rank N₀ N₁ N₂ N₃ L p) = rotCls (wrapIn L neg (rotOff K ρ n b p) (p.2 2)) := by
  rw [idxCode, rotSrc_regVal_rank hN₁ hN₂ hN₃]
  exact inCode_eval hK neg b (p.2 0).isLt (p.2 2).isLt _

lemma outCode_rank (hK : 0 < K) (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃)
    (p : Addr N₀ N₁ N₂ N₃ L) :
    idxCode (outCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n))
        (rank N₀ N₁ N₂ N₃ L p) = rotCls (wrapOut L neg (rotOff K ρ n b p) (p.2 2)) := by
  rw [idxCode, rotSrc_regVal_rank hN₁ hN₂ hN₃]
  exact outCode_eval hK neg b (p.2 0).isLt (p.2 2).isLt _

/-- The rank map of one rotation, on addresses. -/
lemma rankPerm_rot (p : Addr N₀ N₁ N₂ N₃ L) :
    rankPerm N₀ N₁ N₂ N₃ L K ρ n [Instr.rot neg b] (rankEquiv N₀ N₁ N₂ N₃ L p) =
      rankEquiv N₀ N₁ N₂ N₃ L (rotAddr K ρ n neg b p) := by
  simp [rankPerm, progPerm, instrPerm, liftA, rotAddr, crotPerm]
  rfl

end Codes

/-- A permutation of `Fin M` as a map of `ℕ`, the identity from `M` on. -/
def rotIdxFun {M : ℕ} (π : Equiv.Perm (Fin M)) (i : ℕ) : ℕ := if h : i < M then π ⟨i, h⟩ else i

private lemma rotIdxFun_of_lt {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    rotIdxFun π i = π ⟨i, h⟩ := by simp [rotIdxFun, h]

private lemma rotIdxFun_lt {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    rotIdxFun π i < M := by
  rw [rotIdxFun_of_lt π h]; exact (π _).isLt

private lemma rotIdxFun_symm {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    rotIdxFun π.symm (rotIdxFun π i) = i := by
  rw [rotIdxFun_of_lt π h, rotIdxFun_of_lt π.symm (π _).isLt]
  simp

private lemma rotIdxFun_symm' {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    rotIdxFun π (rotIdxFun π.symm i) = i := by
  have := rotIdxFun_symm π.symm h
  rwa [Equiv.symm_symm] at this

/-! ### Records -/

section Lists

variable {α : Type}

private lemma length_flatten_of {B : ℕ} : ∀ (l : List (List α)), (∀ r ∈ l, r.length = B) →
    l.flatten.length = l.length * B
  | [], _ => by simp
  | r :: l, h => by
    rw [List.flatten_cons, List.length_append, h r List.mem_cons_self,
      length_flatten_of l (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')), List.length_cons]
    ring

/-- Block `k` of a flattened record list is record `k`. -/
private lemma blk_flatten {B : ℕ} : ∀ (l : List (List α)), (∀ r ∈ l, r.length = B) →
    ∀ k, blk l.flatten B k = l.getD k []
  | [], _, k => by simp [blk]
  | r :: l, h, k => by
    have hr := h r List.mem_cons_self
    cases k with
    | zero => simp [blk, List.take_left' hr]
    | succ k =>
      have := blk_flatten l (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) k
      rw [List.getD_cons_succ, ← this, List.flatten_cons]
      simp only [blk]
      rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hr]; nlinarith),
        List.nil_append, hr, show (k + 1) * B - B = k * B by rw [Nat.add_one_mul]; omega]

private lemma flatten_moveRecs {M B : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α))
    (hl : ∀ r ∈ l, r.length = B) :
    (moveRecs π l).flatten =
      (List.range M).flatMap (fun j => blk l.flatten B (rotIdxFun π.symm j)) := by
  rw [List.flatMap_def]
  congr 1
  apply List.ext_getElem (by simp [length_moveRecs])
  intro j h1 h2
  have hj : j < M := by simpa using h2
  simp [moveRecs, rotIdxFun_of_lt _ hj, blk_flatten l hl]

/-- A code-matching bijection preserves the count of each code. -/
private lemma idxCount_eq_of_perm {nd M : ℕ} (cin cout : ℕ → Fin nd) (π σ : ℕ → ℕ)
    (hπ : ∀ i < M, π i < M) (hσ : ∀ j < M, σ j < M) (hσπ : ∀ i < M, σ (π i) = i)
    (hπσ : ∀ j < M, π (σ j) = j) (hcode : ∀ i < M, cout (0 + π i) = cin (0 + i)) (d : Fin nd) :
    idxCount cout 0 M d = idxCount cin 0 M d := by
  unfold idxCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  have hperm : ((List.range M).map π).Perm (List.range M) := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.map_on ?_) List.nodup_range]
    · intro a
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hπ x hx
      · intro ha; exact ⟨σ a, hσ a ha, hπσ a ha⟩
    · intro x hx y hy hxy
      rw [List.mem_range] at hx hy
      rw [← hσπ x hx, ← hσπ y hy, hxy]
  rw [← hperm.countP_eq, List.countP_map]
  apply List.countP_congr
  intro x hx
  rw [List.mem_range] at hx
  have h := hcode x hx
  simp only [Nat.zero_add] at h
  simp [h]

end Lists

/-! ### The rotation as a merge -/

section Merge

variable {N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ : ℕ} (K ρ n : ℕ) (neg b : Bool)

/-- Index `i < M` is the rank of an address `p`, and the rotation sends it to the rank of the
rotated address. -/
private lemma idx_addr {i : ℕ} (h : i < rectSize N₀ N₁ N₂ N₃ L) :
    ∃ p : Addr N₀ N₁ N₂ N₃ L, rank N₀ N₁ N₂ N₃ L p = i ∧
      rotIdxFun (rankPerm N₀ N₁ N₂ N₃ L K ρ n [Instr.rot neg b]) i =
        rank N₀ N₁ N₂ N₃ L (rotAddr K ρ n neg b p) := by
  refine ⟨(rankEquiv N₀ N₁ N₂ N₃ L).symm ⟨i, h⟩, ?_, ?_⟩
  · rw [← rankEquiv_val, Equiv.apply_symm_apply]
  · rw [rotIdxFun_of_lt _ h, ← rankEquiv_val, ← rankPerm_rot, Equiv.apply_symm_apply]

variable (hK : 0 < K) (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃)
include hK hN₁ hN₂ hN₃

/-- Every record moves to an output index whose output code is its input code. -/
theorem rot_code : ∀ i < rectSize N₀ N₁ N₂ N₃ L,
    idxCode (outCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n))
        (0 + rotIdxFun (rankPerm N₀ N₁ N₂ N₃ L K ρ n [Instr.rot neg b]) i) =
      idxCode (inCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n)) (0 + i) := by
  intro i hi
  obtain ⟨p, rfl, hp⟩ := idx_addr K ρ n neg b hi
  rw [Nat.zero_add, Nat.zero_add, hp, outCode_rank K ρ n neg b hK hN₁ hN₂ hN₃,
    inCode_rank K ρ n neg b hK hN₁ hN₂ hN₃, wrapOut_rotAddr K ρ n neg b hK]

/-- Records of one input class keep their order. -/
theorem rot_mono : ∀ i < rectSize N₀ N₁ N₂ N₃ L, ∀ i' < rectSize N₀ N₁ N₂ N₃ L,
    idxCode (inCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n)) (0 + i) =
      idxCode (inCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n)) (0 + i') →
    i < i' → rotIdxFun (rankPerm N₀ N₁ N₂ N₃ L K ρ n [Instr.rot neg b]) i <
      rotIdxFun (rankPerm N₀ N₁ N₂ N₃ L K ρ n [Instr.rot neg b]) i' := by
  intro i hi i' hi' hc hlt
  obtain ⟨p, rfl, hp⟩ := idx_addr K ρ n neg b hi
  obtain ⟨q, rfl, hq⟩ := idx_addr K ρ n neg b hi'
  rw [Nat.zero_add, Nat.zero_add, inCode_rank K ρ n neg b hK hN₁ hN₂ hN₃,
    inCode_rank K ρ n neg b hK hN₁ hN₂ hN₃, rotCls_inj] at hc
  rw [hp, hq]
  exact rank_rotAddr_lt K ρ n neg b hK hlt hc

/-- Each output class has as many indices as the input class. -/
theorem rot_count (d : Fin 2) :
    idxCount (idxCode (outCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n))) 0
        (rectSize N₀ N₁ N₂ N₃ L) d =
      idxCount (idxCode (inCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n))) 0
        (rectSize N₀ N₁ N₂ N₃ L) d :=
  idxCount_eq_of_perm _ _ _ _ (fun _ h => rotIdxFun_lt _ h) (fun _ h => rotIdxFun_lt _ h)
    (fun _ h => rotIdxFun_symm _ h) (fun _ h => rotIdxFun_symm' _ h)
    (rot_code K ρ n neg b hK hN₁ hN₂ hN₃) d

/-- **List semantics of the pass.** Merging the input classes, routed in forward order, by the
output code gives the rotated stream and empties the classes. -/
theorem rot_merge {α : Type} {B : ℕ} (l : List (List α)) (hl : l.length = rectSize N₀ N₁ N₂ N₃ L)
    (hlB : ∀ r ∈ l, r.length = B) :
    mergeIdxList B (idxCode (outCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n)))
        (rectSize N₀ N₁ N₂ N₃ L) 0 (fun d => blocksIdx l.flatten B (rectSize N₀ N₁ N₂ N₃ L)
          (idxCode (inCode A neg b) L (rotLen n₀ n₁ n₂ n₃ L) (rotSrc (selMask K ρ n))) 0 d ++ []) =
      ((moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ n [Instr.rot neg b]) l).flatten, fun _ => []) := by
  rw [mergeIdxList_perm B _ l.flatten (by rw [length_flatten_of l hlB, hl]) _ _ 0 0 _ _
    (fun _ h => rotIdxFun_lt _ h) (fun _ h => rotIdxFun_lt _ h) (fun _ h => rotIdxFun_symm _ h)
    (fun _ h => rotIdxFun_symm' _ h) (rot_code K ρ n neg b hK hN₁ hN₂ hN₃)
    (rot_mono K ρ n neg b hK hN₁ hN₂ hN₃), flatten_moveRecs _ l hlB]

end Merge

private lemma length_flatten_moveRecs {α : Type} {M B : ℕ} (π : Equiv.Perm (Fin M))
    (l : List (List α))
    (hl : l.length = M) (hlB : ∀ r ∈ l, r.length = B) :
    (moveRecs π l).flatten.length = M * B := by
  rw [length_flatten_of _ (B := B), length_moveRecs]
  intro r hr
  simp only [moveRecs, List.mem_ofFn] at hr
  obtain ⟨j, rfl⟩ := hr
  have hj : (π.symm j : ℕ) < l.length := by rw [hl]; exact (π.symm j).isLt
  rw [List.getD_eq_getElem _ _ hj]
  exact hlB _ (List.getElem_mem hj)

/-! ### The pass on host registers -/

/-- Registers of the pass: the stream `src`; the record counter `ctr` (`B` symbols) with its
spare `tmp`; the record count `cnt` (`M` symbols) with its spare `ctmp`; the merge output `out`;
the class registers `dst d` and their reversals `aux d`; the counter fields `fld g`; the mask
parameter `prm`; the code-pass spares `spare r`. -/
inductive RotReg where
  | src | ctr | tmp | cnt | ctmp | out
  | dst (d : Fin 2) | aux (d : Fin 2)
  | fld (g : Fin 7) | prm | spare (r : Fin 4)
  deriving DecidableEq

/-- The index registers: the counter fields, the mask parameter and the code-pass spares. -/
def RotReg.isIdx : RotReg → Bool
  | .fld _ | .prm | .spare _ => true
  | _ => false

/-- The register of code-pass slot `r`: the fields of `c₀`, `c₁`, `c₂` and the mask. -/
def rsReg : Fin 4 → RotReg := ![.fld 5, .fld 3, .fld 1, .prm]

lemma rsReg_isIdx (r : Fin 4) : (rsReg r).isIdx = true := by
  fin_cases r <;> rfl

lemma rsReg_injective : Function.Injective rsReg := by
  intro r r' h
  fin_cases r <;> fin_cases r' <;> simp_all [rsReg]

section Machine

variable {T Q : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- The index layout of the pass beside any set `X` of non-index registers. -/
lemma rot_idxLayout {ι : RotReg → Fin T} (hι : Function.Injective ι) {st : Fin T}
    (hst : ∀ x, x.isIdx = true → ι x ≠ st) (L n₀ n₁ n₂ n₃ mask : ℕ) {X : Fin T → Prop}
    (hX : ∀ x, X (ι x) → x.isIdx = false) :
    IdxLayout (fun g => ι (.fld g)) (rotLen n₀ n₁ n₂ n₃ L) L (fun r => ι (rsReg r))
      (fun r => ι (.spare r)) (rotSrc mask) st X where
  rs_inj := hι.comp rsReg_injective
  tmps_inj := fun r r' h => by simpa using hι h
  rs_tmps := fun r r' h => by
    have := hι h
    fin_cases r <;> simp [rsReg] at this
  rs_st := fun r => hst _ (rsReg_isIdx r)
  tmps_st := fun r => hst _ rfl
  cf_inj := fun g g' h => by simpa using hι h
  tmps_cf := fun r g h => by simpa using hι h
  field := fun r g h => by
    fin_cases r <;> simp [rotSrc] at h <;> subst h <;> exact ⟨rfl, rfl⟩
  param := fun r p g h e => by
    have := hι e
    fin_cases r <;> simp [rotSrc, rsReg] at h this
  cf_X := fun g h => by simpa [RotReg.isIdx] using hX _ h
  rs_X := fun r h => by
    have := hX _ h
    rw [rsReg_isIdx] at this
    exact Bool.noConfusion this
  tmps_X := fun r h => by simpa [RotReg.isIdx] using hX _ h

/-- The index state at index `0`. -/
lemma rot_idxState {ι : RotReg → Fin T} (L n₀ n₁ n₂ n₃ mask : ℕ) (R : Fin T → List (Fin (A + 4)))
    (hf : ∀ g, R (ι (.fld g)) = binSyms (rotLen n₀ n₁ n₂ n₃ L g) 0)
    (hp : R (ι .prm) = binSyms L mask) (hs : ∀ r, R (ι (.spare r)) = []) :
    IdxState (fun g => ι (.fld g)) (rotLen n₀ n₁ n₂ n₃ L) L (fun r => ι (rsReg r))
      (fun r => ι (.spare r)) (rotSrc mask) R 0 := by
  refine ⟨fun g => by simp [digit, hf], fun r p h => ?_, hs⟩
  fin_cases r <;> simp [rotSrc] at h
  subst h
  exact hp

/-- The counter wraps after a whole rectangle. -/
lemma rotLen_digit_rect {N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ R : ℕ} (hN₀ : N₀ = R * 2 ^ n₀)
    (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (g : Fin 7) :
    digit (rotLen n₀ n₁ n₂ n₃ L) g (0 + rectSize N₀ N₁ N₂ N₃ L) = 0 := by
  rw [Nat.zero_add, ← digit_mod, rotLen_sum]
  have : rectSize N₀ N₁ N₂ N₃ L = R * 2 ^ (n₃ + 3 * L + n₂ + n₁ + n₀) := by
    subst hN₀ hN₁ hN₂ hN₃
    simp only [rectSize]
    ring
  rw [this, Nat.mul_mod_left]
  simp [digit]

private lemma idxCount_sum {nd : ℕ} (code : ℕ → Fin nd) :
    ∀ (m j : ℕ), ∑ d, idxCount code j m d = m := by
  intro m
  induction m with
  | zero => intro j; simp [idxCount]
  | succ m ih =>
    intro j
    simp only [idxCount_succ, Finset.sum_add_distrib, ih]
    rw [Finset.sum_ite_eq]
    simp [Nat.add_comm]

/-- **The pass of `Instr.rot neg b`.** Route the records of `src` by input class onto `dst 0`,
`dst 1`; reverse each onto `aux d`; merge them by output class onto `out`; move `out` back onto
`src`. Codes are computed on the counter fields `fld 5`, `fld 3`, `fld 1` (`c₀`, `c₁`, `c₂`) and
the mask register `prm`, with the carry in scan slot `st`. -/
def rotPass (neg b : Bool) (ι : RotReg → Fin T) (st : Fin T) : Pr P T Q A U :=
  .seq (routeIdx (ι .src) (fun d => ι (.dst d)) (ι .ctr) (ι .tmp) (fun g => ι (.fld g))
      (fun r => ι (rsReg r)) (fun r => ι (.spare r)) st (inCode A neg b))
    (.seq (revEach (fun d => ι (.dst d)) (fun d => ι (.aux d)))
      (.seq (mergeIdx (fun d => ι (.aux d)) (ι .out) (ι .ctr) (ι .tmp) (ι .cnt) (ι .ctmp)
          (fun g => ι (.fld g)) (fun r => ι (rsReg r)) (fun r => ι (.spare r)) st
          (outCode A neg b))
        (moveR (ι .out) (ι .src) id)))

/-- **The rotation pass, exact form.** Exactly
`M * (12 * B + 12 * L + 8 * (n₃ + 3 * L + n₂ + n₁ + n₀) + 84) + 13` steps,
`M = rectSize N₀ N₁ N₂ N₃ L`; see `rotPass_exec`. -/
theorem rotPass_exec_exact (neg b : Bool) {ι : RotReg → Fin T} (hι : Function.Injective ι)
    {st : Fin T} (hst : ∀ x, x.isIdx = true → ι x ≠ st)
    {N₀ N₁ N₂ N₃ L K ρ f n₀ n₁ n₂ n₃ R B : ℕ} (hK : 0 < K) (hN₀ : N₀ = R * 2 ^ n₀)
    (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (hB : 1 ≤ B)
    {l : List (List (Fin (A + 4)))} (hl : l.length = rectSize N₀ N₁ N₂ N₃ L)
    (hlB : ∀ r ∈ l, r.length = B) {c kk : List (Fin (A + 4))} (hcB : c.length = B)
    (hkk : kk.length = rectSize N₀ N₁ N₂ N₃ L) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (ι .src) = l.flatten) (hctr : S.R (ι .ctr) = c) (hcnt : S.R (ι .cnt) = kk)
    (htmp : S.R (ι .tmp) = []) (hctmp : S.R (ι .ctmp) = []) (hout : S.R (ι .out) = [])
    (hdst : ∀ d, S.R (ι (.dst d)) = []) (haux : ∀ d, S.R (ι (.aux d)) = [])
    (hfld : ∀ g, S.R (ι (.fld g)) = binSyms (rotLen n₀ n₁ n₂ n₃ L g) 0)
    (hprm : S.R (ι .prm) = binSyms L (selMask K ρ (f - 1)))
    (hspare : ∀ r, S.R (ι (.spare r)) = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (rotPass neg b ι st) (mk v S)
        (rectSize N₀ N₁ N₂ N₃ L * (12 * B + 12 * L + 8 * (n₃ + 3 * L + n₂ + n₁ + n₀) + 84) + 13)
        (mk v' { S with
          R := Function.update S.R (ι .src)
            (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) [Instr.rot neg b]) l).flatten }) := by
  set M := rectSize N₀ N₁ N₂ N₃ L with hM
  set len := rotLen n₀ n₁ n₂ n₃ L with hlen
  set mask := selMask K ρ (f - 1) with hmask
  set res := (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) [Instr.rot neg b]) l).flatten
    with hres
  have hw : l.flatten.length = M * B := by rw [length_flatten_of l hlB, hl]
  have hne : ∀ {x y : RotReg}, x ≠ y → ι x ≠ ι y := fun h => hι.ne h
  have hfld0 : ∀ g, binSyms (len g) (digit len g (0 + M)) =
      (binSyms (len g) 0 : List (Fin (A + 4))) :=
    fun g => by rw [rotLen_digit_rect hN₀ hN₁ hN₂ hN₃ g]
  -- routing
  have hXr : ∀ x, routeRegs (ι .src) (fun d => ι (.dst d)) (ι .ctr) (ι .tmp) (ι x) →
      x.isIdx = false := by
    intro x hx
    simp only [routeRegs, hι.eq_iff] at hx
    rcases hx with rfl | rfl | rfl | ⟨d, rfl⟩ <;> rfl
  obtain ⟨v₁, R₁, hu₁, he₁, hsrc₁, hdst₁, hfld₁, hoth₁⟩ :=
    routeIdx_exec body (ι .src) (fun d => ι (.dst d)) (ι .ctr) (ι .tmp) (fun g => ι (.fld g)) len
      L (fun r => ι (rsReg r)) (fun r => ι (.spare r)) (rotSrc mask) st (inCode A neg b)
      (rot_idxLayout hι hst L n₀ n₁ n₂ n₃ mask hXr) (by simp [hι.eq_iff])
      (fun d => by simp [hι.eq_iff]) (fun d d' h => by simpa using hι h) hB hw hcB v S hsrc hctr
      htmp (rot_idxState L n₀ n₁ n₂ n₃ mask S.R hfld hprm hspare)
  have hk₁ : ∀ x, x ≠ .src → (∀ d, x ≠ .dst d) → (∀ g, x ≠ .fld g) → R₁ (ι x) = S.R (ι x) :=
    fun x h1 h2 h3 => hoth₁ _ (hne h1) (fun d => hne (h2 d).symm) (fun g => hne (h3 g).symm)
  -- reversing
  obtain ⟨v₂, R₂, hu₂, he₂, hds₂, hoth₂⟩ := revList_exec body (fun d => ι (.dst d))
    (fun d => ι (.aux d)) (fun d d' h => by simpa using hι h) (fun d d' h => by simpa using hι h)
    (fun d d' h => by simpa using hι h) (List.finRange 2) (List.nodup_finRange 2) v₁
    { S with R := R₁ }
  have hk₂ : ∀ x, (∀ d, x ≠ .dst d) → (∀ d, x ≠ .aux d) → R₂ (ι x) = R₁ (ι x) :=
    fun x h1 h2 => hoth₂ _ (fun d _ => ⟨hne (h1 d), hne (h2 d)⟩)
  have hk₁₂ : ∀ x, x ≠ .src → (∀ d, x ≠ .dst d) → (∀ d, x ≠ .aux d) → (∀ g, x ≠ .fld g) →
      R₂ (ι x) = S.R (ι x) := fun x h1 h2 h3 h4 => (hk₂ x h2 h3).trans (hk₁ x h1 h2 h4)
  have haux₂ : ∀ d, R₂ (ι (.aux d)) =
      blocksIdx l.flatten B M (idxCode (inCode A neg b) L len (rotSrc mask)) 0 d ++ [] := by
    intro d
    rw [(hds₂ d (List.mem_finRange d)).2]
    show (R₁ (ι (.dst d))).reverse ++ R₁ (ι (.aux d)) = _
    rw [hdst₁, hdst, hk₁ _ (by simp) (by simp) (by simp), haux]
    simp
  have hI₂ : IdxState (fun g => ι (.fld g)) len L (fun r => ι (rsReg r)) (fun r => ι (.spare r))
      (rotSrc mask) R₂ 0 := by
    apply rot_idxState L n₀ n₁ n₂ n₃ mask R₂
    · intro g; rw [hk₂ _ (by simp) (by simp), hfld₁, hfld0]
    · rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp), hprm]
    · intro r; rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp), hspare]
  have hsum₂ : ((List.finRange 2).map fun d => 2 * ({ S with R := R₁ }.R (ι (.dst d))).length +
      2).sum = 2 * (M * B) + 4 := by
    simp only [hdst₁, hdst, List.append_nil, List.length_reverse]
    rw [← Fin.sum_univ_def, Fin.sum_univ_two, length_blocksIdx _ _ _ _ _ _ hw,
      length_blocksIdx _ _ _ _ _ _ hw]
    have := idxCount_sum (idxCode (inCode A neg b) L len (rotSrc mask)) M 0
    rw [Fin.sum_univ_two] at this
    have h2 : M * B = (idxCount (idxCode (inCode A neg b) L len (rotSrc mask)) 0 M 0 +
        idxCount (idxCode (inCode A neg b) L len (rotSrc mask)) 0 M 1) * B := by rw [this]
    rw [h2]
    ring
  -- merging
  have hXm : ∀ x, mergeRegs (fun d => ι (.aux d)) (ι .out) (ι .ctr) (ι .tmp) (ι .cnt) (ι .ctmp)
      (ι x) → x.isIdx = false := by
    intro x hx
    simp only [mergeRegs, hι.eq_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | ⟨d, rfl⟩ <;> rfl
  obtain ⟨v₃, R₃, hu₃, he₃, hout₃, haux₃, hfld₃, hoth₃⟩ :=
    mergeIdx_exec body (fun d => ι (.aux d)) (ι .out) (ι .ctr) (ι .tmp) (ι .cnt) (ι .ctmp)
      (fun g => ι (.fld g)) len L (fun r => ι (rsReg r)) (fun r => ι (.spare r)) (rotSrc mask) st
      (outCode A neg b) (rot_idxLayout hι hst L n₀ n₁ n₂ n₃ mask hXm) (by simp [hι.eq_iff])
      (fun d => by simp [hι.eq_iff]) (fun d d' h => by simpa using hι h) hcB hkk
      (fun d => blocksIdx l.flatten B M (idxCode (inCode A neg b) L len (rotSrc mask)) 0 d ++ [])
      (fun d => by
        rw [List.length_append, length_blocksIdx _ _ _ _ _ _ hw, List.length_nil, Nat.add_zero,
          rot_count K ρ (f - 1) neg b hK hN₁ hN₂ hN₃ d])
      v₂ { S with R := R₂ } haux₂
      (by show R₂ (ι .ctr) = c; rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp), hctr])
      (by show R₂ (ι .tmp) = []; rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp), htmp])
      (by show R₂ (ι .cnt) = kk; rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp), hcnt])
      (by show R₂ (ι .ctmp) = []; rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp), hctmp]) hI₂
  have hmerge := rot_merge K ρ (f - 1) neg b hK hN₁ hN₂ hN₃ l hl hlB (A := A) (n₀ := n₀)
  rw [hmerge] at hout₃ haux₃
  have hout₂ : R₂ (ι .out) = [] := by
    rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp), hout]
  have hsrc₂ : R₂ (ι .src) = [] := by rw [hk₂ _ (by simp) (by simp), hsrc₁]
  have hk₃ : ∀ x, x ≠ .out → (∀ d, x ≠ .aux d) → (∀ g, x ≠ .fld g) → R₃ (ι x) = R₂ (ι x) :=
    fun x h1 h2 h3 => hoth₃ _ (hne h1) (fun d => hne (h2 d).symm) (fun g => hne (h3 g).symm)
  have hout₃' : R₃ (ι .out) = res.reverse := by
    rw [hout₃]; show _ ++ R₂ (ι .out) = _; rw [hout₂, List.append_nil]
  have hsrc₃ : R₃ (ι .src) = [] := by rw [hk₃ _ (by simp) (by simp) (by simp), hsrc₂]
  -- moving back
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body (ι .out) (ι .src) (hne (by simp)) id v₃
    { S with R := R₃ }
  have hfin : movedR R₃ (ι .out) (ι .src) id (R₃ (ι .out)) =
      Function.update S.R (ι .src) res := by
    funext k
    by_cases hk1 : k = ι .src
    · subst hk1
      simp [movedR, hout₃', hsrc₃]
    by_cases hk2 : k = ι .out
    · subst hk2
      simp [movedR, hne (show RotReg.out ≠ .src by simp), hout]
    simp only [movedR, Function.update_of_ne hk1, Function.update_of_ne hk2]
    by_cases hk3 : ∃ d, k = ι (.aux d)
    · obtain ⟨d, rfl⟩ := hk3
      rw [haux₃, haux]
    by_cases hk4 : ∃ g, k = ι (.fld g)
    · obtain ⟨g, rfl⟩ := hk4
      rw [hfld₃, hfld0, hfld]
    simp only [not_exists] at hk3 hk4
    rw [hoth₃ k hk2 (fun d e => hk3 d e.symm) (fun g e => hk4 g e.symm)]
    show R₂ k = S.R k
    by_cases hk5 : ∃ d, k = ι (.dst d)
    · obtain ⟨d, rfl⟩ := hk5
      rw [(hds₂ d (List.mem_finRange d)).1, hdst]
    simp only [not_exists] at hk5
    rw [hoth₂ k (fun d _ => ⟨hk5 d, hk3 d⟩)]
    exact hoth₁ k hk1 (fun d e => hk5 d e.symm) (fun g e => hk4 g e.symm)
  refine ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂
    (Exec.seq he₃ he₄))) ?_ ?_⟩
  · rw [hsum₂]
    show _ + (_ + (_ + (2 * (R₃ (ι .out)).length + 2))) = _
    rw [hout₃', List.length_reverse, hres,
      length_flatten_moveRecs _ l hl hlB, rotLen_sum]
    ring
  · simp only [hfin]

/-- **The rotation pass.** Register `src` holds `l.flatten` for `M = rectSize N₀ N₁ N₂ N₃ L`
records of `B ≥ 1` symbols in rank order, with `N₀ = R 2^n₀`, `N₁ = 2^n₁`, `N₂ = 2^n₂`,
`N₃ = 2^n₃` and `K ≥ 1`; `ctr` holds `B` symbols and `cnt` holds `M`; the counter fields hold
zero, `prm` holds the mask `selMask K ρ (f - 1)`, and `tmp`, `ctmp`, `out`, `dst d`, `aux d` and
the code-pass spares are empty. Then `rotPass neg b` leaves
`(moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) [Instr.rot neg b]) l).flatten` on `src` in forward
order; every other stack, the counters, parameters and temporaries included, ends as it started,
and `user` is kept. At most `M * (12 * B + 12 * (n₃ + 3 * L + n₂ + n₁ + n₀) + 84) + 13` steps. -/
theorem rotPass_exec (neg b : Bool) {ι : RotReg → Fin T} (hι : Function.Injective ι)
    {st : Fin T} (hst : ∀ x, x.isIdx = true → ι x ≠ st)
    {N₀ N₁ N₂ N₃ L K ρ f n₀ n₁ n₂ n₃ R B : ℕ} (hK : 0 < K) (hN₀ : N₀ = R * 2 ^ n₀)
    (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (hB : 1 ≤ B)
    {l : List (List (Fin (A + 4)))} (hl : l.length = rectSize N₀ N₁ N₂ N₃ L)
    (hlB : ∀ r ∈ l, r.length = B) {c kk : List (Fin (A + 4))} (hcB : c.length = B)
    (hkk : kk.length = rectSize N₀ N₁ N₂ N₃ L) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (ι .src) = l.flatten) (hctr : S.R (ι .ctr) = c) (hcnt : S.R (ι .cnt) = kk)
    (htmp : S.R (ι .tmp) = []) (hctmp : S.R (ι .ctmp) = []) (hout : S.R (ι .out) = [])
    (hdst : ∀ d, S.R (ι (.dst d)) = []) (haux : ∀ d, S.R (ι (.aux d)) = [])
    (hfld : ∀ g, S.R (ι (.fld g)) = binSyms (rotLen n₀ n₁ n₂ n₃ L g) 0)
    (hprm : S.R (ι .prm) = binSyms L (selMask K ρ (f - 1)))
    (hspare : ∀ r, S.R (ι (.spare r)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ rectSize N₀ N₁ N₂ N₃ L * (12 * B + 12 * (n₃ + 3 * L + n₂ + n₁ + n₀) + 84) + 13 ∧
      Exec body (rotPass neg b ι st) (mk v S) m
        (mk v' { S with
          R := Function.update S.R (ι .src)
            (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) [Instr.rot neg b]) l).flatten }) := by
  obtain ⟨v', hu, he⟩ := rotPass_exec_exact body neg b hι hst hK hN₀ hN₁ hN₂ hN₃ hB hl hlB hcB
    hkk v S hsrc hctr hcnt htmp hctmp hout hdst haux hfld hprm hspare
  exact ⟨v', _, hu, Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 13, he⟩

end Machine

end IntegerMultBounds.MathlibTM2.Node
