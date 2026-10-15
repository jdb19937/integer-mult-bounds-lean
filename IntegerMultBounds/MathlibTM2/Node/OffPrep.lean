module

public import IntegerMultBounds.MathlibTM2.Node.RotGen
public import IntegerMultBounds.MathlibTM2.Node.Params

/-!
# Preparing a compact-control rotation offset

The rotations of the compact slot XOR (`IntegerMultBounds.MathlibTM2.Layer.CompactXor.core`)
use offsets of the form
`∑_{c<n} coef_c · 2^{o + c s}` with `coef_c = [z_c] · (2 w_c or 1)`, where `z_c` is a bit of a
control field (`a_c`, possibly XORed with a bit `y_c` of the target slot) and `w_c` a radix-`2^G`
digit of the temporary field. `prepOff useY useT` assembles such an offset on a host from the
counter fields of the control field `A` (bits at `oA + c sA`), the slot `Y` (bits at `ρ + cK`)
and the digit field `T` (digits at `cG`), writing `binSyms W off` into the computed register
`comp` and restoring everything else; its contract is the `Host.PrepSpec` of the rotation pass
(`prepOff_prepSpec`).

**Arithmetic.** `offSum coef o s n = ∑_{c<n} coef c · 2^{o + c s}`; with `coef c < 2^s` its bit
`o + c s + t`, `t < s`, is bit `t` of `coef c` (`testBit_offSum`). The four offsets of the
compact program are `offSum` of the uniform coefficient `coefU` (`offYW_eq`, `offYb_eq`,
`offBb_eq`, `offBx_eq`).

**Machine.** Positions are emitted least significant first onto the accumulator `w` against the
position counter `cnt` holding `W` ticks (`Node/Params.lean`, `emit`, `maskRegs`): `oO` zeros;
for each of `n` columns the control bit `z_c` read from the tops of the field registers after the
prefixes were moved to the scratch registers `tA`, `tY`, then the segment bits
`z_c ∧ ¬useT`, the `G` digit bits of `T` masked by `z_c ∧ useT`, and `pad = s - 1 - [useT] G`
zeros, the fields advancing by `sA`, `K` and `G`; `W` zeros of padding; the fields restored from
the scratch; `w` moved onto `comp`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer.CompactXor

/-! ### Sums of shifted coefficients -/

section OffSum

/-- `∑_{c<n} coef c · 2^{o + c s}`. -/
def offSum (coef : ℕ → ℕ) (o s n : ℕ) : ℕ := ∑ c ∈ Finset.range n, coef c * 2 ^ (o + c * s)

lemma offSum_succ (coef : ℕ → ℕ) (o s n : ℕ) :
    offSum coef o s (n + 1) = offSum coef o s n + coef n * 2 ^ (o + n * s) := by
  simp [offSum, Finset.sum_range_succ]

lemma offSum_lt (coef : ℕ → ℕ) (o s : ℕ) (hs : ∀ c, coef c < 2 ^ s) :
    ∀ n, offSum coef o s n < 2 ^ (o + n * s)
  | 0 => by simp [offSum]
  | n + 1 => by
    rw [offSum_succ]
    have ih := offSum_lt coef o s hs n
    have h1 := hs n
    have h2 : coef n * 2 ^ (o + n * s) ≤ (2 ^ s - 1) * 2 ^ (o + n * s) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : 2 ^ (o + (n + 1) * s) = 2 ^ s * 2 ^ (o + n * s) := by
      rw [← pow_add]; congr 1; ring
    have h4 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    rw [h3]
    have h5 : (2 ^ s - 1) * 2 ^ (o + n * s) + 2 ^ (o + n * s) = 2 ^ s * 2 ^ (o + n * s) := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel h4]
    omega

/-- Bit `t` of `offSum coef o s n`: for `t = o + c s + u`, `c < n`, `u < s`, bit `u` of `coef c`;
`false` below `o` and from `o + n s` on. -/
lemma testBit_offSum (coef : ℕ → ℕ) (o s : ℕ) (hs : ∀ c, coef c < 2 ^ s) (hs1 : 1 ≤ s) :
    ∀ n t, (offSum coef o s n).testBit t =
      if o ≤ t ∧ (t - o) / s < n then (coef ((t - o) / s)).testBit ((t - o) % s) else false
  | 0, t => by simp [offSum]
  | n + 1, t => by
    rw [offSum_succ, Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (offSum_lt coef o s hs n),
      testBit_offSum coef o s hs hs1 n t]
    by_cases ht : t < o + n * s
    · simp only [ht, ↓reduceIte]
      have key : (o ≤ t ∧ (t - o) / s < n) ↔ (o ≤ t ∧ (t - o) / s < n + 1) := by
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          apply Nat.div_lt_of_lt_mul
          rw [Nat.mul_comm]; omega
      simp only [key]
    · simp only [ht, ↓reduceIte]
      rw [not_lt] at ht
      have hq : (t - o) / s ≥ n := by
        apply (Nat.le_div_iff_mul_le hs1).mpr
        omega
      by_cases h1 : (t - o) / s < n + 1
      · have hq' : (t - o) / s = n := by omega
        have hr : (t - o) % s = t - (o + n * s) := by
          have := Nat.mod_add_div (t - o) s
          rw [hq', Nat.mul_comm] at this
          omega
        have h2 : o ≤ t ∧ (t - o) / s < n + 1 := ⟨by omega, h1⟩
        rw [if_pos h2, hq', hr]
      · have h2 : ¬ (o ≤ t ∧ (t - o) / s < n + 1) := fun h => h1 h.2
        rw [if_neg h2]
        apply Nat.testBit_eq_false_of_lt
        calc coef n < 2 ^ s := hs n
          _ ≤ 2 ^ (t - (o + n * s)) := by
            apply Nat.pow_le_pow_right (by norm_num)
            have : n + 1 ≤ (t - o) / s := by omega
            have := (Nat.le_div_iff_mul_le hs1).mp this
            rw [Nat.add_mul, one_mul] at this
            omega

end OffSum

/-! ### The uniform coefficient of the compact-control offsets -/

section Coef

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- The control bit of column `c`: the bit of `A` at `oA + c sA`, XORed with the bit of `Y` at
`ρ + cK` when `useY`. -/
def ctrlBit (useY : Bool) (A Y : Fin nf) (oA sA ρ K c i : ℕ) : Bool :=
  xor (bitAt len A oA sA c i) (useY && bitAt len Y ρ K c i)

/-- The coefficient of column `c`: the control bit, times `2 w_c` (digit `c` of `T`) when
`useT`. -/
def coefU (useY useT : Bool) (A Y T : Fin nf) (oA sA ρ K G c i : ℕ) : ℕ :=
  b2n (ctrlBit len useY A Y oA sA ρ K c i) * (if useT then 2 * digAt len G T c i else 1)

lemma coefU_lt (useY useT : Bool) (A Y T : Fin nf) (oA sA ρ K G c i s : ℕ)
    (hs : (if useT then G + 1 else 1) ≤ s) :
    coefU len useY useT A Y T oA sA ρ K G c i < 2 ^ s := by
  unfold coefU
  have hb := b2n_le_one (ctrlBit len useY A Y oA sA ρ K c i)
  have hd := digAt_lt len G T c i
  cases useT
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    have hs' : s ≠ 0 := by simp at hs; omega
    calc _ ≤ 1 := hb
      _ < 2 ^ s := Nat.one_lt_two_pow_iff.mpr hs'
  · simp only [↓reduceIte]
    have : 2 * digAt len G T c i < 2 ^ (G + 1) := by rw [pow_succ]; omega
    calc _ ≤ 1 * (2 * digAt len G T c i) := Nat.mul_le_mul_right _ hb
      _ < 2 ^ (G + 1) := by rw [one_mul]; exact this
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by simpa using hs)

lemma offYW_eq {T : Fin nf} {K ρ G n : ℕ} (A Y : Fin nf) (oA sA i : ℕ) :
    offYW len T K ρ G n A oA sA i = offSum (fun c => coefU len false true A Y T oA sA ρ K G c i) ρ K n := by
  unfold offYW offSum coefU ctrlBit
  apply Finset.sum_congr rfl
  intro c _
  simp [b2n]

lemma offYb_eq {K ρ n : ℕ} (A Y T : Fin nf) (oA sA G i : ℕ) :
    offYb len K ρ n A oA sA i = offSum (fun c => coefU len false false A Y T oA sA ρ K G c i) ρ K n := by
  unfold offYb offSum coefU ctrlBit
  apply Finset.sum_congr rfl
  intro c _
  simp [b2n]

lemma offBb_eq {G n : ℕ} (A Y T : Fin nf) (oA sA ρ K i : ℕ) :
    offBb len G n A oA sA i = offSum (fun c => coefU len false false A Y T oA sA ρ K G c i) 0 G n := by
  unfold offBb offSum coefU ctrlBit
  apply Finset.sum_congr rfl
  intro c _
  simp [b2n]

lemma offBx_eq {Y : Fin nf} {K ρ G n : ℕ} (A T : Fin nf) (oA sA i : ℕ) :
    offBx len Y K ρ G n A oA sA i = offSum (fun c => coefU len true false A Y T oA sA ρ K G c i) 0 G n := by
  unfold offBx offSum coefU ctrlBit
  apply Finset.sum_congr rfl
  intro c _
  simp only [Bool.true_and, mul_one, Nat.zero_add]
  congr 2
  cases bitAt len Y ρ K c i <;> cases bitAt len A oA sA c i <;> rfl

end Coef


/-! ### Bits of the uniform coefficient -/

section CoefBits

variable {nf : ℕ} (len : Fin nf → ℕ)

lemma b2n_mul_testBit (b : Bool) (m t : ℕ) : (b2n b * m).testBit t = (b && m.testBit t) := by
  cases b <;> simp [b2n]

lemma coefU_testBit_zero (useY useT : Bool) (A Y T : Fin nf) (oA sA ρ K G c i : ℕ) :
    (coefU len useY useT A Y T oA sA ρ K G c i).testBit 0 =
      (ctrlBit len useY A Y oA sA ρ K c i && !useT) := by
  unfold coefU
  rw [b2n_mul_testBit]
  cases useT
  · simp
  · simp [Nat.testBit_zero]

lemma coefU_testBit_succ (useY : Bool) (A Y T : Fin nf) (oA sA ρ K G c i m : ℕ) :
    (coefU len useY true A Y T oA sA ρ K G c i).testBit (m + 1) =
      (ctrlBit len useY A Y oA sA ρ K c i && (digAt len G T c i).testBit m) := by
  unfold coefU
  rw [b2n_mul_testBit]
  simp only [↓reduceIte]
  congr 1
  rw [Nat.testBit_succ, Nat.mul_div_cancel_left _ (by norm_num)]

lemma coefU_testBit_false (useY : Bool) (A Y T : Fin nf) (oA sA ρ K G c i m : ℕ)
    (hm : m ≥ 1) : (coefU len useY false A Y T oA sA ρ K G c i).testBit m = false := by
  apply Nat.testBit_eq_false_of_lt
  unfold coefU
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
  calc _ ≤ 1 := b2n_le_one _
    _ < 2 ^ m := Nat.one_lt_two_pow_iff.mpr (by omega)

lemma coefU_testBit_high (useY : Bool) (A Y T : Fin nf) (oA sA ρ K G c i m : ℕ)
    (hm : m ≥ G + 1) : (coefU len useY true A Y T oA sA ρ K G c i).testBit m = false := by
  apply Nat.testBit_eq_false_of_lt
  calc _ < 2 ^ (G + 1) := coefU_lt len useY true A Y T oA sA ρ K G c i (G + 1) (by simp)
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

/-- The digit `c` of `T` is read bit by bit from the field register. -/
lemma digAt_testBit (D : Fin nf) (G c i m : ℕ) (hm : m < G) :
    (digAt len G D c i).testBit m = (dig len D i).testBit (c * G + m) := by
  unfold digAt
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hm, Nat.add_comm]

end CoefBits

/-! ### The program -/

/-- The registers of the preparation: the three field registers and the computed register of
the rotation pass, nine unary parameter registers, and eight scratch registers. -/
inductive PReg where
  | cfA | cfY | cfT | comp
  | WR | oOR | oAR | oYR | sAR | KR | GR | nR | padR
  | cnt | w | t₁ | t₂ | tA | tY | tT | cb
  deriving DecidableEq

/-- The parameters of one preparation: the output width `W`, the output offset `oO`, the field
offsets `oA`, `oY`, the strides `sA`, `K`, `G`, the column count `n`, the padding `pad`, and the
three field contents `xA`, `xY`, `xT` with their widths. -/
structure PData where
  W : ℕ
  oO : ℕ
  oA : ℕ
  oY : ℕ
  sA : ℕ
  K : ℕ
  G : ℕ
  n : ℕ
  pad : ℕ
  lA : ℕ
  xA : ℕ
  lY : ℕ
  xY : ℕ
  lT : ℕ
  xT : ℕ

namespace PData

variable (useY useT : Bool) (d : PData)

/-- The control bit of column `c`. -/
def ctrl (c : ℕ) : Bool := xor (d.xA.testBit (d.oA + c * d.sA)) (useY && d.xY.testBit (d.oY + c * d.K))

/-- Digit `c` of the temporary field. -/
def digit (c : ℕ) : ℕ := d.xT / 2 ^ (c * d.G) % 2 ^ d.G

/-- The coefficient of column `c`. -/
def coef (c : ℕ) : ℕ := b2n (ctrl useY d c) * (if useT then 2 * digit d c else 1)

/-- The output stride: one segment bit, `G` digit bits when `useT`, and `pad` zeros. -/
def sO : ℕ := 1 + (if useT then d.G else 0) + d.pad

/-- The prepared offset. -/
def X : ℕ := offSum (coef useY useT d) d.oO (sO useT d) d.n

lemma digit_lt (c : ℕ) : digit d c < 2 ^ d.G := Nat.mod_lt _ (by positivity)

lemma coef_lt (c : ℕ) : coef useY useT d c < 2 ^ sO useT d := by
  unfold coef sO
  have hb := b2n_le_one (ctrl useY d c)
  have hd := digit_lt d c
  cases useT
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one, Nat.add_zero]
    calc _ ≤ 1 := hb
      _ < 2 ^ (1 + d.pad) := Nat.one_lt_two_pow_iff.mpr (by omega)
  · simp only [↓reduceIte]
    have : 2 * digit d c < 2 ^ (d.G + 1) := by rw [pow_succ]; omega
    calc _ ≤ 1 * (2 * digit d c) := Nat.mul_le_mul_right _ hb
      _ < 2 ^ (d.G + 1) := by rw [one_mul]; exact this
      _ ≤ 2 ^ (1 + d.G + d.pad) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma coef_testBit_zero (c : ℕ) : (coef useY useT d c).testBit 0 = (ctrl useY d c && !useT) := by
  unfold coef
  rw [b2n_mul_testBit]
  cases useT
  · simp
  · simp [Nat.testBit_zero]

lemma coef_testBit_succ (c m : ℕ) :
    (coef useY true d c).testBit (m + 1) = (ctrl useY d c && (digit d c).testBit m) := by
  unfold coef
  rw [b2n_mul_testBit]
  simp only [↓reduceIte]
  congr 1
  rw [Nat.testBit_succ, Nat.mul_div_cancel_left _ (by norm_num)]

lemma coef_testBit_high (c m : ℕ) (hm : m ≥ 1 + (if useT then d.G else 0)) :
    (coef useY useT d c).testBit m = false := by
  apply Nat.testBit_eq_false_of_lt
  unfold coef
  have hb := b2n_le_one (ctrl useY d c)
  have hd := digit_lt d c
  cases useT
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hm ⊢
    calc _ ≤ 1 := hb
      _ < 2 ^ m := Nat.one_lt_two_pow_iff.mpr (by omega)
  · simp only [↓reduceIte] at hm ⊢
    have : 2 * digit d c < 2 ^ (d.G + 1) := by rw [pow_succ]; omega
    calc _ ≤ 1 * (2 * digit d c) := Nat.mul_le_mul_right _ hb
      _ < 2 ^ (d.G + 1) := by rw [one_mul]; exact this
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma digit_testBit (c m : ℕ) (hm : m < d.G) :
    (digit d c).testBit m = d.xT.testBit (c * d.G + m) := by
  unfold digit
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hm, Nat.add_comm]

/-- Bit `p` of the offset inside column `c`. -/
lemma X_testBit_col (c : ℕ) (hc : c < d.n) (u : ℕ) (hu : u < sO useT d) :
    (X useY useT d).testBit (d.oO + c * sO useT d + u) = (coef useY useT d c).testBit u := by
  unfold X
  rw [testBit_offSum _ _ _ (coef_lt useY useT d) (by unfold sO; omega)]
  have h1 : d.oO ≤ d.oO + c * sO useT d + u := by omega
  have h2 : (d.oO + c * sO useT d + u - d.oO) / sO useT d = c := by
    rw [show d.oO + c * sO useT d + u - d.oO = c * sO useT d + u by omega,
      Nat.mul_comm, Nat.mul_add_div (by unfold sO; omega), Nat.div_eq_of_lt hu, Nat.add_zero]
  have h3 : (d.oO + c * sO useT d + u - d.oO) % sO useT d = u := by
    rw [show d.oO + c * sO useT d + u - d.oO = c * sO useT d + u by omega,
      Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
  rw [if_pos ⟨h1, by rw [h2]; exact hc⟩, h2, h3]

/-- Bits below the output offset are zero. -/
lemma X_testBit_lo (q : ℕ) (hq : q < d.oO) : (X useY useT d).testBit q = false := by
  unfold X
  rw [testBit_offSum _ _ _ (coef_lt useY useT d) (by unfold sO; omega)]
  rw [if_neg (by omega)]

/-- Bits from the end of the last column on are zero. -/
lemma X_testBit_hi (q : ℕ) (hq : d.oO + d.n * sO useT d ≤ q) : (X useY useT d).testBit q = false := by
  unfold X
  rw [testBit_offSum _ _ _ (coef_lt useY useT d) (by unfold sO; omega)]
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have : d.n ≤ (q - d.oO) / sO useT d := by
    apply (Nat.le_div_iff_mul_le (by unfold sO; omega)).mpr
    omega
  omega

end PData

section Program

variable {T Q A : ℕ} {U P : Type}

/-- Store the bit `b` in scan slot `sb`. -/
def setScan (sb : Fin T) (b : Bool) (v : HS T Q A U) : HS T Q A U :=
  { v with scan := Function.update v.scan sb (bitSymbol b) }

/-- The bit held by the top of a register (`false` when empty). -/
def isTick (o : Option (Fin (A + 4))) : Bool := (o.map symBit).getD false

/-- Read the control bit of the current column from the tops of `cfA` and `cfY` and push it onto
the empty register `cb`. -/
def readBit (useY : Bool) (ι : PReg → Fin T) : Act T Q A U :=
  .peek (.rt (ι .cfA)) (fun v o => setScan (ι .cb) (isTick o) v)
    (.peek (.rt (ι .cfY)) (fun v o =>
      setScan (ι .cb) (xor (symBit (v.scan (ι .cb))) (useY && isTick o)) v)
      (.push (.rt (ι .cb)) (fun v => v.scan (ι .cb)) .done))

/-- Emit one position with the bit `g (control bit) sym`, the control bit read from `cb`. -/
def emitD (ι : PReg → Fin T) (g : Bool → Option (Fin (A + 4)) → Bool) (k : Act T Q A U) :
    Act T Q A U :=
  .peek (.rt (ι .cb)) (fun v o => setScan (ι .cb) (isTick o) v)
    (.pop (.rt (ι .cnt)) (fun v o => { v with flag := o.isSome })
      (.branch (·.flag)
        (.push (.rt (ι .w)) (fun v => bitSymbol (g (symBit (v.scan (ι .cb))) v.sym)) k) k))

/-- One digit bit: pop `cfT` onto `tT` and emit the popped bit masked by the control bit. -/
def digitStep (ι : PReg → Fin T) : Act T Q A U :=
  .pop (.rt (ι .cfT)) (fun v o => { v with sym := o })
    (.push (.rt (ι .tT)) (fun v => v.sym.getD blank)
      (emitD ι (fun b sy => b && symBit (sy.getD blank)) .done))

/-- Clear the control-bit register. -/
def clearCb (ι : PReg → Fin T) : Act T Q A U := .pop (.rt (ι .cb)) (fun v _ => v) .done

/-- One column: the control bit; the segment bit `0`; the `G` digit bits of `T` when `useT`;
`pad` zeros; the fields `A` and `Y` advance by `sA` and `K`; the control bit is cleared. -/
def column (useY useT : Bool) (ι : PReg → Fin T) : Pr P T Q A U :=
  .seq (.act (readBit useY ι))
    (.seq (.act (emitD ι (fun b _ => b && !useT) .done))
      (.seq (if useT then scanP (ι .GR) (ι .t₂) (.act (digitStep ι)) else .act .done)
        (.seq (scanR (ι .padR) (ι .t₂) (emit (ι .cnt) (ι .w) false))
          (.seq (scanP (ι .sAR) (ι .t₂) (.act (popPush (ι .cfA) (ι .tA))))
            (.seq (scanP (ι .KR) (ι .t₂) (.act (popPush (ι .cfY) (ι .tY))))
              (.act (clearCb ι)))))))

/-- The offset preparation. -/
def prepOff (useY useT : Bool) (ι : PReg → Fin T) : Pr P T Q A U :=
  .seq (uclear (ι .comp))
    (.seq (ucopy (ι .WR) (ι .cnt) (ι .t₁))
      (.seq (scanR (ι .oOR) (ι .t₁) (emit (ι .cnt) (ι .w) false))
        (.seq (scanP (ι .oAR) (ι .t₁) (.act (popPush (ι .cfA) (ι .tA))))
          (.seq (scanP (ι .oYR) (ι .t₁) (.act (popPush (ι .cfY) (ι .tY))))
            (.seq (scanP (ι .nR) (ι .t₁) (column useY useT ι))
              (.seq (scanR (ι .WR) (ι .t₁) (emit (ι .cnt) (ι .w) false))
                (.seq (moveR (ι .tA) (ι .cfA) id)
                  (.seq (moveR (ι .tY) (ι .cfY) id)
                    (.seq (moveR (ι .tT) (ι .cfT) id) (moveR (ι .w) (ι .comp) id))))))))))

/-! ### Single steps -/

variable (body : P → Pr P T Q A U)

lemma readBit_run (useY : Bool) (ι : PReg → Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (readBit useY ι : Act T Q A U).run (mk v S) =
      mk (setScan (ι .cb) (xor (isTick (S.R (ι .cfA)).head?) (useY && isTick (S.R (ι .cfY)).head?)) v)
        { S with
          R := Function.update S.R (ι .cb)
            (bitSymbol (xor (isTick (S.R (ι .cfA)).head?) (useY && isTick (S.R (ι .cfY)).head?)) ::
              S.R (ι .cb)) } := by
  simp [readBit, Action.run, setScan, Function.update_idem, update_rt]

lemma emitD_run {ι : PReg → Fin T} (hι : Function.Injective ι)
    (g : Bool → Option (Fin (A + 4)) → Bool) (k : Act T Q A U) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.sym = v.sym ∧
      (emitD ι g k).run (mk v S) =
        k.run (mk v' { S with R := emitFx (ι .cnt) (ι .w) (g (isTick (S.R (ι .cb)).head?) v.sym) S.R }) := by
  have hcw : ι .cnt ≠ ι .w := hι.ne (by decide)
  by_cases h : S.R (ι .cnt) = []
  · refine ⟨{ (setScan (ι .cb) (isTick (S.R (ι .cb)).head?) v) with flag := false }, rfl, rfl, ?_⟩
    have h' : Function.update S.R (ι .cnt) [] = S.R := by rw [← h, Function.update_eq_self]
    simp [emitD, Action.run, h, update_rt, emitFx, h', setScan]
  · obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil h
    refine ⟨{ (setScan (ι .cb) (isTick (S.R (ι .cb)).head?) v) with flag := true }, rfl, rfl, ?_⟩
    simp [emitD, Action.run, hy, update_rt, emitFx, Function.update_of_ne hcw.symm, setScan]

/-- The top of a field register after `k` pops. -/
lemma head_drop_binSyms (L x k : ℕ) (hk : k < L) :
    ((binSyms L x : List (Fin (A + 4))).drop k).head? = some (bitSymbol (x.testBit k)) := by
  rw [List.head?_drop]
  simp [binSyms, hk]

lemma head_drop_binSyms_ge (L x k : ℕ) (hk : L ≤ k) :
    ((binSyms L x : List (Fin (A + 4))).drop k).head? = none := by
  rw [List.head?_drop]
  simp [binSyms, not_lt.mpr hk]

lemma isTick_head (L x k : ℕ) (hx : x < 2 ^ L) :
    isTick (((binSyms L x : List (Fin (A + 4))).drop k).head?) = x.testBit k := by
  by_cases hk : k < L
  · rw [head_drop_binSyms L x k hk]
    simp [isTick]
  · rw [head_drop_binSyms_ge L x k (not_lt.mp hk)]
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
      (not_lt.mp hk)))]
    simp [isTick]

/-- The registers after popping position `k` of the field `binSyms L x` from `a` onto `t`. -/
def popFieldFx (R : Regs T A) (a t : Fin T) (L x k : ℕ) : Regs T A :=
  Function.update (Function.update R a ((binSyms L x : List (Fin (A + 4))).drop (k + 1))) t
    ((binSyms L x : List (Fin (A + 4))).take (k + 1)).reverse

lemma popFieldFx_ne {R : Regs T A} {a t k : Fin T} (hka : k ≠ a) (hkt : k ≠ t) (L x j : ℕ) :
    popFieldFx R a t L x j k = R k := by
  simp [popFieldFx, Function.update_of_ne hka, Function.update_of_ne hkt]

lemma emitFx_ne {R : Regs T A} {cnt w k : Fin T} (hkc : k ≠ cnt) (hkw : k ≠ w) (b : Bool) :
    emitFx cnt w b R k = R k := by
  unfold emitFx
  split_ifs
  · rfl
  · simp [Function.update_of_ne hkc, Function.update_of_ne hkw]

/-- Popping position `k` of a field onto its scratch register. -/
lemma popPush_run {a t : Fin T} (hat : a ≠ t) (L x k : ℕ) (hk : k < L) (v : HS T Q A U)
    (S : Stacks T A) (ha : S.R a = (binSyms L x : List (Fin (A + 4))).drop k)
    (ht : S.R t = ((binSyms L x : List (Fin (A + 4))).take k).reverse) :
    (popPush a t : Act T Q A U).run (mk v S) =
      mk { v with sym := some (bitSymbol (x.testBit k)) } { S with R := popFieldFx S.R a t L x k } := by
  have hhead := head_drop_binSyms (A := A) L x k hk
  have htail : ((binSyms L x : List (Fin (A + 4))).drop k).tail =
      (binSyms L x : List (Fin (A + 4))).drop (k + 1) := by
    rw [List.tail_drop]
  have htake : ((binSyms L x : List (Fin (A + 4))).take (k + 1)).reverse =
      bitSymbol (x.testBit k) :: ((binSyms L x : List (Fin (A + 4))).take k).reverse := by
    rw [List.take_succ, List.reverse_append]
    have : (binSyms L x : List (Fin (A + 4)))[k]? = some (bitSymbol (x.testBit k)) := by
      simp [binSyms, hk]
    rw [this]
    rfl
  simp only [popPush, Action.run, mk_var, mk_stk, get_rt, ha, hhead, Option.getD_some, update_rt,
    store_mk, htail, popFieldFx]
  rw [Function.update_of_ne hat.symm, ht, htake]

end Program

/-! ### Register files indexed by names -/

section RegsOf

variable {T A : ℕ} {ι : PReg → Fin T}

open Classical in
/-- The register file that holds `tbl x` in register `ι x` and `R₀ k` elsewhere. -/
noncomputable def regsOf (ι : PReg → Fin T) (R₀ : Regs T A) (tbl : PReg → List (Fin (A + 4))) :
    Regs T A :=
  fun k => if h : ∃ x, ι x = k then tbl h.choose else R₀ k

variable (hι : Function.Injective ι)
include hι

lemma regsOf_apply (R₀ : Regs T A) (tbl : PReg → List (Fin (A + 4))) (x : PReg) :
    regsOf ι R₀ tbl (ι x) = tbl x := by
  have h : ∃ y, ι y = ι x := ⟨x, rfl⟩
  unfold regsOf
  rw [dif_pos h]
  congr 1
  exact hι h.choose_spec

lemma regsOf_ne (R₀ : Regs T A) (tbl : PReg → List (Fin (A + 4))) {k : Fin T}
    (hk : ∀ x, ι x ≠ k) : regsOf ι R₀ tbl k = R₀ k := by
  have h : ¬ ∃ x, ι x = k := fun ⟨x, hx⟩ => hk x hx
  unfold regsOf
  rw [dif_neg h]

lemma update_regsOf (R₀ : Regs T A) (tbl : PReg → List (Fin (A + 4))) (x : PReg)
    (l : List (Fin (A + 4))) :
    Function.update (regsOf ι R₀ tbl) (ι x) l = regsOf ι R₀ (Function.update tbl x l) := by
  funext k
  by_cases hk : ∃ y, ι y = k
  · obtain ⟨y, rfl⟩ := hk
    rw [regsOf_apply hι]
    by_cases hxy : y = x
    · subst hxy; simp
    · rw [Function.update_of_ne (hι.ne hxy), Function.update_of_ne hxy, regsOf_apply hι]
  · have hk' : ∀ y, ι y ≠ k := fun y hy => hk ⟨y, hy⟩
    rw [Function.update_of_ne (hk' x).symm, regsOf_ne hι _ _ hk', regsOf_ne hι _ _ hk']

omit hι in
lemma regsOf_congr (R₀ : Regs T A) {tbl tbl' : PReg → List (Fin (A + 4))} (h : tbl = tbl') :
    regsOf ι R₀ tbl = regsOf ι R₀ tbl' := by rw [h]

end RegsOf

/-! ### The register state of the preparation -/

section State

variable {T A : ℕ} (ι : PReg → Fin T) (useY useT : Bool) (d : PData) (R₀ : Regs T A)

/-- The table of the preparation after `kA`, `kY`, `kT` pops of the three fields, `p` emitted
positions, with the control-bit register holding `cbl`. -/
def ptbl (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) : PReg → List (Fin (A + 4))
  | .cfA => (binSyms d.lA d.xA : List (Fin (A + 4))).drop kA
  | .tA => ((binSyms d.lA d.xA : List (Fin (A + 4))).take kA).reverse
  | .cfY => (binSyms d.lY d.xY : List (Fin (A + 4))).drop kY
  | .tY => ((binSyms d.lY d.xY : List (Fin (A + 4))).take kY).reverse
  | .cfT => (binSyms d.lT d.xT : List (Fin (A + 4))).drop kT
  | .tT => ((binSyms d.lT d.xT : List (Fin (A + 4))).take kT).reverse
  | .cnt => List.replicate (d.W - p) tick
  | .w => (binSyms (min p d.W) (PData.X useY useT d) : List (Fin (A + 4))).reverse
  | .cb => cbl
  | x => R₀ (ι x)

/-- The register file of the preparation. -/
noncomputable def pst (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) : Regs T A :=
  regsOf ι R₀ (ptbl ι useY useT d R₀ kA kY kT p cbl)

variable {ι} (hι : Function.Injective ι)
include hι

lemma pst_apply (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) (x : PReg) :
    pst ι useY useT d R₀ kA kY kT p cbl (ι x) = ptbl ι useY useT d R₀ kA kY kT p cbl x :=
  regsOf_apply hι _ _ x

lemma pst_ne (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) {k : Fin T} (hk : ∀ x, ι x ≠ k) :
    pst ι useY useT d R₀ kA kY kT p cbl k = R₀ k :=
  regsOf_ne hι _ _ hk

/-- Advancing the field `A` by one position. -/
lemma pst_popA (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) :
    popFieldFx (pst ι useY useT d R₀ kA kY kT p cbl) (ι .cfA) (ι .tA) d.lA d.xA kA =
      pst ι useY useT d R₀ (kA + 1) kY kT p cbl := by
  unfold popFieldFx pst
  rw [update_regsOf hι, update_regsOf hι]
  apply regsOf_congr
  funext x
  cases x <;> simp [ptbl, Function.update_of_ne]

/-- Advancing the field `Y` by one position. -/
lemma pst_popY (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) :
    popFieldFx (pst ι useY useT d R₀ kA kY kT p cbl) (ι .cfY) (ι .tY) d.lY d.xY kY =
      pst ι useY useT d R₀ kA (kY + 1) kT p cbl := by
  unfold popFieldFx pst
  rw [update_regsOf hι, update_regsOf hι]
  apply regsOf_congr
  funext x
  cases x <;> simp [ptbl, Function.update_of_ne]

/-- Advancing the field `T` by one position. -/
lemma pst_popT (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) :
    popFieldFx (pst ι useY useT d R₀ kA kY kT p cbl) (ι .cfT) (ι .tT) d.lT d.xT kT =
      pst ι useY useT d R₀ kA kY (kT + 1) p cbl := by
  unfold popFieldFx pst
  rw [update_regsOf hι, update_regsOf hι]
  apply regsOf_congr
  funext x
  cases x <;> simp [ptbl, Function.update_of_ne]

/-- Emitting one position whose bit agrees with the offset. -/
lemma pst_emit (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) {b : Bool}
    (hb : p < d.W → (PData.X useY useT d).testBit p = b) :
    emitFx (ι .cnt) (ι .w) b (pst ι useY useT d R₀ kA kY kT p cbl) =
      pst ι useY useT d R₀ kA kY kT (p + 1) cbl := by
  have hcnt : pst ι useY useT d R₀ kA kY kT p cbl (ι .cnt) = List.replicate (d.W - p) tick :=
    pst_apply useY useT d R₀ hι kA kY kT p cbl .cnt
  have hw : pst ι useY useT d R₀ kA kY kT p cbl (ι .w) =
      (binSyms (min p d.W) (PData.X useY useT d) : List (Fin (A + 4))).reverse :=
    pst_apply useY useT d R₀ hι kA kY kT p cbl .w
  by_cases hp : p < d.W
  · have hc : pst ι useY useT d R₀ kA kY kT p cbl (ι .cnt) =
        tick :: List.replicate (d.W - (p + 1)) tick := by
      rw [hcnt, show d.W - p = d.W - (p + 1) + 1 by omega, List.replicate_succ]
    simp only [emitFx, hc, reduceCtorEq, ↓reduceIte, List.tail_cons, hw]
    unfold pst
    rw [update_regsOf hι, update_regsOf hι]
    apply regsOf_congr
    funext x
    cases x <;> simp [ptbl, Function.update_of_ne]
    rw [show min (p + 1) d.W = p + 1 by omega, show min p d.W = p by omega, binSyms_succ', hb hp]
    simp
  · have hc : pst ι useY useT d R₀ kA kY kT p cbl (ι .cnt) = [] := by
      rw [hcnt, show d.W - p = 0 by omega, List.replicate_zero]
    simp only [emitFx, hc, ↓reduceIte]
    unfold pst
    apply regsOf_congr
    funext x
    cases x <;> simp [ptbl]
    · rw [show d.W - p = d.W - (p + 1) by omega]
    · rw [show min p d.W = min (p + 1) d.W by omega]

/-- Pushing the control bit. -/
lemma pst_pushCb (kA kY kT p : ℕ) (b : Bool) :
    Function.update (pst ι useY useT d R₀ kA kY kT p []) (ι .cb) (bitSymbol b :: []) =
      pst ι useY useT d R₀ kA kY kT p [bitSymbol b] := by
  unfold pst
  rw [update_regsOf hι]
  apply regsOf_congr
  funext x
  cases x <;> simp [ptbl, Function.update_of_ne]

end State


/-! ### The loops of the preparation -/

section Loops

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U) {ι : PReg → Fin T}
  (hι : Function.Injective ι) (useY useT : Bool) (d : PData) (R₀ : Regs T A)
include hι

/-- The control-bit register is set or cleared independently of the rest. -/
lemma pst_setCb (kA kY kT p : ℕ) (cbl cbl' : List (Fin (A + 4))) :
    Function.update (pst ι useY useT d R₀ kA kY kT p cbl) (ι .cb) cbl' =
      pst ι useY useT d R₀ kA kY kT p cbl' := by
  unfold pst
  rw [update_regsOf hι]
  apply regsOf_congr
  funext x
  cases x <;> simp [ptbl, Function.update_of_ne]

/-- Emitting a run of zeros whose positions carry zero bits of the offset. -/
lemma pst_foldl_emit (kA kY kT : ℕ) (cbl : List (Fin (A + 4))) :
    ∀ (l : List (Fin (A + 4))) (p : ℕ),
      (∀ q, p ≤ q → q < p + l.length → q < d.W → (PData.X useY useT d).testBit q = false) →
      l.foldl (fun R _ => emitFx (ι .cnt) (ι .w) false R) (pst ι useY useT d R₀ kA kY kT p cbl) =
        pst ι useY useT d R₀ kA kY kT (p + l.length) cbl
  | [], p, _ => by simp
  | x :: rest, p, h => by
    simp only [List.foldl_cons]
    rw [pst_emit useY useT d R₀ hι kA kY kT p cbl (fun hp => h p le_rfl (by simp) hp),
      pst_foldl_emit kA kY kT cbl rest (p + 1) (fun q h1 h2 h3 => h q (by omega) (by simp; omega) h3)]
    simp [Nat.add_assoc, Nat.add_comm 1]

/-- `scanR a t (emit cnt w false)` on the preparation state. -/
lemma pst_scanEmit {a t : PReg} (hat : a ≠ t) (ha1 : a ≠ .cnt) (ha2 : a ≠ .w) (ht1 : t ≠ .cnt)
    (ht2 : t ≠ .w) (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = pst ι useY useT d R₀ kA kY kT p cbl) (ht0 : R₀ (ι t) = []) (htp : ptbl ι useY useT d R₀ kA kY kT p cbl t = R₀ (ι t))
    (hX : ∀ q, p ≤ q → q < p + (R₀ (ι a)).length → q < d.W → (PData.X useY useT d).testBit q = false)
    (hap : ptbl ι useY useT d R₀ kA kY kT p cbl a = R₀ (ι a)) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (scanR (ι a) (ι t) (emit (ι .cnt) (ι .w) false)) (mk v S)
        (4 * (R₀ (ι a)).length + 4)
        (mk v' { S with R := pst ι useY useT d R₀ kA kY kT (p + (R₀ (ι a)).length) cbl }) := by
  have hcw : ι .cnt ≠ ι .w := hι.ne (by decide)
  have hSa : S.R (ι a) = R₀ (ι a) := by rw [hS, pst_apply useY useT d R₀ hι, hap]
  have hSt : S.R (ι t) = [] := by rw [hS, pst_apply useY useT d R₀ hι, htp, ht0]
  obtain ⟨v', hu, he⟩ := scanR_exec' body (hι.ne hat) (regFx_emit hcw false)
    (frame_emitFx (hι.ne ha1) (hι.ne ha2) false) (frame_emitFx (hι.ne ht1) (hι.ne ht2) false) v S hSt
  refine ⟨v', hu, Exec.cast he (by rw [hSa]) ?_⟩
  rw [hSa]
  conv_lhs => rw [hS]
  rw [pst_foldl_emit hι useY useT d R₀ kA kY kT cbl (R₀ (ι a)) p hX]

/-- One pop of the field `A` as an iteration: `IterSpec` over any scan registers other than the
field and its scratch. -/
lemma popA_iter {a t : PReg} (ha1 : a ≠ .cfA) (ha2 : a ≠ .tA) (ht1 : t ≠ .cfA) (ht2 : t ≠ .tA)
    (hxA : d.xA < 2 ^ d.lA) (kA₀ kY kT p : ℕ) (cbl : List (Fin (A + 4))) (N : ℕ)
    (hN : kA₀ + N ≤ d.lA) :
    IterSpec body (.act (popPush (ι .cfA) (ι .tA))) (ι a) (ι t)
      (fun j => pst ι useY useT d R₀ (kA₀ + j) kY kT p cbl) (fun _ => 1) N := by
  intro j hj v S hΨ
  have hcA : S.R (ι .cfA) = (binSyms d.lA d.xA : List (Fin (A + 4))).drop (kA₀ + j) := by
    rw [hΨ _ (hι.ne ha1.symm) (hι.ne ht1.symm)]; beta_reduce; rw [pst_apply useY useT d R₀ hι]; rfl
  have htA : S.R (ι .tA) = ((binSyms d.lA d.xA : List (Fin (A + 4))).take (kA₀ + j)).reverse := by
    rw [hΨ _ (hι.ne ha2.symm) (hι.ne ht2.symm)]; beta_reduce; rw [pst_apply useY useT d R₀ hι]; rfl
  have hrun := popPush_run (hι.ne (by decide : PReg.cfA ≠ .tA)) d.lA d.xA (kA₀ + j) (by omega) v S
    hcA htA
  have hex : Exec body (.act (popPush (ι .cfA) (ι .tA))) (mk v S) 1
      (mk { v with sym := some (bitSymbol (d.xA.testBit (kA₀ + j))) }
        { S with R := popFieldFx S.R (ι .cfA) (ι .tA) d.lA d.xA (kA₀ + j) }) :=
    hrun ▸ Exec.act (body := body) (popPush (ι .cfA) (ι .tA)) (mk v S)
  refine ⟨_, _, 1, ?_, le_rfl, hex, ?_, ?_, ?_⟩
  · rfl
  · exact popFieldFx_ne (hι.ne ha1) (hι.ne ha2) _ _ _
  · exact popFieldFx_ne (hι.ne ht1) (hι.ne ht2) _ _ _
  · intro k hka hkt
    have : popFieldFx S.R (ι .cfA) (ι .tA) d.lA d.xA (kA₀ + j) k =
        popFieldFx (pst ι useY useT d R₀ (kA₀ + j) kY kT p cbl) (ι .cfA) (ι .tA) d.lA d.xA
          (kA₀ + j) k := by
      unfold popFieldFx
      by_cases h1 : k = ι .tA
      · subst h1; simp
      by_cases h2 : k = ι .cfA
      · subst h2; simp [Function.update_of_ne (hι.ne (by decide : PReg.cfA ≠ .tA))]
      · simp only [Function.update_of_ne h1, Function.update_of_ne h2]
        exact hΨ k hka hkt
    rw [this, pst_popA useY useT d R₀ hι]
    rfl

/-- One pop of the field `Y` as an iteration. -/
lemma popY_iter {a t : PReg} (ha1 : a ≠ .cfY) (ha2 : a ≠ .tY) (ht1 : t ≠ .cfY) (ht2 : t ≠ .tY)
    (hxY : d.xY < 2 ^ d.lY) (kA kY₀ kT p : ℕ) (cbl : List (Fin (A + 4))) (N : ℕ)
    (hN : kY₀ + N ≤ d.lY) :
    IterSpec body (.act (popPush (ι .cfY) (ι .tY))) (ι a) (ι t)
      (fun j => pst ι useY useT d R₀ kA (kY₀ + j) kT p cbl) (fun _ => 1) N := by
  intro j hj v S hΨ
  have hcY : S.R (ι .cfY) = (binSyms d.lY d.xY : List (Fin (A + 4))).drop (kY₀ + j) := by
    rw [hΨ _ (hι.ne ha1.symm) (hι.ne ht1.symm)]; beta_reduce; rw [pst_apply useY useT d R₀ hι]; rfl
  have htY : S.R (ι .tY) = ((binSyms d.lY d.xY : List (Fin (A + 4))).take (kY₀ + j)).reverse := by
    rw [hΨ _ (hι.ne ha2.symm) (hι.ne ht2.symm)]; beta_reduce; rw [pst_apply useY useT d R₀ hι]; rfl
  have hrun := popPush_run (hι.ne (by decide : PReg.cfY ≠ .tY)) d.lY d.xY (kY₀ + j) (by omega) v S
    hcY htY
  have hex : Exec body (.act (popPush (ι .cfY) (ι .tY))) (mk v S) 1
      (mk { v with sym := some (bitSymbol (d.xY.testBit (kY₀ + j))) }
        { S with R := popFieldFx S.R (ι .cfY) (ι .tY) d.lY d.xY (kY₀ + j) }) :=
    hrun ▸ Exec.act (body := body) (popPush (ι .cfY) (ι .tY)) (mk v S)
  refine ⟨_, _, 1, ?_, le_rfl, hex, ?_, ?_, ?_⟩
  · rfl
  · exact popFieldFx_ne (hι.ne ha1) (hι.ne ha2) _ _ _
  · exact popFieldFx_ne (hι.ne ht1) (hι.ne ht2) _ _ _
  · intro k hka hkt
    have : popFieldFx S.R (ι .cfY) (ι .tY) d.lY d.xY (kY₀ + j) k =
        popFieldFx (pst ι useY useT d R₀ kA (kY₀ + j) kT p cbl) (ι .cfY) (ι .tY) d.lY d.xY
          (kY₀ + j) k := by
      unfold popFieldFx
      by_cases h1 : k = ι .tY
      · subst h1; simp
      by_cases h2 : k = ι .cfY
      · subst h2; simp [Function.update_of_ne (hι.ne (by decide : PReg.cfY ≠ .tY))]
      · simp only [Function.update_of_ne h1, Function.update_of_ne h2]
        exact hΨ k hka hkt
    rw [this, pst_popY useY useT d R₀ hι]
    rfl

/-- One digit bit of column `c` as an iteration of the digit loop (scan registers `GR`, `t₂`). -/
lemma digit_iter (hxT : d.xT < 2 ^ d.lT) (c : ℕ) (hc : c < d.n) (kA kY : ℕ)
    (hT : c * d.G + d.G ≤ d.lT) :
    IterSpec body (.act (digitStep ι)) (ι .GR) (ι .t₂)
      (fun m => pst ι useY true d R₀ kA kY (c * d.G + m) (d.oO + c * PData.sO true d + 1 + m)
        [bitSymbol (PData.ctrl useY d c)]) (fun _ => 1) d.G := by
  intro m hm v S hΨ
  have hcT : S.R (ι .cfT) = (binSyms d.lT d.xT : List (Fin (A + 4))).drop (c * d.G + m) := by
    rw [hΨ _ (hι.ne (by decide)) (hι.ne (by decide))]; beta_reduce; rw [pst_apply useY true d R₀ hι]; rfl
  have htT : S.R (ι .tT) = ((binSyms d.lT d.xT : List (Fin (A + 4))).take (c * d.G + m)).reverse := by
    rw [hΨ _ (hι.ne (by decide)) (hι.ne (by decide))]; beta_reduce; rw [pst_apply useY true d R₀ hι]; rfl
  have hcb : S.R (ι .cb) = [bitSymbol (PData.ctrl useY d c)] := by
    rw [hΨ _ (hι.ne (by decide)) (hι.ne (by decide))]; beta_reduce; rw [pst_apply useY true d R₀ hι]; rfl
  -- the pop and push
  have hhead := head_drop_binSyms (A := A) d.lT d.xT (c * d.G + m) (by omega)
  have htail : ((binSyms d.lT d.xT : List (Fin (A + 4))).drop (c * d.G + m)).tail =
      (binSyms d.lT d.xT : List (Fin (A + 4))).drop (c * d.G + m + 1) := by rw [List.tail_drop]
  have htake : ((binSyms d.lT d.xT : List (Fin (A + 4))).take (c * d.G + m + 1)).reverse =
      bitSymbol (d.xT.testBit (c * d.G + m)) ::
        ((binSyms d.lT d.xT : List (Fin (A + 4))).take (c * d.G + m)).reverse := by
    rw [List.take_succ, List.reverse_append]
    have : (binSyms d.lT d.xT : List (Fin (A + 4)))[c * d.G + m]? =
        some (bitSymbol (d.xT.testBit (c * d.G + m))) := by simp [binSyms, show c * d.G + m < d.lT by omega]
    rw [this]
    rfl
  set S₁ : Stacks T A := { S with R := popFieldFx S.R (ι .cfT) (ι .tT) d.lT d.xT (c * d.G + m) }
  set v₁ : HS T Q A U := { v with sym := some (bitSymbol (d.xT.testBit (c * d.G + m))) }
  have hpp : ∀ k : Act T Q A U, (Action.pop (.rt (ι .cfT)) (fun v o => { v with sym := o })
      (.push (.rt (ι .tT)) (fun v => v.sym.getD blank) k)).run (mk v S) = k.run (mk v₁ S₁) := by
    intro k
    simp only [Action.run, mk_var, mk_stk, get_rt, hcT, hhead, Option.getD_some, update_rt, store_mk,
      htail, S₁, v₁, popFieldFx]
    rw [Function.update_of_ne (hι.ne (by decide : PReg.cfT ≠ .tT)).symm, htT, htake]
  have hcb₁ : S₁.R (ι .cb) = [bitSymbol (PData.ctrl useY d c)] := by
    simp [S₁, popFieldFx, Function.update_of_ne (hι.ne (by decide : PReg.cb ≠ .tT)),
      Function.update_of_ne (hι.ne (by decide : PReg.cb ≠ .cfT)), hcb]
  obtain ⟨v₂, hu₂, _, hrun₂⟩ := emitD_run hι (fun b sy => b && symBit (sy.getD blank)) .done v₁ S₁
  rw [hcb₁] at hrun₂
  simp only [List.head?_cons, isTick, Option.map_some, Option.getD_some, symBit_bitSymbol, v₁,
    Option.getD_some] at hrun₂
  have hrun : (digitStep ι : Act T Q A U).run (mk v S) =
      mk v₂ { S₁ with
        R := emitFx (ι .cnt) (ι .w) (PData.ctrl useY d c && d.xT.testBit (c * d.G + m)) S₁.R } := by
    unfold digitStep
    rw [hpp, hrun₂, run_done]
  have hex : Exec body (.act (digitStep ι)) (mk v S) 1 (mk v₂ { S₁ with
      R := emitFx (ι .cnt) (ι .w) (PData.ctrl useY d c && d.xT.testBit (c * d.G + m)) S₁.R }) :=
    hrun ▸ Exec.act (body := body) (digitStep ι) (mk v S)
  refine ⟨v₂, _, 1, by rw [hu₂], le_rfl, hex, ?_, ?_, ?_⟩
  · rw [emitFx_ne (hι.ne (by decide)) (hι.ne (by decide))]
    exact popFieldFx_ne (hι.ne (by decide)) (hι.ne (by decide)) _ _ _
  · rw [emitFx_ne (hι.ne (by decide)) (hι.ne (by decide))]
    exact popFieldFx_ne (hι.ne (by decide)) (hι.ne (by decide)) _ _ _
  · intro k hka hkt
    -- the registers off `GR`, `t₂` agree with the state, so the state transitions apply
    have hS₁ : ∀ k, k ≠ ι .GR → k ≠ ι .t₂ → S₁.R k =
        pst ι useY true d R₀ kA kY (c * d.G + m + 1)
          (d.oO + c * PData.sO true d + 1 + m) [bitSymbol (PData.ctrl useY d c)] k := by
      intro k hka hkt
      rw [← pst_popT useY true d R₀ hι]
      simp only [S₁, popFieldFx]
      by_cases h1 : k = ι .tT
      · subst h1; simp
      by_cases h2 : k = ι .cfT
      · subst h2; simp [Function.update_of_ne (hι.ne (by decide : PReg.cfT ≠ .tT))]
      · simp only [Function.update_of_ne h1, Function.update_of_ne h2]
        exact hΨ k hka hkt
    have hE : emitFx (ι .cnt) (ι .w) (PData.ctrl useY d c && d.xT.testBit (c * d.G + m)) S₁.R k =
        emitFx (ι .cnt) (ι .w) (PData.ctrl useY d c && d.xT.testBit (c * d.G + m))
          (pst ι useY true d R₀ kA kY (c * d.G + m + 1)
            (d.oO + c * PData.sO true d + 1 + m) [bitSymbol (PData.ctrl useY d c)]) k := by
      unfold emitFx
      rw [hS₁ _ (hι.ne (by decide)) (hι.ne (by decide))]
      split_ifs
      · exact hS₁ k hka hkt
      · simp only [Function.update_apply]
        split_ifs with h1 h2 <;> try rfl
        · rw [hS₁ (ι .w) (hι.ne (by decide)) (hι.ne (by decide))]
        · exact hS₁ k hka hkt
    rw [hE, pst_emit useY true d R₀ hι _ _ _ _ _ (fun hp => ?_)]
    · beta_reduce
      rw [Nat.add_assoc (c * d.G) m 1, Nat.add_assoc (d.oO + c * PData.sO true d + 1) m 1]
    · -- the emitted bit is bit `m + 1` of the coefficient
      have hu : 1 + m < PData.sO true d := by unfold PData.sO; simp; omega
      rw [show d.oO + c * PData.sO true d + 1 + m = d.oO + c * PData.sO true d + (1 + m) by ring,
        PData.X_testBit_col useY true d c hc (1 + m) hu, show 1 + m = m + 1 by ring,
        PData.coef_testBit_succ, PData.digit_testBit _ _ _ hm]

end Loops


/-! ### One column -/

section Column

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U) {ι : PReg → Fin T}
  (hι : Function.Injective ι) (useY useT : Bool) (d : PData)

omit hι in
lemma clearCb_run (v : HS T Q A U) (S : Stacks T A) :
    (clearCb ι : Act T Q A U).run (mk v S) =
      mk v { S with R := Function.update S.R (ι .cb) (S.R (ι .cb)).tail } := by
  simp [clearCb, Action.run, update_rt]

include hι

/-- The preparation state depends on the background only pointwise. -/
lemma pst_R₀_congr {R₀ R₀' : Regs T A} (kA kY kT p : ℕ) (cbl : List (Fin (A + 4))) {k : Fin T}
    (h : R₀ k = R₀' k) :
    pst ι useY useT d R₀ kA kY kT p cbl k = pst ι useY useT d R₀' kA kY kT p cbl k := by
  by_cases hk : ∃ x, ι x = k
  · obtain ⟨x, rfl⟩ := hk
    rw [pst_apply useY useT d R₀ hι, pst_apply useY useT d R₀' hι]
    cases x <;> simp [ptbl, h]
  · push_neg at hk
    rw [pst_ne useY useT d R₀ hι _ _ _ _ _ hk, pst_ne useY useT d R₀' hι _ _ _ _ _ hk, h]

/-- A register file that agrees with a target preparation state off two scan registers, and
keeps those two registers from a source preparation state with the same table entries there,
is the target state. -/
lemma pst_of_agree (R₀ : Regs T A) {kA kY kT p : ℕ} {cbl : List (Fin (A + 4))}
    {kA' kY' kT' p' : ℕ} {cbl' : List (Fin (A + 4))} {a t : PReg}
    {R R' : Regs T A} (hS : R = pst ι useY useT d R₀ kA kY kT p cbl)
    (hRa : R' (ι a) = R (ι a)) (hRt : R' (ι t) = R (ι t))
    (hk : ∀ k, k ≠ ι a → k ≠ ι t → R' k = pst ι useY useT d R₀ kA' kY' kT' p' cbl' k)
    (ha : ∀ kA kY kT p cbl, ptbl ι useY useT d R₀ kA kY kT p cbl a = R₀ (ι a))
    (ht : ∀ kA kY kT p cbl, ptbl ι useY useT d R₀ kA kY kT p cbl t = R₀ (ι t)) :
    R' = pst ι useY useT d R₀ kA' kY' kT' p' cbl' := by
  funext k
  by_cases h1 : k = ι a
  · subst h1
    rw [hRa, hS, pst_apply useY useT d R₀ hι, pst_apply useY useT d R₀ hι, ha, ha]
  by_cases h2 : k = ι t
  · subst h2
    rw [hRt, hS, pst_apply useY useT d R₀ hι, pst_apply useY useT d R₀ hι, ht, ht]
  exact hk k h1 h2

/-- The cost of one column. -/
def colCost : ℕ := 6 * (if useT then d.G else 0) + 4 * d.pad + 6 * d.sA + 6 * d.K + 19

/-- The digit loop of a column (a single step when `useT` is off). -/
lemma digits_exec (R₀ : Regs T A) (hxT : d.xT < 2 ^ d.lT) (j : ℕ) (hj : j < d.n)
    (hT : useT = true → j * d.G + d.G ≤ d.lT) (hG : R₀ (ι .GR) = List.replicate d.G tick)
    (ht₂ : R₀ (ι .t₂) = []) (kA kY : ℕ) (b : Bool) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = pst ι useY useT d R₀ kA kY (if useT then j * d.G else 0)
      (d.oO + j * PData.sO useT d + 1) [bitSymbol b]) (hb : b = PData.ctrl useY d j) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 6 * (if useT then d.G else 0) + 4 ∧
      Exec body (if useT then scanP (ι .GR) (ι .t₂) (.act (digitStep ι)) else .act .done)
        (mk v S) m
        (mk v' { S with
          R := pst ι useY useT d R₀ kA kY ((if useT then j * d.G else 0) + (if useT then d.G else 0))
                (d.oO + j * PData.sO useT d + 1 + (if useT then d.G else 0)) [bitSymbol b] }) := by
  subst hb
  cases useT with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hS ⊢
    refine ⟨v, 1, rfl, by omega, ?_⟩
    have := Exec.act (body := body) (Action.done : Act T Q A U) (mk v S)
    rw [run_done] at this
    exact Exec.cast this rfl (by rw [← hS])
  | true =>
    have hT' := hT rfl
    simp only [↓reduceIte, Nat.zero_add] at hS ⊢
    have hSG : S.R (ι .GR) = List.replicate d.G tick := by
      rw [hS, pst_apply useY true d R₀ hι]; exact hG
    have hSt : S.R (ι .t₂) = [] := by
      rw [hS, pst_apply useY true d R₀ hι]; exact ht₂
    obtain ⟨v', R', m, hu, hm, he, ha, ht, hk⟩ := scanP_exec body (hι.ne (by decide))
      (digit_iter body hι useY d R₀ hxT j hj kA kY hT') 0 v S
      (by rw [hSG]; simp) (fun k hka hkt => by simp [hS])
    refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
    · rw [hSG, hSt] at hm
      simp [Finset.sum_const, Finset.card_range] at hm
      omega
    · rw [hSG] at hk
      rw [hSt, List.reverse_nil, List.nil_append] at ha
      simp only [List.length_replicate, Nat.zero_add] at hk
      congr 2
      exact pst_of_agree hι useY true d R₀ (a := .GR) (t := .t₂) hS ha (ht.trans hSt.symm) hk
        (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)

/-- One column of the preparation. -/
lemma column_exec (R₀ : Regs T A) (hxA : d.xA < 2 ^ d.lA) (hxY : d.xY < 2 ^ d.lY)
    (hxT : d.xT < 2 ^ d.lT) (j : ℕ) (hj : j < d.n) (hA : d.oA + j * d.sA + d.sA ≤ d.lA)
    (hY : d.oY + j * d.K + d.K ≤ d.lY) (hT : useT = true → j * d.G + d.G ≤ d.lT)
    (hG : R₀ (ι .GR) = List.replicate d.G tick) (hpad : R₀ (ι .padR) = List.replicate d.pad tick)
    (hsA : R₀ (ι .sAR) = List.replicate d.sA tick) (hK : R₀ (ι .KR) = List.replicate d.K tick)
    (ht₂ : R₀ (ι .t₂) = []) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = pst ι useY useT d R₀ (d.oA + j * d.sA) (d.oY + j * d.K)
      (if useT then j * d.G else 0) (d.oO + j * PData.sO useT d) []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ colCost useT d ∧
      Exec body (column useY useT ι) (mk v S) m
        (mk v' { S with
          R := pst ι useY useT d R₀ (d.oA + j * d.sA + d.sA) (d.oY + j * d.K + d.K)
                ((if useT then j * d.G else 0) + (if useT then d.G else 0))
                (d.oO + j * PData.sO useT d + 1 + (if useT then d.G else 0) + d.pad) [] }) := by
  set kA := d.oA + j * d.sA with hkA
  set kY := d.oY + j * d.K with hkY
  set kT := if useT then j * d.G else 0 with hkT
  set p := d.oO + j * PData.sO useT d with hpdef
  set G' := if useT then d.G else 0 with hG'
  set b := PData.ctrl useY d j with hb
  -- step 1: the control bit
  have he₁ := Exec.act (body := body) (readBit useY ι) (mk v S)
  rw [readBit_run] at he₁
  have hR₁ : Function.update S.R (ι .cb)
      (bitSymbol (xor (isTick (S.R (ι .cfA)).head?) (useY && isTick (S.R (ι .cfY)).head?)) ::
        S.R (ι .cb)) = pst ι useY useT d R₀ kA kY kT p [bitSymbol b] := by
    have hA' : S.R (ι .cfA) = (binSyms d.lA d.xA : List (Fin (A + 4))).drop kA := by
      rw [hS, pst_apply useY useT d R₀ hι]; rfl
    have hY' : S.R (ι .cfY) = (binSyms d.lY d.xY : List (Fin (A + 4))).drop kY := by
      rw [hS, pst_apply useY useT d R₀ hι]; rfl
    have hcb : S.R (ι .cb) = [] := by
      rw [hS, pst_apply useY useT d R₀ hι]; rfl
    rw [hA', hY', hcb, isTick_head _ _ _ hxA, isTick_head _ _ _ hxY, hS,
      pst_pushCb useY useT d R₀ hι, hb, PData.ctrl, hkA, hkY]
  rw [hR₁] at he₁
  set S₁ : Stacks T A := { S with R := pst ι useY useT d R₀ kA kY kT p [bitSymbol b] } with hS₁
  set v₁ := setScan (ι .cb) (xor (isTick (S.R (ι .cfA)).head?)
    (useY && isTick (S.R (ι .cfY)).head?)) v with hv₁
  -- step 2: the segment bit
  obtain ⟨v₂, hu₂, -, hr₂⟩ := emitD_run hι (fun b _ => b && !useT) .done v₁ S₁
  rw [run_done] at hr₂
  have he₂ := Exec.act (body := body) (emitD ι (fun b _ => b && !useT) .done) (mk v₁ S₁)
  rw [hr₂] at he₂
  have hcb₁ : S₁.R (ι .cb) = [bitSymbol b] := by
    simp only [hS₁]; rw [pst_apply useY useT d R₀ hι]; rfl
  have hR₂ : emitFx (ι .cnt) (ι .w) ((fun b _ => b && !useT) (isTick (S₁.R (ι .cb)).head?) v₁.sym)
      S₁.R = pst ι useY useT d R₀ kA kY kT (p + 1) [bitSymbol b] := by
    rw [hcb₁]
    simp only [List.head?_cons, isTick, Option.map_some, Option.getD_some, symBit_bitSymbol, hS₁]
    refine pst_emit useY useT d R₀ hι kA kY kT p _ fun _ => ?_
    rw [hpdef, ← Nat.add_zero (d.oO + j * PData.sO useT d),
      PData.X_testBit_col useY useT d j hj 0 (by unfold PData.sO; omega),
      PData.coef_testBit_zero]
  rw [hR₂] at he₂
  set S₂ : Stacks T A := { S with R := pst ι useY useT d R₀ kA kY kT (p + 1) [bitSymbol b] } with hS₂
  -- step 3: the digit bits
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := digits_exec body hι useY useT d R₀ hxT j hj hT hG ht₂ kA kY b v₂
    S₂ rfl hb
  set S₃ : Stacks T A :=
    { S with R := pst ι useY useT d R₀ kA kY (kT + G') (p + 1 + G') [bitSymbol b] } with hS₃
  -- step 4: the padding zeros
  have hpadX : ∀ q, p + 1 + G' ≤ q → q < p + 1 + G' + (R₀ (ι .padR)).length → q < d.W →
      (PData.X useY useT d).testBit q = false := by
    intro q h1 h2 _
    rw [hpad, List.length_replicate] at h2
    have hu : q = d.oO + j * PData.sO useT d + (1 + G' + (q - (p + 1 + G'))) := by omega
    rw [hu, PData.X_testBit_col useY useT d j hj _ (by unfold PData.sO; omega)]
    exact PData.coef_testBit_high useY useT d j _ (by omega)
  obtain ⟨v₄, hu₄, he₄⟩ := pst_scanEmit body hι useY useT d R₀ (a := .padR) (t := .t₂)
    (by decide) (by decide) (by decide) (by decide) (by decide) kA kY (kT + G') (p + 1 + G')
    [bitSymbol b] v₃ S₃ rfl ht₂ rfl hpadX rfl
  rw [hpad, List.length_replicate] at he₄
  set S₄ : Stacks T A :=
    { S with R := pst ι useY useT d R₀ kA kY (kT + G') (p + 1 + G' + d.pad) [bitSymbol b] } with hS₄
  -- step 5: advance the field `A`
  have hSa : S₄.R (ι .sAR) = List.replicate d.sA tick := by
    simp only [hS₄]; rw [pst_apply useY useT d R₀ hι]; exact hsA
  have hSt₄ : S₄.R (ι .t₂) = [] := by
    simp only [hS₄]; rw [pst_apply useY useT d R₀ hι]; exact ht₂
  obtain ⟨v₅, R₅, m₅, hu₅, hm₅, he₅, ha₅, ht₅, hk₅⟩ := scanP_exec body (hι.ne (by decide))
    (popA_iter body hι useY useT d R₀ (a := .sAR) (t := .t₂) (by decide) (by decide) (by decide)
      (by decide) hxA kA kY (kT + G') (p + 1 + G' + d.pad) [bitSymbol b] d.sA (by omega))
    0 v₄ S₄ (by rw [hSa]; simp) (fun k _ _ => rfl)
  rw [hSa] at hk₅
  rw [hSt₄, List.reverse_nil, List.nil_append] at ha₅
  simp only [List.length_replicate, Nat.zero_add] at hk₅
  have hR₅ : R₅ = pst ι useY useT d R₀ (kA + d.sA) kY (kT + G') (p + 1 + G' + d.pad)
      [bitSymbol b] :=
    pst_of_agree hι useY useT d R₀ (a := .sAR) (t := .t₂) (R := S₄.R) (by rw [hS₄]) ha₅
      (ht₅.trans hSt₄.symm) hk₅ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  rw [hR₅] at he₅
  set S₅ : Stacks T A :=
    { S with
      R := pst ι useY useT d R₀ (kA + d.sA) kY (kT + G') (p + 1 + G' + d.pad) [bitSymbol b] } with hS₅
  -- step 6: advance the field `Y`
  have hSk : S₅.R (ι .KR) = List.replicate d.K tick := by
    simp only [hS₅]; rw [pst_apply useY useT d R₀ hι]; exact hK
  have hSt₅ : S₅.R (ι .t₂) = [] := by
    simp only [hS₅]; rw [pst_apply useY useT d R₀ hι]; exact ht₂
  obtain ⟨v₆, R₆, m₆, hu₆, hm₆, he₆, ha₆, ht₆, hk₆⟩ := scanP_exec body (hι.ne (by decide))
    (popY_iter body hι useY useT d R₀ (a := .KR) (t := .t₂) (by decide) (by decide) (by decide)
      (by decide) hxY (kA + d.sA) kY (kT + G') (p + 1 + G' + d.pad) [bitSymbol b] d.K (by omega))
    0 v₅ S₅ (by rw [hSk]; simp) (fun k _ _ => rfl)
  rw [hSk] at hk₆
  rw [hSt₅, List.reverse_nil, List.nil_append] at ha₆
  simp only [List.length_replicate, Nat.zero_add] at hk₆
  have hR₆ : R₆ = pst ι useY useT d R₀ (kA + d.sA) (kY + d.K) (kT + G') (p + 1 + G' + d.pad)
      [bitSymbol b] :=
    pst_of_agree hι useY useT d R₀ (a := .KR) (t := .t₂) (R := S₅.R) (by rw [hS₅]) ha₆
      (ht₆.trans hSt₅.symm) hk₆ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  rw [hR₆] at he₆
  set S₆ : Stacks T A :=
    { S with
      R := pst ι useY useT d R₀ (kA + d.sA) (kY + d.K) (kT + G') (p + 1 + G' + d.pad)
            [bitSymbol b] } with hS₆
  -- step 7: clear the control bit
  have he₇ := Exec.act (body := body) (clearCb ι) (mk v₆ S₆)
  rw [clearCb_run] at he₇
  have hR₇ : Function.update S₆.R (ι .cb) (S₆.R (ι .cb)).tail =
      pst ι useY useT d R₀ (kA + d.sA) (kY + d.K) (kT + G') (p + 1 + G' + d.pad) [] := by
    simp only [hS₆]
    rw [pst_apply useY useT d R₀ hι, pst_setCb hι useY useT d R₀]
    simp [ptbl]
  rw [hR₇] at he₇
  -- assembly
  refine ⟨v₆, 1 + (1 + (m₃ + ((4 * d.pad + 4) + (m₅ + (m₆ + 1))))),
    by simp only [hu₆, hu₅, hu₄, hu₃, hu₂, hv₁, setScan], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ he₇)))))⟩
  rw [hSa, hSt₄] at hm₅
  rw [hSk, hSt₅] at hm₆
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_replicate,
    List.length_nil] at hm₅ hm₆
  unfold colCost
  omega

end Column


/-! ### The column loop and the whole preparation -/

section Whole

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U) {ι : PReg → Fin T}
  (hι : Function.Injective ι) (useY useT : Bool) (d : PData)
include hι

omit hι in
/-- The state after `j` columns. -/
noncomputable def colState (R₀ : Regs T A) (j : ℕ) : Regs T A :=
  pst ι useY useT d R₀ (d.oA + j * d.sA) (d.oY + j * d.K) (if useT then j * d.G else 0)
    (d.oO + j * PData.sO useT d) []

/-- The column as an iteration of the loop over `nR`, `t₁`. -/
lemma column_iter (R₀ : Regs T A) (hxA : d.xA < 2 ^ d.lA) (hxY : d.xY < 2 ^ d.lY)
    (hxT : d.xT < 2 ^ d.lT) (hA : d.oA + d.n * d.sA ≤ d.lA) (hY : d.oY + d.n * d.K ≤ d.lY)
    (hT : useT = true → d.n * d.G ≤ d.lT)
    (hG : R₀ (ι .GR) = List.replicate d.G tick) (hpad : R₀ (ι .padR) = List.replicate d.pad tick)
    (hsA : R₀ (ι .sAR) = List.replicate d.sA tick) (hK : R₀ (ι .KR) = List.replicate d.K tick)
    (ht₂ : R₀ (ι .t₂) = []) :
    IterSpec body (column useY useT ι) (ι .nR) (ι .t₁) (colState (ι := ι) useY useT d R₀)
      (fun _ => colCost useT d) d.n := by
  intro j hj v S hΨ
  set R₀' : Regs T A :=
    Function.update (Function.update R₀ (ι .nR) (S.R (ι .nR))) (ι .t₁) (S.R (ι .t₁)) with hR₀'
  have hnt : ι .nR ≠ ι .t₁ := hι.ne (by decide)
  have hoff : ∀ k, k ≠ ι .nR → k ≠ ι .t₁ → R₀ k = R₀' k := by
    intro k h1 h2
    simp [hR₀', Function.update_of_ne h1, Function.update_of_ne h2]
  have hS : S.R = pst ι useY useT d R₀' (d.oA + j * d.sA) (d.oY + j * d.K)
      (if useT then j * d.G else 0) (d.oO + j * PData.sO useT d) [] := by
    funext k
    by_cases h1 : k = ι .nR
    · subst h1
      rw [pst_apply useY useT d R₀' hι]
      simp [ptbl, hR₀', Function.update_of_ne hnt]
    by_cases h2 : k = ι .t₁
    · subst h2
      rw [pst_apply useY useT d R₀' hι]
      simp [ptbl, hR₀']
    rw [hΨ k h1 h2]
    exact pst_R₀_congr hι useY useT d _ _ _ _ _ (hoff k h1 h2)
  have hA' : d.oA + j * d.sA + d.sA ≤ d.lA := by nlinarith [Nat.mul_le_mul_right d.sA hj]
  have hY' : d.oY + j * d.K + d.K ≤ d.lY := by nlinarith [Nat.mul_le_mul_right d.K hj]
  have hT' : useT = true → j * d.G + d.G ≤ d.lT := fun h => by
    have := hT h; nlinarith [Nat.mul_le_mul_right d.G hj]
  obtain ⟨v', m, hu, hm, he⟩ := column_exec body hι useY useT d R₀' hxA hxY hxT j hj hA' hY' hT'
    (by rw [← hoff _ (hι.ne (by decide)) (hι.ne (by decide))]; exact hG)
    (by rw [← hoff _ (hι.ne (by decide)) (hι.ne (by decide))]; exact hpad)
    (by rw [← hoff _ (hι.ne (by decide)) (hι.ne (by decide))]; exact hsA)
    (by rw [← hoff _ (hι.ne (by decide)) (hι.ne (by decide))]; exact hK)
    (by rw [← hoff _ (hι.ne (by decide)) (hι.ne (by decide))]; exact ht₂) v S hS
  refine ⟨v', _, m, hu, hm, he, ?_, ?_, ?_⟩
  · rw [pst_apply useY useT d R₀' hι]; simp [ptbl, hR₀', Function.update_of_ne hnt]
  · rw [pst_apply useY useT d R₀' hι]; simp [ptbl, hR₀']
  · intro k h1 h2
    rw [← pst_R₀_congr hι useY useT d _ _ _ _ _ (hoff k h1 h2)]
    unfold colState
    rw [show d.oA + j * d.sA + d.sA = d.oA + (j + 1) * d.sA by ring,
      show d.oY + j * d.K + d.K = d.oY + (j + 1) * d.K by ring,
      show (if useT = true then j * d.G else 0) + (if useT = true then d.G else 0) =
        if useT = true then (j + 1) * d.G else 0 by split_ifs <;> ring,
      show d.oO + j * PData.sO useT d + 1 + (if useT = true then d.G else 0) + d.pad =
        d.oO + (j + 1) * PData.sO useT d by unfold PData.sO; ring]

omit hι in
/-- Moving a field's consumed prefix back from its scratch register. -/
lemma movedR_field (R : Regs T A) {t cf : Fin T} (htc : t ≠ cf) (l : List (Fin (A + 4))) (k : ℕ)
    (ht : R t = (l.take k).reverse) (hcf : R cf = l.drop k) :
    movedR R t cf id (R t) = Function.update (Function.update R t []) cf l := by
  unfold movedR
  rw [ht, hcf, List.map_id, List.reverse_reverse, List.take_append_drop]

/-- The cost of the preparation. -/
def prepCost (lenComp : ℕ) : ℕ :=
  2 * lenComp + 10 * d.W + 4 * d.oO + 6 * d.oA + 6 * d.oY + 2 * (d.lA + d.lY + d.lT) +
    d.n * (colCost useT d + 5) + 34

/-- The offset preparation: from the initial register file it computes the offset word `X` into
`comp` and restores every other register. -/
theorem prepOff_exec (hxA : d.xA < 2 ^ d.lA) (hxY : d.xY < 2 ^ d.lY) (hxT : d.xT < 2 ^ d.lT)
    (hA : d.oA + d.n * d.sA ≤ d.lA) (hY : d.oY + d.n * d.K ≤ d.lY)
    (hT : useT = true → d.n * d.G ≤ d.lT) (v : HS T Q A U) (S : Stacks T A)
    (hcfA : S.R (ι .cfA) = binSyms d.lA d.xA) (hcfY : S.R (ι .cfY) = binSyms d.lY d.xY)
    (hcfT : S.R (ι .cfT) = binSyms d.lT d.xT)
    (hWR : S.R (ι .WR) = List.replicate d.W tick) (hoOR : S.R (ι .oOR) = List.replicate d.oO tick)
    (hoAR : S.R (ι .oAR) = List.replicate d.oA tick)
    (hoYR : S.R (ι .oYR) = List.replicate d.oY tick)
    (hsAR : S.R (ι .sAR) = List.replicate d.sA tick) (hKR : S.R (ι .KR) = List.replicate d.K tick)
    (hGR : S.R (ι .GR) = List.replicate d.G tick) (hnR : S.R (ι .nR) = List.replicate d.n tick)
    (hpadR : S.R (ι .padR) = List.replicate d.pad tick)
    (hcnt : S.R (ι .cnt) = []) (hw : S.R (ι .w) = []) (ht₁ : S.R (ι .t₁) = [])
    (ht₂ : S.R (ι .t₂) = []) (htA : S.R (ι .tA) = []) (htY : S.R (ι .tY) = [])
    (htT : S.R (ι .tT) = []) (hcb : S.R (ι .cb) = []) :
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧
      m ≤ prepCost useT d (S.R (ι .comp)).length ∧
      Exec body (prepOff useY useT ι) (mk v S) m (mk v' { S with R := R' }) ∧
      R' (ι .comp) = binSyms d.W (PData.X useY useT d) ∧
      ∀ k, k ≠ ι .comp → R' k = S.R k := by
  set R₀ : Regs T A := Function.update S.R (ι .comp) [] with hR₀
  have hR₀k : ∀ k, k ≠ ι .comp → R₀ k = S.R k := fun k hk => by
    simp [hR₀, Function.update_of_ne hk]
  -- step 1: clear `comp`
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body (ι .comp) v S
  set S₁ : Stacks T A := { S with R := R₀ } with hS₁
  -- step 2: the counter
  obtain ⟨v₂, hu₂, he₂⟩ := ucopy_exec body (hι.ne (by decide : PReg.WR ≠ .cnt))
    (hι.ne (by decide : PReg.WR ≠ .t₁)) (hι.ne (by decide : PReg.cnt ≠ .t₁)) v₁ S₁
    (by simp only [hS₁]; rw [hR₀k _ (hι.ne (by decide))]; exact ht₁)
  have hR₂ : Function.update S₁.R (ι .cnt) (List.replicate (S₁.R (ι .WR)).length tick ++
      S₁.R (ι .cnt)) = pst ι useY useT d R₀ 0 0 0 0 [] := by
    simp only [hS₁]
    rw [hR₀k _ (hι.ne (by decide)), hR₀k _ (hι.ne (by decide)), hWR, hcnt, List.length_replicate,
      List.append_nil]
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      rw [pst_apply useY useT d R₀ hι]
      cases x <;> simp [ptbl, Function.update_apply, hι.eq_iff, hR₀, hcfA, hcfY, hcfT, hw, htA,
        htY, htT, hcb, binSyms]
    · push_neg at hk
      rw [pst_ne useY useT d R₀ hι _ _ _ _ _ hk, Function.update_of_ne (hk .cnt).symm]
  rw [hR₂] at he₂
  set S₂ : Stacks T A := { S with R := pst ι useY useT d R₀ 0 0 0 0 [] } with hS₂
  -- step 3: the low zeros
  obtain ⟨v₃, hu₃, he₃⟩ := pst_scanEmit body hι useY useT d R₀ (a := .oOR) (t := .t₁)
    (by decide) (by decide) (by decide) (by decide) (by decide) 0 0 0 0 [] v₂ S₂ rfl
    (by rw [hR₀k _ (hι.ne (by decide))]; exact ht₁) rfl
    (fun q _ h2 _ => by
      rw [hR₀k _ (hι.ne (by decide)), hoOR, List.length_replicate] at h2
      exact PData.X_testBit_lo useY useT d q (by omega)) rfl
  rw [hR₀k _ (hι.ne (by decide)), hoOR, List.length_replicate, Nat.zero_add] at he₃
  set S₃ : Stacks T A := { S with R := pst ι useY useT d R₀ 0 0 0 d.oO [] } with hS₃
  -- step 4: advance `A` to its offset
  have hSa : S₃.R (ι .oAR) = List.replicate d.oA tick := by
    simp only [hS₃]; rw [pst_apply useY useT d R₀ hι]; exact (hR₀k _ (hι.ne (by decide))).trans hoAR
  have hSt₃ : S₃.R (ι .t₁) = [] := by
    simp only [hS₃]; rw [pst_apply useY useT d R₀ hι]; exact (hR₀k _ (hι.ne (by decide))).trans ht₁
  obtain ⟨v₄, R₄, m₄, hu₄, hm₄, he₄, ha₄, ht₄, hk₄⟩ := scanP_exec body (hι.ne (by decide))
    (popA_iter body hι useY useT d R₀ (a := .oAR) (t := .t₁) (by decide) (by decide) (by decide)
      (by decide) hxA 0 0 0 d.oO [] d.oA (by nlinarith)) 0 v₃ S₃ (by rw [hSa]; simp)
    (fun k _ _ => rfl)
  rw [hSa] at hk₄
  rw [hSt₃, List.reverse_nil, List.nil_append] at ha₄
  simp only [List.length_replicate, Nat.zero_add] at hk₄
  have hR₄ : R₄ = pst ι useY useT d R₀ d.oA 0 0 d.oO [] :=
    pst_of_agree hι useY useT d R₀ (a := .oAR) (t := .t₁) (R := S₃.R) (by rw [hS₃]) ha₄
      (ht₄.trans hSt₃.symm) hk₄ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  rw [hR₄] at he₄
  set S₄ : Stacks T A := { S with R := pst ι useY useT d R₀ d.oA 0 0 d.oO [] } with hS₄
  -- step 5: advance `Y` to its offset
  have hSy : S₄.R (ι .oYR) = List.replicate d.oY tick := by
    simp only [hS₄]; rw [pst_apply useY useT d R₀ hι]; exact (hR₀k _ (hι.ne (by decide))).trans hoYR
  have hSt₄ : S₄.R (ι .t₁) = [] := by
    simp only [hS₄]; rw [pst_apply useY useT d R₀ hι]; exact (hR₀k _ (hι.ne (by decide))).trans ht₁
  obtain ⟨v₅, R₅, m₅, hu₅, hm₅, he₅, ha₅, ht₅, hk₅⟩ := scanP_exec body (hι.ne (by decide))
    (popY_iter body hι useY useT d R₀ (a := .oYR) (t := .t₁) (by decide) (by decide) (by decide)
      (by decide) hxY d.oA 0 0 d.oO [] d.oY (by nlinarith)) 0 v₄ S₄ (by rw [hSy]; simp)
    (fun k _ _ => rfl)
  rw [hSy] at hk₅
  rw [hSt₄, List.reverse_nil, List.nil_append] at ha₅
  simp only [List.length_replicate, Nat.zero_add] at hk₅
  have hR₅ : R₅ = pst ι useY useT d R₀ d.oA d.oY 0 d.oO [] :=
    pst_of_agree hι useY useT d R₀ (a := .oYR) (t := .t₁) (R := S₄.R) (by rw [hS₄]) ha₅
      (ht₅.trans hSt₄.symm) hk₅ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  rw [hR₅] at he₅
  set S₅ : Stacks T A := { S with R := pst ι useY useT d R₀ d.oA d.oY 0 d.oO [] } with hS₅
  -- step 6: the columns
  have hSn : S₅.R (ι .nR) = List.replicate d.n tick := by
    simp only [hS₅]; rw [pst_apply useY useT d R₀ hι]; exact (hR₀k _ (hι.ne (by decide))).trans hnR
  have hSt₅ : S₅.R (ι .t₁) = [] := by
    simp only [hS₅]; rw [pst_apply useY useT d R₀ hι]; exact (hR₀k _ (hι.ne (by decide))).trans ht₁
  have hΨ₀ : colState (ι := ι) useY useT d R₀ 0 = pst ι useY useT d R₀ d.oA d.oY 0 d.oO [] := by
    unfold colState; simp
  obtain ⟨v₆, R₆, m₆, hu₆, hm₆, he₆, ha₆, ht₆, hk₆⟩ := scanP_exec body (hι.ne (by decide))
    (column_iter body hι useY useT d R₀ hxA hxY hxT hA hY hT
      ((hR₀k _ (hι.ne (by decide))).trans hGR) ((hR₀k _ (hι.ne (by decide))).trans hpadR)
      ((hR₀k _ (hι.ne (by decide))).trans hsAR) ((hR₀k _ (hι.ne (by decide))).trans hKR)
      ((hR₀k _ (hι.ne (by decide))).trans ht₂)) 0 v₅ S₅ (by rw [hSn]; simp)
    (fun k _ _ => by rw [hΨ₀])
  rw [hSn] at hk₆
  rw [hSt₅, List.reverse_nil, List.nil_append] at ha₆
  simp only [List.length_replicate, Nat.zero_add] at hk₆
  have hR₆ : R₆ = colState (ι := ι) useY useT d R₀ d.n :=
    pst_of_agree hι useY useT d R₀ (a := .nR) (t := .t₁) (R := S₅.R) (by rw [hS₅]) ha₆
      (ht₆.trans hSt₅.symm) hk₆ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  rw [hR₆] at he₆
  set kA := d.oA + d.n * d.sA with hkA
  set kY := d.oY + d.n * d.K with hkY
  set kT := if useT then d.n * d.G else 0 with hkT
  set pF := d.oO + d.n * PData.sO useT d with hpF
  have hR₆' : colState (ι := ι) useY useT d R₀ d.n = pst ι useY useT d R₀ kA kY kT pF [] := rfl
  rw [hR₆'] at he₆
  set S₆ : Stacks T A := { S with R := pst ι useY useT d R₀ kA kY kT pF [] } with hS₆
  -- step 7: the high zeros
  obtain ⟨v₇, hu₇, he₇⟩ := pst_scanEmit body hι useY useT d R₀ (a := .WR) (t := .t₁)
    (by decide) (by decide) (by decide) (by decide) (by decide) kA kY kT pF [] v₆ S₆ rfl
    (by rw [hR₀k _ (hι.ne (by decide))]; exact ht₁) rfl
    (fun q h1 _ _ => PData.X_testBit_hi useY useT d q (by rw [hpF] at h1; exact h1)) rfl
  rw [hR₀k _ (hι.ne (by decide)), hWR, List.length_replicate] at he₇
  set S₇ : Stacks T A := { S with R := pst ι useY useT d R₀ kA kY kT (pF + d.W) [] } with hS₇
  -- steps 8–11: restore the fields and deliver the word
  have hp7 := pst_apply useY useT d R₀ hι kA kY kT (pF + d.W) []
  obtain ⟨v₈, hu₈, he₈⟩ := moveR_exec body (ι .tA) (ι .cfA) (hι.ne (by decide)) id v₇ S₇
  have hM₈ : movedR S₇.R (ι .tA) (ι .cfA) id (S₇.R (ι .tA)) =
      Function.update (Function.update S₇.R (ι .tA) []) (ι .cfA) (binSyms d.lA d.xA) :=
    movedR_field _ (hι.ne (by decide)) _ kA (by simp only [hS₇]; rw [hp7]; rfl)
      (by simp only [hS₇]; rw [hp7]; rfl)
  rw [hM₈] at he₈
  set S₈ : Stacks T A := { S with
    R := Function.update (Function.update S₇.R (ι .tA) []) (ι .cfA) (binSyms d.lA d.xA) } with hS₈
  obtain ⟨v₉, hu₉, he₉⟩ := moveR_exec body (ι .tY) (ι .cfY) (hι.ne (by decide)) id v₈ S₈
  have hM₉ : movedR S₈.R (ι .tY) (ι .cfY) id (S₈.R (ι .tY)) =
      Function.update (Function.update S₈.R (ι .tY) []) (ι .cfY) (binSyms d.lY d.xY) :=
    movedR_field _ (hι.ne (by decide)) _ kY
      (by simp only [hS₈, hS₇, Function.update_of_ne (hι.ne (by decide : PReg.tY ≠ .cfA)),
            Function.update_of_ne (hι.ne (by decide : PReg.tY ≠ .tA))]; rw [hp7]; rfl)
      (by simp only [hS₈, hS₇, Function.update_of_ne (hι.ne (by decide : PReg.cfY ≠ .cfA)),
            Function.update_of_ne (hι.ne (by decide : PReg.cfY ≠ .tA))]; rw [hp7]; rfl)
  rw [hM₉] at he₉
  set S₉ : Stacks T A := { S with
    R := Function.update (Function.update S₈.R (ι .tY) []) (ι .cfY) (binSyms d.lY d.xY) } with hS₉
  obtain ⟨v₁₀, hu₁₀, he₁₀⟩ := moveR_exec body (ι .tT) (ι .cfT) (hι.ne (by decide)) id v₉ S₉
  have hM₁₀ : movedR S₉.R (ι .tT) (ι .cfT) id (S₉.R (ι .tT)) =
      Function.update (Function.update S₉.R (ι .tT) []) (ι .cfT) (binSyms d.lT d.xT) :=
    movedR_field _ (hι.ne (by decide)) _ kT
      (by simp only [hS₉, hS₈, hS₇, Function.update_of_ne (hι.ne (by decide : PReg.tT ≠ .cfY)),
            Function.update_of_ne (hι.ne (by decide : PReg.tT ≠ .tY)),
            Function.update_of_ne (hι.ne (by decide : PReg.tT ≠ .cfA)),
            Function.update_of_ne (hι.ne (by decide : PReg.tT ≠ .tA))]; rw [hp7]; rfl)
      (by simp only [hS₉, hS₈, hS₇, Function.update_of_ne (hι.ne (by decide : PReg.cfT ≠ .cfY)),
            Function.update_of_ne (hι.ne (by decide : PReg.cfT ≠ .tY)),
            Function.update_of_ne (hι.ne (by decide : PReg.cfT ≠ .cfA)),
            Function.update_of_ne (hι.ne (by decide : PReg.cfT ≠ .tA))]; rw [hp7]; rfl)
  rw [hM₁₀] at he₁₀
  set S₁₀ : Stacks T A := { S with
    R := Function.update (Function.update S₉.R (ι .tT) []) (ι .cfT) (binSyms d.lT d.xT) } with hS₁₀
  obtain ⟨v₁₁, hu₁₁, he₁₁⟩ := moveR_exec body (ι .w) (ι .comp) (hι.ne (by decide)) id v₁₀ S₁₀
  have hw₁₀ : S₁₀.R (ι .w) = (binSyms d.W (PData.X useY useT d) : List (Fin (A + 4))).reverse := by
    simp only [hS₁₀, hS₉, hS₈, hS₇, Function.update_of_ne (hι.ne (by decide : PReg.w ≠ .cfT)),
      Function.update_of_ne (hι.ne (by decide : PReg.w ≠ .tT)),
      Function.update_of_ne (hι.ne (by decide : PReg.w ≠ .cfY)),
      Function.update_of_ne (hι.ne (by decide : PReg.w ≠ .tY)),
      Function.update_of_ne (hι.ne (by decide : PReg.w ≠ .cfA)),
      Function.update_of_ne (hι.ne (by decide : PReg.w ≠ .tA))]
    rw [hp7]
    simp [ptbl, show min (pF + d.W) d.W = d.W by omega]
  have hc₁₀ : S₁₀.R (ι .comp) = [] := by
    simp only [hS₁₀, hS₉, hS₈, hS₇, Function.update_of_ne (hι.ne (by decide : PReg.comp ≠ .cfT)),
      Function.update_of_ne (hι.ne (by decide : PReg.comp ≠ .tT)),
      Function.update_of_ne (hι.ne (by decide : PReg.comp ≠ .cfY)),
      Function.update_of_ne (hι.ne (by decide : PReg.comp ≠ .tY)),
      Function.update_of_ne (hι.ne (by decide : PReg.comp ≠ .cfA)),
      Function.update_of_ne (hι.ne (by decide : PReg.comp ≠ .tA))]
    rw [hp7]
    simp [ptbl, hR₀]
  have hM₁₁ : movedR S₁₀.R (ι .w) (ι .comp) id (S₁₀.R (ι .w)) =
      Function.update (Function.update S₁₀.R (ι .w) []) (ι .comp)
        (binSyms d.W (PData.X useY useT d)) := by
    unfold movedR
    rw [hw₁₀, hc₁₀, List.map_id, List.reverse_reverse, List.append_nil]
  rw [hM₁₁] at he₁₁
  -- assembly
  refine ⟨v₁₁, _, _, by simp only [hu₁₁, hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆
      (Exec.seq he₇ (Exec.seq he₈ (Exec.seq he₉ (Exec.seq he₁₀ he₁₁))))))))), ?_, ?_⟩
  · -- the cost
    have hl₈ : (S₇.R (ι .tA)).length = kA := by
      simp only [hS₇]; rw [hp7]; simp [ptbl, length_binSyms]; omega
    have hl₉ : (S₈.R (ι .tY)).length = kY := by
      simp only [hS₈, hS₇, Function.update_of_ne (hι.ne (by decide : PReg.tY ≠ .cfA)),
        Function.update_of_ne (hι.ne (by decide : PReg.tY ≠ .tA))]
      rw [hp7]; simp [ptbl, length_binSyms]; omega
    have hl₁₀ : (S₉.R (ι .tT)).length = kT := by
      simp only [hS₉, hS₈, hS₇, Function.update_of_ne (hι.ne (by decide : PReg.tT ≠ .cfY)),
        Function.update_of_ne (hι.ne (by decide : PReg.tT ≠ .tY)),
        Function.update_of_ne (hι.ne (by decide : PReg.tT ≠ .cfA)),
        Function.update_of_ne (hι.ne (by decide : PReg.tT ≠ .tA))]
      rw [hp7]; simp [ptbl, length_binSyms]
      have : kT ≤ d.lT := by
        rw [hkT]; split_ifs with h
        · exact hT h
        · exact Nat.zero_le _
      omega
    have hl₁₁ : (S₁₀.R (ι .w)).length = d.W := by rw [hw₁₀]; simp [length_binSyms]
    have hl₂ : (S₁.R (ι .WR)).length = d.W := by
      simp only [hS₁]; rw [hR₀k _ (hι.ne (by decide)), hWR, List.length_replicate]
    rw [hSa, hSt₃] at hm₄
    rw [hSy, hSt₄] at hm₅
    rw [hSn, hSt₅] at hm₆
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_replicate,
      List.length_nil] at hm₄ hm₅ hm₆
    rw [hl₈, hl₉, hl₁₀, hl₁₁, hl₂]
    have hkT' : kT ≤ d.lT := by
      rw [hkT]; split_ifs with h
      · exact hT h
      · exact Nat.zero_le _
    unfold prepCost
    have hnl : d.n * (colCost useT d + 5) = d.n * (colCost useT d + 3) + 2 * d.n := by ring
    omega
  · simp
  · intro k hk
    simp only [Function.update_of_ne hk, Function.update_apply]
    by_cases hx : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hx
      have hx' : x ≠ .comp := fun h => hk (by rw [h])
      simp only [hS₁₀, hS₉, hS₈, hS₇, Function.update_apply, hι.eq_iff]
      rw [hp7]
      cases x <;> simp [ptbl, hR₀, hι.eq_iff, hcfA, hcfY, hcfT, hw, htA, htY, htT, hcb, hcnt,
        show d.W - (pF + d.W) = 0 by omega] <;> exact absurd rfl hx'
    · push_neg at hx
      simp only [Function.update_of_ne (hx _).symm, hS₁₀, hS₉, hS₈, hS₇]
      rw [pst_ne useY useT d R₀ hι _ _ _ _ _ hx, hR₀k _ (hx .comp).symm, if_neg (hx .w).symm]

end Whole


/-! ### The preparation contract of the rotation pass -/

section Spec

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U) {nf : ℕ} (len : Fin nf → ℕ)

/-- The preparation registers inside the rotation pass: three fields, the computed register,
nine parameter registers and eight scratch registers. -/
def embedP (fA fY fT : Fin nf) : PReg → RotGReg nf 8 9
  | .cfA => .fld fA | .cfY => .fld fY | .cfT => .fld fT | .comp => .comp
  | .WR => .prm 0 | .oOR => .prm 1 | .oAR => .prm 2 | .oYR => .prm 3 | .sAR => .prm 4
  | .KR => .prm 5 | .GR => .prm 6 | .nR => .prm 7 | .padR => .prm 8
  | .cnt => .scr 0 | .w => .scr 1 | .t₁ => .scr 2 | .t₂ => .scr 3 | .tA => .scr 4
  | .tY => .scr 5 | .tT => .scr 6 | .cb => .scr 7

lemma embedP_injective {fA fY fT : Fin nf} (hAY : fA ≠ fY) (hAT : fA ≠ fT) (hYT : fY ≠ fT) :
    Function.Injective (embedP fA fY fT) := by
  intro x y h
  cases x <;> cases y <;> simp_all [embedP]

/-- The parameter constants of one preparation. -/
def prmP (W oO oA oY sA K G n pad : ℕ) : Fin 9 → List (Fin (A + 4)) :=
  ![List.replicate W tick, List.replicate oO tick, List.replicate oA tick, List.replicate oY tick,
    List.replicate sA tick, List.replicate K tick, List.replicate G tick, List.replicate n tick,
    List.replicate pad tick]

/-- The data of the preparation at index `i`. -/
def pdataP (fA fY fT : Fin nf) (W oO oA oY sA K G n pad i : ℕ) : PData where
  W := W
  oO := oO
  oA := oA
  oY := oY
  sA := sA
  K := K
  G := G
  n := n
  pad := pad
  lA := len fA
  xA := digit len fA i
  lY := len fY
  xY := digit len fY i
  lT := len fT
  xT := digit len fT i

/-- The word of the preparation is the uniform offset sum. -/
lemma pdataP_X (useY useT : Bool) (fA fY fT : Fin nf) (W oO oA oY sA K G n pad i : ℕ) :
    PData.X useY useT (pdataP len fA fY fT W oO oA oY sA K G n pad i) =
      offSum (fun c => coefU len useY useT fA fY fT oA sA oY K G c i) oO
        (1 + (if useT then G else 0) + pad) n := by
  unfold PData.X PData.sO offSum
  apply Finset.sum_congr rfl
  intro c _
  congr 1

/-- The offset preparation satisfies the preparation contract of the rotation pass, for any
offset function of the uniform form with control field `fA`, auxiliary field `fY` and digit
field `fT`. -/
theorem prepOff_spec {ι : RotGReg nf 8 9 → Fin T} (hι : Function.Injective ι) (tf fA fY fT : Fin nf)
    (hAY : fA ≠ fY) (hAT : fA ≠ fT) (hYT : fY ≠ fT) (useY useT : Bool)
    (oO oA oY sA K G n pad : ℕ) (hA : oA + n * sA ≤ len fA) (hY : oY + n * K ≤ len fY)
    (hT : useT = true → n * G ≤ len fT) (off : ℕ → ℕ)
    (hoff : ∀ i, off i = offSum (fun c => coefU len useY useT fA fY fT oA sA oY K G c i) oO
      (1 + (if useT then G else 0) + pad) n) :
    PrepSpec body (prepOff useY useT (ι ∘ embedP fA fY fT)) (fun g => ι (.fld g)) len (len tf)
      (fun r => ι (RotGReg.rsRegG tf r)) (fun r => ι (.spare r)) (rsrcR tf off)
      (fun s => ι (.scr s)) (fun q => ι (.prm q)) (prmP (len tf) oO oA oY sA K G n pad)
      (prepCost useT (pdataP len fA fY fT (len tf) oO oA oY sA K G n pad 0) (len tf)) where
  run := by
    intro i v S hI
    obtain ⟨hfld, hcomp, -, hscr, hprm⟩ := hI
    have hιP : Function.Injective (ι ∘ embedP fA fY fT) := hι.comp (embedP_injective hAY hAT hYT)
    set d := pdataP len fA fY fT (len tf) oO oA oY sA K G n pad i with hd
    have hxA : d.xA < 2 ^ d.lA := Nat.mod_lt _ (by positivity)
    have hxY : d.xY < 2 ^ d.lY := Nat.mod_lt _ (by positivity)
    have hxT : d.xT < 2 ^ d.lT := Nat.mod_lt _ (by positivity)
    obtain ⟨v', R', m, hu, hm, he, hc, hk⟩ := prepOff_exec body hιP useY useT d hxA hxY hxT hA hY hT
      v S (hfld fA) (hfld fY) (hfld fT) (hprm 0) (hprm 1) (hprm 2) (hprm 3) (hprm 4) (hprm 5)
      (hprm 6) (hprm 7) (hprm 8) (hscr 0) (hscr 1) (hscr 2) (hscr 3) (hscr 4) (hscr 5) (hscr 6)
      (hscr 7)
    refine ⟨v', R', m, hu, ?_, he, ?_, ?_⟩
    · have hL : (S.R ((ι ∘ embedP fA fY fT) .comp)).length = len tf := hcomp 1 off rfl
      rw [hL] at hm
      exact hm
    · intro r g hr
      fin_cases r
      · simp [rsrcR] at hr
      · simp [rsrcR] at hr
        subst hr
        rw [hoff i, ← pdataP_X]
        exact hc
    · intro k hk'
      exact hk k (hk' 1 off rfl)

end Spec

end IntegerMultBounds.MathlibTM2.Node
