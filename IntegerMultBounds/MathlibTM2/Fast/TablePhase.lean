module

public import IntegerMultBounds.MathlibTM2.Fast.TableExp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Taylor sums and roundings of the phase tables on the table machine

The phase tables (`Chirp.axisPhase`, `Pipeline.twistPlus`) are Taylor sums of `e^{ix}` for an
angle `x = X / 2^Q` with integer numerator `X`, rounded to a grid. Their integer numerators are
`TableNum.tblCre`, `TableNum.tblCim` (`TableNum.tbl_taylorExpI`), then `⌊(a + 2^d) / 2^(d+1)⌋`
(`roundC`, `TableNum.tbl_roundC`) or `((2^(p+2) − 1) a).tdiv 2^(q+2)` (`diskPhase`,
`TableNum.tbl_diskPhase`).

## Signed differences

Signs travel as bits. `tblSdL` computes from naturals `E`, `F` the bit `[E < F]` as
`⌊2F / (E + F + 1)⌋` (`tbl_sd_neg`) and `|E − F| = E + F − 2 min(E, F)` (`tbl_sd_mag`), so that
`± |E − F| = E − F` (`tbl_sd_val`); `tblXorL` combines two sign bits (`tbl_xor_val`).

## Machines

* `tblTaylorCode` (36 variables): the magnitude loop `tblMagCode` on variables `0 … 17`, then the
  signed differences `S₀ − S₂` and `S₁ − S₃` and the imaginary sign. `tblTaylor_do`: for
  `Y ≤ 4 · 2^Q` and `q + Q + size n + 10 ≤ W`, the outputs are `tblCre Y q Q n` and
  `tblCim xneg Y q Q n` in sign–magnitude form, within `39 n + 56` atoms. `tblTaylor_exp`: for
  `Y = |X|`, `xneg = [X < 0]`, they are the numerators of `taylorExpI q (X / 2^Q) n`.
* `tblRoundCode`, `tblRound_do`: `⌊(D + 2^d − [neg]) / 2^(d+1)⌋` with the sign of `a = ±D` is
  `⌊(a + 2^d) / 2^(d+1)⌋` (`tbl_round_signed`), the `roundC` numerator.
* `tblDiskCode`, `tblDisk_do`: `⌊(2^(p+2) − 1) D / 2^(q+2)⌋` with the sign of `a = ±D` is
  `((2^(p+2) − 1) a).tdiv 2^(q+2)` (`tbl_disk_signed`), the `diskPhase` numerator.

## Known values

`tblKV s l`: the state holds `e.2` in variable `e.1` for each `e ∈ l`; `tblKV.frame` keeps known
values off the written variables. `tblPow2_kv` and `tblClog_kv` (`⌈log₂ N⌉` by doubling,
`tblClogCode`) are stated on known values.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Fast.TableNum


/-- The comparison bit `[E < F]`. -/
def tblSdNeg (E F : ℕ) : ℕ := if E < F then 1 else 0

/-- The distance `|E − F|`. -/
def tblSdMag (E F : ℕ) : ℕ := if E < F then F - E else E - F

theorem tbl_sd_neg (E F : ℕ) : (F + F) / (E + F + 1) = tblSdNeg E F := by
  unfold tblSdNeg
  split_ifs with h
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

theorem tbl_sd_mag (E F : ℕ) :
    E + F - (E * tblSdNeg E F + F * (1 - tblSdNeg E F) + (E * tblSdNeg E F + F * (1 - tblSdNeg E F))) =
      tblSdMag E F := by
  unfold tblSdNeg tblSdMag
  split_ifs with h <;> simp <;> omega

theorem tbl_sd_val (E F : ℕ) :
    tblSgn (decide (tblSdNeg E F = 1)) * (tblSdMag E F : ℤ) = (E : ℤ) - F := by
  unfold tblSdNeg tblSdMag tblSgn
  by_cases h : E < F
  · simp only [h, ite_true, decide_true]
    push_cast [Nat.cast_sub h.le]; ring
  · simp only [h, ite_false]
    push_cast [Nat.cast_sub (not_lt.1 h)]; simp

theorem tbl_sdNeg_le (E F : ℕ) : tblSdNeg E F ≤ 1 := by unfold tblSdNeg; split_ifs <;> omega

theorem tbl_sd_min (E F : ℕ) : E * tblSdNeg E F + F * (1 - tblSdNeg E F) = min E F := by
  unfold tblSdNeg; split_ifs <;> simp <;> omega

theorem tbl_sd_le (E F : ℕ) : E * tblSdNeg E F ≤ E ∧ F * (1 - tblSdNeg E F) ≤ F := by
  unfold tblSdNeg; split_ifs <;> simp

theorem tbl_sdMag_le (E F : ℕ) : tblSdMag E F ≤ max E F := by unfold tblSdMag; split_ifs <;> omega

/-- The signed difference `E − F` as the bit `[E < F]` into `neg` and `|E − F|` into `D`, from
`one = 1`, through `t₁ t₂ t₃`. -/
def tblSdL {n : ℕ} (E F one t₁ t₂ t₃ neg D : Fin n) : List (TblIns n) :=
  [.add E F t₁, .inc t₁, .add F F t₂, .div t₂ t₁ neg, .mul E neg t₂, .sub one neg t₃, .mul F t₃ t₃,
    .add t₂ t₃ t₂, .add t₂ t₂ t₂, .add E F t₁, .sub t₁ t₂ D]

/-- The exclusive or of two bits `a b` into `c`, through `t`. -/
def tblXorL {n : ℕ} (a b t c : Fin n) : List (TblIns n) :=
  [.mul a b t, .add t t t, .add a b c, .sub c t c]

theorem tbl_xor_val (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) :
    a + b - (a * b + a * b) ≤ 1 ∧
      tblSgn (decide (a + b - (a * b + a * b) = 1)) = tblSgn (decide (a = 1)) * tblSgn (decide (b = 1)) := by
  interval_cases a <;> interval_cases b <;> simp [tblSgn]

/-! ### The Taylor machine -/

local notation "cS0" => (4 : Fin 36)
local notation "cS1" => (5 : Fin 36)
local notation "cS2" => (6 : Fin 36)
local notation "cS3" => (7 : Fin 36)
local notation "cX" => (18 : Fin 36)
local notation "cOne" => (19 : Fin 36)
local notation "cRN" => (20 : Fin 36)
local notation "cRM" => (21 : Fin 36)
local notation "cIN" => (22 : Fin 36)
local notation "cIM" => (23 : Fin 36)
local notation "cT1" => (24 : Fin 36)
local notation "cT2" => (25 : Fin 36)
local notation "cT3" => (26 : Fin 36)
local notation "cN1" => (27 : Fin 36)

/-- The Taylor machine on 36 variables: the magnitude loop on variables `0 … 17`
(`Y, 2^q, 2^Q, n` in `0 … 3`), then the signed differences `S₀ − S₂` into `(20, 21)` and
`S₁ − S₃` into `(27, 23)`, and the imaginary sign `[S₁ < S₃] ⊕ xneg` into `22`, with `xneg` in
`18` and `1` in `19`. -/
def tblTaylorCode : TblCode 36 :=
  tblMagCode.rename (Fin.castLE (by norm_num : 18 ≤ 36)) ;;
    tblBlock 36 (tblSdL cS0 cS2 cOne cT1 cT2 cT3 cRN cRM ++ tblSdL cS1 cS3 cOne cT1 cT2 cT3 cN1 cIM ++
      [.mul cN1 cX cT1, .add cT1 cT1 cT1, .add cN1 cX cIN]) (.sub cIN cT1 cIN)

theorem tbl_pow_bound {n q W : ℕ} (hW : q + Nat.size n ≤ W) : n * 2 ^ q < 2 ^ W := by
  have h1 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  calc n * 2 ^ q < 2 ^ Nat.size n * 2 ^ q := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos q)
    _ = 2 ^ (Nat.size n + q) := by rw [pow_add]
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem tblTaylor_do {A W w : ℕ} (st : TblSt 36 A) {Y q Q n : ℕ} (xneg : Bool)
    (hY : st.val 0 = Y) (hpq : st.val 1 = 2 ^ q) (hpQ : st.val 2 = 2 ^ Q) (hn : st.val 3 = n)
    (hx : st.val 18 = xneg.toNat) (hone : st.val 19 = 1) (hYb : Y ≤ 4 * 2 ^ Q)
    (hW : q + Q + Nat.size n + 10 ≤ W) :
    TblDo A W w tblTaylorCode st (fun s =>
      tblSgn (decide (s.val 20 = 1)) * (s.val 21 : ℤ) = tblCre Y q Q n ∧ s.val 20 ≤ 1 ∧
      tblSgn (decide (s.val 22 = 1)) * (s.val 23 : ℤ) = tblCim xneg Y q Q n ∧ s.val 22 ≤ 1 ∧
      s.val 21 ≤ n * 2 ^ (q + 6) ∧ s.val 23 ≤ n * 2 ^ (q + 6) ∧
      s.val 1 = 2 ^ q ∧ s.val 2 = 2 ^ Q ∧ s.val 3 = n ∧ s.val 19 = 1 ∧ s.acc = st.acc)
      (39 * n + 56) := by
  have hf : Function.Injective (Fin.castLE (by norm_num : 18 ≤ 36)) := Fin.castLE_injective _
  have hB : n * 2 ^ (q + 6) * 4 < 2 ^ W := by
    have := tbl_pow_bound (n := n) (q := q + 8) (W := W) (by omega)
    rw [show q + 8 = (q + 6) + 2 by ring, pow_add] at this; linarith
  have hnW : n < 2 ^ W := by
    have := tbl_pow_bound (n := n) (q := 0) (W := W) (by omega); simpa using this
  have hml : ∀ m, tblMag Y q Q m < 2 ^ (q + 6) := fun m => tbl_mag_lt Y q Q m hYb
  have hsl : ∀ r m, m ≤ n → tblSum Y q Q r m ≤ n * 2 ^ (q + 6) := fun r m hm =>
    (tbl_sum_le Y q Q r m hYb).trans (Nat.mul_le_mul_right _ hm)
  have hq6 : 2 ^ (q + 6) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmag := TblDo.rename (W := W) (w := w) hf (c := tblMagCode) (st := st)
    (tblMag_do (st.restrict _) (Y := Y) (q := q) (Q := Q) (N := n) hY hpq hpQ hn (by omega) hnW
      (fun m _ => lt_of_lt_of_le (hml m) hq6)
      (fun m _ => by
        have h1 := hml m
        have h2 : 2 ^ (q + 6) * (4 * 2 ^ Q) ≤ 2 ^ W := by
          rw [show 4 * 2 ^ Q = 2 ^ (Q + 2) by rw [pow_add]; ring, ← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        calc tblMag Y q Q m * Y ≤ tblMag Y q Q m * (4 * 2 ^ Q) := Nat.mul_le_mul_left _ hYb
          _ < 2 ^ (q + 6) * (4 * 2 ^ Q) := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
          _ ≤ 2 ^ W := h2)
      (by
        have := tbl_pow_bound (n := n) (q := Q) (W := W) (by omega)
        rwa [mul_comm] at this)
      (fun r _ m hm => by have := hsl r m hm; omega))
  have hout : ∀ x : Fin 36, 18 ≤ x.val → ∀ y : Fin 18, Fin.castLE (by norm_num : 18 ≤ 36) y ≠ x :=
    fun x hx y h => by have := congrArg Fin.val h; simp at this; omega
  refine (hmag.seq (K₂ := 26) (fun s ⟨⟨hS, hy, hpq', hpQ', hn', hacc⟩, hfr⟩ => ?_)).mono
    (fun _ h => h) (by omega)
  have h0 : s.val 4 = tblSum Y q Q 0 n := hS 0
  have h1 : s.val 5 = tblSum Y q Q 1 n := hS 1
  have h2 : s.val 6 = tblSum Y q Q 2 n := hS 2
  have h3 : s.val 7 = tblSum Y q Q 3 n := hS 3
  have hpq1 : s.val 1 = 2 ^ q := hpq'
  have hpQ1 : s.val 2 = 2 ^ Q := hpQ'
  have hn1 : s.val 3 = n := hn'
  have hx1 : s.val 18 = xneg.toNat := (hfr 18 (hout 18 (by decide))).trans hx
  have hone1 : s.val 19 = 1 := (hfr 19 (hout 19 (by decide))).trans hone
  have b0 := hsl 0 n le_rfl
  have b1 := hsl 1 n le_rfl
  have b2 := hsl 2 n le_rfl
  have b3 := hsl 3 n le_rfl
  have hxb : xneg.toNat ≤ 1 := Bool.toNat_le xneg
  have l02 := tbl_sd_le (tblSum Y q Q 0 n) (tblSum Y q Q 2 n)
  have l13 := tbl_sd_le (tblSum Y q Q 1 n) (tblSum Y q Q 3 n)
  have n13 := tbl_sdNeg_le (tblSum Y q Q 1 n) (tblSum Y q Q 3 n)
  have n02 := tbl_sdNeg_le (tblSum Y q Q 0 n) (tblSum Y q Q 2 n)
  have hxp1 : tblSdNeg (tblSum Y q Q 1 n) (tblSum Y q Q 3 n) * xneg.toNat ≤
      tblSdNeg (tblSum Y q Q 1 n) (tblSum Y q Q 3 n) := by
    have := Nat.mul_le_mul_left (tblSdNeg (tblSum Y q Q 1 n) (tblSum Y q Q 3 n)) hxb
    simpa using this
  have hxp2 : tblSdNeg (tblSum Y q Q 1 n) (tblSum Y q Q 3 n) * xneg.toNat ≤ xneg.toNat := by
    have := Nat.mul_le_mul_right xneg.toNat n13
    simpa using this
  have h4W : 4 ≤ 2 ^ W := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine TblDo.block _ _ ?_ ?_
  · simp [tblSdL, tblFitsList, TblIns.fits, TblIns.exact, h0, h1, h2, h3,
      hx1, hone1, tbl_sd_neg, tbl_sd_min]
    and_intros
    all_goals omega
  · simp [tblSdL, tblExactList, TblIns.exact, h0, h1, h2, h3,
      hx1, hone1, tbl_sd_neg, tbl_sd_mag, hpq1, hpQ1, hn1]
    obtain ⟨hxa, hxs⟩ := tbl_xor_val _ _ n13 hxb
    have m02 := tbl_sdMag_le (tblSum Y q Q 0 n) (tblSum Y q Q 2 n)
    have m13 := tbl_sdMag_le (tblSum Y q Q 1 n) (tblSum Y q Q 3 n)
    refine ⟨by rw [tbl_sd_val]; rfl, n02, ?_, by omega, by omega, by omega, hacc⟩
    rw [hxs, mul_comm (tblSgn _) (tblSgn (decide (xneg.toNat = 1))), mul_assoc, tbl_sd_val]
    unfold tblCim
    cases xneg <;> rfl

/-- **Taylor machine, real form.** For `Y = |X|` and `xneg = [X < 0]`, the sign–magnitude outputs
of `tblTaylorCode` are the numerators of `taylorExpI q (X / 2^Q) n` at `q` bits. -/
theorem tblTaylor_exp {A W w : ℕ} (st : TblSt 36 A) (X : ℤ) {q Q n : ℕ}
    (hY : st.val 0 = X.natAbs) (hpq : st.val 1 = 2 ^ q) (hpQ : st.val 2 = 2 ^ Q) (hn : st.val 3 = n)
    (hx : st.val 18 = (decide (X < 0)).toNat) (hone : st.val 19 = 1)
    (hYb : X.natAbs ≤ 4 * 2 ^ Q) (hW : q + Q + Nat.size n + 10 ≤ W) :
    TblDo A W w tblTaylorCode st (fun s =>
      IntegerMultBounds.MathlibTM2.Mult.ComplexConv.taylorExpI q ((X : ℝ) / 2 ^ Q) n =
        ⟨((tblSgn (decide (s.val 20 = 1)) * s.val 21 : ℤ) : ℝ) / 2 ^ q,
          ((tblSgn (decide (s.val 22 = 1)) * s.val 23 : ℤ) : ℝ) / 2 ^ q⟩) (39 * n + 56) :=
  (tblTaylor_do st (decide (X < 0)) hY hpq hpQ hn hx hone hYb hW).mono
    (fun s h => by rw [tbl_taylorExpI, h.1, h.2.2.1]) le_rfl

/-! ### Roundings -/

theorem tbl_neg_ediv (a m : ℕ) (hm : 0 < m) :
    (-(a : ℤ) + ((m - 1 : ℕ) : ℤ)) / (m : ℤ) = -((a / m : ℕ) : ℤ) := by
  have h1 := Nat.div_add_mod a m
  have h2 := Nat.mod_lt a hm
  have hq := (Int.ediv_emod_unique (a := -(a : ℤ) + ((m - 1 : ℕ) : ℤ)) (b := (m : ℤ))
    (r := ((m - 1 - a % m : ℕ) : ℤ)) (q := -((a / m : ℕ) : ℤ)) (by exact_mod_cast hm)).2
  refine (hq ⟨?_, by positivity, by omega⟩).1
  have h1' : (a : ℤ) = (m : ℤ) * ((a / m : ℕ) : ℤ) + ((a % m : ℕ) : ℤ) := by exact_mod_cast h1.symm
  rw [Nat.cast_sub (by omega : a % m ≤ m - 1), Nat.cast_sub (by omega : 1 ≤ m)]
  push_cast
  linarith

/-- Rounding to nearest of a signed numerator: `⌊(±D + 2^d) / 2^(d+1)⌋` is `±⌊(D + 2^d − [neg]) / 2^(d+1)⌋`. -/
theorem tbl_round_signed (neg : Bool) (D d : ℕ) :
    (tblSgn neg * (D : ℤ) + 2 ^ d) / 2 ^ (d + 1) =
      tblSgn neg * (((D + 2 ^ d - neg.toNat) / 2 ^ (d + 1) : ℕ) : ℤ) := by
  cases neg
  · simp only [tblSgn, Bool.false_eq_true, ite_false, one_mul, Bool.toNat_false, Nat.sub_zero]
    push_cast
    rfl
  · simp only [tblSgn, ite_true, neg_mul, one_mul, Bool.toNat_true]
    have hd : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have e := tbl_neg_ediv (D + 2 ^ d - 1) (2 ^ (d + 1)) (Nat.two_pow_pos _)
    rw [← e]
    congr 1
    rw [pow_succ]
    push_cast [Nat.cast_sub hd, Nat.cast_sub (show 1 ≤ 2 ^ d * 2 by omega),
      Nat.cast_sub (show 1 ≤ D + 2 ^ d by omega)]
    ring

/-- The `diskPhase` truncation of a signed numerator: `(c (±D)).tdiv den = ±⌊c D / den⌋`. -/
theorem tbl_disk_signed (neg : Bool) (D c den : ℕ) :
    ((c : ℤ) * (tblSgn neg * D)).tdiv den = tblSgn neg * ((c * D / den : ℕ) : ℤ) := by
  rw [mul_left_comm, tbl_tdiv_unit (by unfold tblSgn; split_ifs <;> simp),
    Int.tdiv_eq_ediv_of_nonneg (by positivity)]
  push_cast
  rfl

/-- Rounding to nearest on 5 variables: `out := ⌊(D + h − neg) / hh⌋` from `neg` in `0`, `D` in
`1`, `h = 2^d` in `2`, `hh = 2^(d+1)` in `3`, into `4`. -/
def tblRoundCode : TblCode 5 := tblBlock 5 [.add 1 2 4, .sub 4 0 4] (.div 4 3 4)

/-- **Rounding machine.** The result is the numerator `⌊(a + 2^d) / 2^(d+1)⌋` of `roundC` for
`a = ±D` (`tbl_roundC`), with the sign of `a`. -/
theorem tblRound_do {A W w : ℕ} (st : TblSt 5 A) (neg : Bool) {D d : ℕ}
    (h0 : st.val 0 = neg.toNat) (h1 : st.val 1 = D) (h2 : st.val 2 = 2 ^ d)
    (h3 : st.val 3 = 2 ^ (d + 1)) (hW : D + 2 ^ d < 2 ^ W) :
    TblDo A W w tblRoundCode st (fun s =>
      tblSgn neg * (s.val 4 : ℤ) = (tblSgn neg * (D : ℤ) + 2 ^ d) / 2 ^ (d + 1) ∧
      s.acc = st.acc) 3 := by
  have hb : neg.toNat ≤ 1 := Bool.toNat_le neg
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, h0, h1, h2]
    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    omega
  · simp [tblExactList, TblIns.exact, h0, h1, h2, h3, tbl_round_signed]

/-- The `diskPhase` truncation on 5 variables: `out := ⌊c D / den⌋` from `D` in `0`, `c` in `1`,
`den` in `2`, into `3`. -/
def tblDiskCode : TblCode 5 := tblBlock 5 [.mul 1 0 3] (.div 3 2 3)

/-- **Disk truncation machine.** With `c = 2^(p+2) − 1` and `den = 2^(q+2)`, the result with the
sign of `a = ±D` is the numerator `((2^(p+2) − 1) a).tdiv 2^(q+2)` of `diskPhase p`
(`tbl_diskPhase`). -/
theorem tblDisk_do {A W w : ℕ} (st : TblSt 5 A) (neg : Bool) {D p q : ℕ}
    (h0 : st.val 0 = D) (h1 : st.val 1 = 2 ^ (p + 2) - 1) (h2 : st.val 2 = 2 ^ (q + 2))
    (hW : (2 ^ (p + 2) - 1) * D < 2 ^ W) :
    TblDo A W w tblDiskCode st (fun s =>
      tblSgn neg * (s.val 3 : ℤ) = ((2 ^ (p + 2) - 1) * (tblSgn neg * (D : ℤ))).tdiv (2 ^ (q + 2)) ∧
      s.acc = st.acc) 2 := by
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, h0, h1]
    exact hW
  · have hv : (tblExactList A w ([.mul 1 0 3] ++ [.div 3 2 3]) st).val 3 =
        (2 ^ (p + 2) - 1) * D / 2 ^ (q + 2) := by
      simp [tblExactList, TblIns.exact, h0, h1, h2]
    refine ⟨?_, by simp [tblExactList, TblIns.exact]⟩
    have hc : ((2 ^ (p + 2) - 1 : ℕ) : ℤ) = 2 ^ (p + 2) - 1 := by
      push_cast [Nat.cast_sub (Nat.one_le_two_pow)]; ring
    rw [hv, ← hc, show ((2 : ℤ) ^ (q + 2)) = ((2 ^ (q + 2) : ℕ) : ℤ) by push_cast; ring,
      tbl_disk_signed]

/-! ### Known values -/

/-- The state `s` holds the value `e.2` in variable `e.1` for every `e ∈ l`. -/
def tblKV {n A : ℕ} (s : TblSt n A) (l : List (Fin n × ℕ)) : Prop := ∀ e ∈ l, s.val e.1 = e.2

theorem tblKV.frame {n A : ℕ} {s s' : TblSt n A} {l : List (Fin n × ℕ)} (h : tblKV s l)
    (M : List (Fin n)) (hfr : ∀ x, x ∉ M → s'.val x = s.val x) (hd : ∀ e ∈ l, e.1 ∉ M) :
    tblKV s' l := fun e he => (hfr e.1 (hd e he)).trans (h e he)

theorem tblKV.get {n A : ℕ} {s : TblSt n A} {l : List (Fin n × ℕ)} (h : tblKV s l) {k : Fin n}
    {v : ℕ} (hk : (k, v) ∈ l) : s.val k = v := h _ hk

theorem tblKV.cons {n A : ℕ} {s : TblSt n A} {l : List (Fin n × ℕ)} {k : Fin n} {v : ℕ}
    (h1 : s.val k = v) (h : tblKV s l) : tblKV s ((k, v) :: l) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact h1
  · exact h e he

theorem tblKV.sub {n A : ℕ} {s : TblSt n A} {l l' : List (Fin n × ℕ)} (h : tblKV s l)
    (hl : ∀ e ∈ l', e ∈ l) : tblKV s l' := fun e he => h e (hl e he)

/-- `tblPow2` on known values: `c := 2^E` for `(e, E)` known, the other known values kept. -/
theorem tblPow2_kv {n A W w : ℕ} {c e i : Fin n} (hce : c ≠ e) (hci : c ≠ i) (hei : e ≠ i)
    {L : List (Fin n × ℕ)} (hL : ∀ x ∈ L, x.1 ∉ [c, i]) {E : ℕ} (he : (e, E) ∈ L) (hEW : E < W)
    (s : TblSt n A) (hs : tblKV s L) :
    TblDo A W w (tblPow2 c e i) s (fun s' => tblKV s' ((c, 2 ^ E) :: L) ∧ s'.acc = s.acc)
      (4 * E + 5) := by
  have hE : s.val e = E := hs.get he
  refine (tblPow2_do hce hci hei s (by rw [hE]; exact hEW)).mono (fun s' ⟨h1, _, h3, h4⟩ => ⟨?_, h4⟩)
    (by rw [hE])
  refine tblKV.cons (by rw [h1, hE]) (hs.frame [c, i] (fun x hx => ?_) hL)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  exact h3 x hx.1 hx.2

/-! ### The ceiling logarithm -/

/-- `c := ⌈log₂ N⌉` (`Nat.clog 2 N`) by doubling `pw` from `1` while `pw < N`. -/
def tblClogCode {n : ℕ} (pw c nv : Fin n) : TblCode n :=
  tblBlock n [.zero c, .zero pw] (.inc pw) ;; .loop pw nv (tblBlock n [.add pw pw pw] (.inc c))

theorem tbl_two_pow_clog_le (N : ℕ) : 2 ^ Nat.clog 2 N ≤ 2 * N ∨ N = 0 := by
  rcases Nat.lt_or_ge N 2 with h | h
  · rcases N with _ | _ | N
    · right; rfl
    · left; simp
    · omega
  · left
    have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (by omega : 1 < N)
    have h2 := Nat.clog_pos (b := 2) (by norm_num) (by omega : 1 < N)
    have : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N).pred := by
      rw [← pow_succ']; congr 1; rw [Nat.pred_eq_sub_one]; omega
    omega

/-- `tblClogCode`: `c = clog 2 N`, `pw = 2^c`, the known values off `pw`, `c` kept. -/
theorem tblClog_kv {n A W w : ℕ} {pw c nv : Fin n} (hpc : pw ≠ c) (hpn : pw ≠ nv) (hcn : c ≠ nv)
    {L : List (Fin n × ℕ)} (hL : ∀ x ∈ L, x.1 ∉ [pw, c]) {N : ℕ} (hN : (nv, N) ∈ L)
    (h1N : 1 ≤ N) (hNW : 2 * N < 2 ^ W) (s : TblSt n A) (hs : tblKV s L) :
    TblDo A W w (tblClogCode pw c nv) s (fun s' =>
      tblKV s' ((c, Nat.clog 2 N) :: (pw, 2 ^ Nat.clog 2 N) :: L) ∧ s'.acc = s.acc)
      (3 + (Nat.clog 2 N * (1 + 1 + 2) + 2)) := by
  have hNv : s.val nv = N := hs.get hN
  have hcl : 2 ^ Nat.clog 2 N ≤ 2 * N := (tbl_two_pow_clog_le N).resolve_right (by omega)
  have hclW : Nat.clog 2 N < 2 ^ W :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (by omega)
  let Inv : ℕ → TblSt n A → Prop := fun j s' => s'.val pw = 2 ^ j ∧ s'.val c = j ∧
    (∀ x, x ≠ pw → x ≠ c → s'.val x = s.val x) ∧ s'.acc = s.acc
  refine (TblDo.block _ _ (P := Inv 0) ?_ ?_).seq (fun s₁ h₁ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact]
    rintro rfl
    simp at hNW
    omega
  · refine ⟨by simp [tblExactList, TblIns.exact], ?_, fun x h1 h2 => ?_, by simp [tblExactList, TblIns.exact]⟩
    · simp [tblExactList, TblIns.exact, Function.update_of_ne hpc.symm]
    · simp [tblExactList, TblIns.exact, Function.update_of_ne h1, Function.update_of_ne h2]
  refine TblDo.loop Inv (Nat.clog 2 N) 2 h₁ ?_ ?_
  · intro j hj s' ⟨hp, hc, hx, ha⟩
    have hlt : 2 ^ j < N := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hj
    have hnv : s'.val nv = N := by rw [hx nv hpn.symm hcn.symm, hNv]
    refine ⟨by rw [hp, hnv]; exact hlt, TblDo.block _ _ ?_ ?_⟩
    · simp [tblFitsList, TblIns.fits, TblIns.exact, Function.update_of_ne hpc.symm, hp, hc]
      have : 2 ^ (j + 1) ≤ 2 ^ Nat.clog 2 N := Nat.pow_le_pow_right (by norm_num) hj
      rw [pow_succ] at this
      constructor <;> omega
    · refine ⟨?_, ?_, fun x h1 h2 => ?_, ?_⟩
      · simp [tblExactList, TblIns.exact, Function.update_of_ne hpc, hp, pow_succ]; ring
      · simp [tblExactList, TblIns.exact, Function.update_of_ne hpc.symm, hc]
      · simp [tblExactList, TblIns.exact, Function.update_of_ne h1, Function.update_of_ne h2, hx x h1 h2]
      · simp [tblExactList, TblIns.exact, ha]
  · intro s' ⟨hp, hc, hx, ha⟩
    have hnv : s'.val nv = N := by rw [hx nv hpn.symm hcn.symm, hNv]
    refine ⟨by rw [hp, hnv]; exact not_lt.2 (Nat.le_pow_clog (by norm_num) N), ?_, ha⟩
    refine tblKV.cons hc (tblKV.cons hp (hs.frame [pw, c] (fun x hx' => ?_) hL))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    exact hx x hx'.1 hx'.2

end IntegerMultBounds.MathlibTM2.Fast.TableVM
