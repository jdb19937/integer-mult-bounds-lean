module

public import IntegerMultBounds.MathlibTM2.Host.SSMul
public import IntegerMultBounds.MathlibTM2.Node.Params
public import IntegerMultBounds.MathlibTM2.Layer.Format
import IntegerMultBounds.MathlibTM2.Fast.Output

/-!
# The rounding stage of the fast multiplier

The computed convolution ends as Gaussian grid values `N i / 2^p`, and coefficient `i` of
`pipelineCoeffs` is `rndCoeff b S p (N i).re`, the rounded `2^(2b) S · 16 S · (N i).re / 2^p`
truncated to a natural number (`rndCoeff_complex` matches the complex expression of
`Pipeline.pipelineCoeffs` for `computed … i = N i / 2^p`). `roundStage` turns the coefficient
stream of the numerators into the words `binSyms W (rndCoeff …)` that `carryOut` (`Fast/Output`)
reads.

**Arithmetic.**
* `rndDiv_round`: `round (X / 2^p) = X / 2^p + rndBit p X` for natural `X`, where `rndBit p X` is
  bit `p - 1` of `X` (`false` for `p = 0`); Mathlib's `round x` is `⌊x + 1/2⌋`.
* `rnd_val_testBit`: for `|x| < 2^(w-1)`, bit `w - 1` of the residue of `x` modulo `2^w` is the
  sign of `x`, and the residue is `x` for `x ≥ 0`.
* `rndMag w v`: the residue `v` when its bit `w - 1` is clear, `0` when it is set.
* `rndCoeff_eq`: `rndDiv p (2^(2b+4) · rndMag w (x mod 2^w) · S²) = rndCoeff b S p x`; a negative
  `x` gives `0` on both sides.

**Registers.** `rg : RndReg → Fin T` is injective and disjoint from the 64 registers `ι j` of the
Schönhage–Strassen multiplier, which are empty (both stacks) before and after.
* `src`: the coefficient stream `(List.ofFn fun i => red w (N i)).flatMap (coeffSyms A w)`; it is
  consumed (ends empty).
* `dst`: gains `(List.ofFn fun i => rndCoeff b S p (N i).re).flatMap (binSyms W)` on top, word `0`
  on top and each word least significant bit first. From an empty `dst` this is the data register
  of `carryOut`.
* `wn`, `mn`, `nn`, `bn`, `pn`, `wo`: `w`, `m`, `topN m`, `b`, `p`, `W` in unary (any symbols);
  restored.
* `sq`: `binSyms m (S * S)`; restored. `rndSquare` computes it once from `binSyms ℓ S` on `sb`, with
  `topN ℓ` and `m - (topN ℓ + 1)` in unary on `ns` and `pd` (`rndSquare_exec`).
* `tm`, `u1`, `sg`, `xa`, `xc`, `cy`, `acc`: scratch, empty before and after.

**One coefficient** (`rndCoeffProg`), with `v` the residue of `(N i).re` modulo `2^w`:
* Phase A (`rndPhaseA`): `w` pair symbols of `src` give their real bits on `u1`, most significant
  on top (`rndMapAct`, counted by `wn`); the top bit, the sign, goes onto `sg`; `xa` receives
  `m - w` zero bits (`zeroBits` by `mn`, `usub` by `wn`) and then the `w` bits of `u1` masked by
  the sign, so `xa = binSyms m (rndMag w v)`.
* Phase B (`rndPhaseB`): `ssMul` on `m`-bit operands pushes `binSyms (topN m + 1) (mag · S²)` onto
  `xc`; `2b + 4` zero bits pushed on top shift it, so `xc = binSyms (2b + 4 + topN m + 1) X` with
  `X = 2^(2b+4) · mag · S²`.
* Phase C (`rndPhaseC`): `p` bits of `xc` are dropped and the last one is kept on `cy`
  (`rndDropAct`, counted by `pn`); `W` bits of `X / 2^p` plus that bit go onto `acc` through an
  increment with its carry on `cy` (`rndIncAct`, counted by `wo`); `cy` and `xc` are cleared.

`rndWhile` repeats one coefficient while `src` is nonempty (`w ≥ 1`), and `moveR` moves `acc`
(latest word on top, most significant bit first) onto `dst`.

**Result** (`roundStage_exec`): the exact final stacks, the `user` component unchanged, within
`roundStageCost T m w b p W S = S · (SS + 12 w + 14 m + 12 b + 4 p + 6 W + 58) + 4` steps, where
`SS = (T + 773) · ssCostBound m + 164 m + 463` bounds one `ssMul` on `m`-bit operands
(`ssMul_exec`); `roundStageCost_le` replaces `SS` by `ssMulConst (T + 1) m (log m + 1)
(log log m + 1)`. Conditions: `4 ≤ A`, `1 ≤ w ≤ m`, `S² < 2^m`, `|(N i).re| < 2^(w-1)`. The words
carry the low `W` bits of each coefficient; `carryOut_exec` needs every coefficient below `2^W`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Schoenhage.Schedule (topN topN_facts)


/-! ### Rounding arithmetic -/

/-- The rounded coefficient `(round (2^(2b) S · 16 S · x / 2^p)).toNat` for the real part `x` of a
numerator. -/
noncomputable def rndCoeff (b S p : ℕ) (x : ℤ) : ℕ :=
  (round ((2 ^ (2 * b) * S * 16 * S : ℝ) * ((x : ℝ) / 2 ^ p))).toNat

/-- The rounding bit: bit `p - 1` of `X`, `false` for `p = 0`. -/
def rndBit (p X : ℕ) : Bool := decide (p ≠ 0) && X.testBit (p - 1)

/-- `X / 2^p` rounded half up: the quotient plus the rounding bit. -/
def rndDiv (p X : ℕ) : ℕ := X / 2 ^ p + (rndBit p X).toNat

/-- `rndDiv p X` is Mathlib's `round` of `X / 2^p`. -/
theorem rndDiv_round (p X : ℕ) : round ((X : ℝ) / 2 ^ p) = (rndDiv p X : ℤ) := by
  rw [round_eq, Int.floor_eq_iff]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [rndDiv, rndBit]
    norm_num
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  set P := 2 ^ k with hP
  have hP0 : 0 < P := by positivity
  have h2 : (2 : ℕ) ^ (k + 1) = 2 * P := by rw [pow_succ]; ring
  have hq := Nat.div_add_mod X (2 * P)
  have hr := Nat.mod_lt X (show 0 < 2 * P by omega)
  set q := X / (2 * P)
  set r := X % (2 * P)
  have hbit : X.testBit k = decide (P ≤ r) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have e : X / P = 2 * q + r / P := by
      rw [← hq, show 2 * P * q + r = r + P * (2 * q) by ring, Nat.add_mul_div_left _ _ hP0]
      ring
    rw [e]
    by_cases h : P ≤ r
    · have : r / P = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      simp [h, this, Nat.add_mod]
    · have : r / P = 0 := Nat.div_eq_of_lt (by omega)
      simp [h, this]
  have hn : rndDiv (k + 1) X = q + (decide (P ≤ r)).toNat := by
    simp [rndDiv, rndBit, hbit, h2, q]
  rw [hn]
  have hX : (X : ℝ) = 2 * P * q + r := by exact_mod_cast hq.symm
  have hPr : (P : ℝ) = 2 ^ k := by simp [hP]
  have h2r : (2 : ℝ) ^ (k + 1) = 2 * P := by rw [hPr, pow_succ]; ring
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP0
  have e : (X : ℝ) / 2 ^ (k + 1) + 1 / 2 = q + (r + P) / (2 * P) := by
    rw [h2r, hX]; field_simp; ring
  rw [e]
  have hrlt : (r : ℝ) < 2 * P := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := by positivity
  by_cases h : P ≤ r
  · have hr' : (P : ℝ) ≤ r := by exact_mod_cast h
    simp only [h, decide_true, Bool.toNat_true]
    push_cast
    constructor
    · have : (1 : ℝ) ≤ (r + P) / (2 * P) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    · have : ((r : ℝ) + P) / (2 * P) < 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
      linarith
  · have hr' : (r : ℝ) < P := by exact_mod_cast (not_le.1 h)
    simp only [h, decide_false, Bool.toNat_false]
    push_cast
    constructor
    · have : (0 : ℝ) ≤ (r + P) / (2 * P) := by positivity
      linarith
    · have : ((r : ℝ) + P) / (2 * P) < 1 := by rw [div_lt_iff₀ (by positivity)]; linarith
      linarith

/-- The sign bit of a two's complement residue. -/
theorem rnd_val_testBit {w : ℕ} (hw : 1 ≤ w) {x : ℤ} (hx : |x| < 2 ^ (w - 1)) :
    ((x : ZMod (2 ^ w)).val).testBit (w - 1) = decide (x < 0) ∧
      (0 ≤ x → (x : ZMod (2 ^ w)).val = x.toNat) := by
  have hv : (((x : ZMod (2 ^ w)).val : ℕ) : ℤ) = x % 2 ^ w := by
    rw [ZMod.val_intCast]; push_cast; rfl
  have hpow : (2 : ℤ) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow' : (2 : ℕ) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [abs_lt] at hx
  set v := (x : ZMod (2 ^ w)).val
  by_cases h0 : 0 ≤ x
  · have hm : x % 2 ^ w = x := Int.emod_eq_of_lt h0 (by rw [hpow]; linarith)
    have hvx : (v : ℤ) = x := by rw [hv, hm]
    have hvx' : v = x.toNat := by omega
    refine ⟨?_, fun _ => hvx'⟩
    have hlt : v < 2 ^ (w - 1) := by
      have : (v : ℤ) < 2 ^ (w - 1) := by rw [hvx]; exact hx.2
      exact_mod_cast this
    simp [Nat.testBit_lt_two_pow hlt, h0]
  · have hm : x % 2 ^ w = x + 2 ^ w := by
      rw [← Int.add_emod_right]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
    have hvx : (v : ℤ) = x + 2 ^ w := by rw [hv, hm]
    refine ⟨?_, fun h => absurd h h0⟩
    have hlo : 2 ^ (w - 1) ≤ v := by
      have : (2 : ℤ) ^ (w - 1) ≤ v := by rw [hvx]; linarith
      exact_mod_cast this
    have hhi : v < 2 ^ w := by
      have : (v : ℤ) < 2 ^ w := by rw [hvx]; linarith
      exact_mod_cast this
    have : v / 2 ^ (w - 1) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [Nat.testBit_eq_decide_div_mod_eq, this, not_le.1 h0]

/-- The masked magnitude: the residue for a nonnegative value, `0` for a negative one. -/
def rndMag (w v : ℕ) : ℕ := if v.testBit (w - 1) then 0 else v

private lemma rndMag_lt (w v : ℕ) (hv : v < 2 ^ w) : rndMag w v < 2 ^ w := by
  unfold rndMag; split_ifs <;> [positivity; exact hv]

/-- The integer computation of the stage gives the rounded coefficient: the masked residue of `x`
modulo `2^w`, times `S²`, shifted by `2b + 4` and rounded by `rndDiv`. -/
theorem rndCoeff_eq {w : ℕ} (hw : 1 ≤ w) (b S p : ℕ) {x : ℤ} (hx : |x| < 2 ^ (w - 1)) :
    rndDiv p (2 ^ (2 * b + 4) * (rndMag w (x : ZMod (2 ^ w)).val * (S * S))) =
      rndCoeff b S p x := by
  obtain ⟨hs, hpos⟩ := rnd_val_testBit hw hx
  unfold rndMag
  rw [hs]
  by_cases h0 : x < 0
  · simp only [h0, decide_true, ite_true, zero_mul, mul_zero]
    have hr : round ((2 ^ (2 * b) * S * 16 * S : ℝ) * ((x : ℝ) / 2 ^ p)) ≤ 0 := by
      have hy : (2 ^ (2 * b) * S * 16 * S : ℝ) * ((x : ℝ) / 2 ^ p) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
        apply div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h0.le) (by positivity)
      rw [round_eq, Int.floor_le_iff]
      push_cast
      linarith
    simp [rndCoeff, rndDiv, rndBit, Int.toNat_eq_zero.mpr hr]
  · simp only [h0, decide_false]
    rw [hpos (not_lt.1 h0)]
    simp only [Bool.false_eq_true, ite_false]
    have e : (2 ^ (2 * b) * S * 16 * S : ℝ) * ((x : ℝ) / 2 ^ p) =
        ((2 ^ (2 * b + 4) * (x.toNat * (S * S)) : ℕ) : ℝ) / 2 ^ p := by
      have hx' : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (not_lt.1 h0)
      push_cast
      rw [hx', pow_add]
      ring
    rw [rndCoeff, e, rndDiv_round]
    simp

/-- The coefficient of `pipelineCoeffs`: rounding the real part of `2^(2b) S · (16 S) • z` for a
grid value `z = N / 2^p`. -/
theorem rndCoeff_complex (b S p : ℕ) (N : GaussianInt) (z : ℂ)
    (hz : z = GaussianInt.toComplex N / 2 ^ p) :
    (round (((2 : ℂ) ^ (2 * b) * (S : ℂ)) * ((16 * (S : ℂ)) • z)).re).toNat =
      rndCoeff b S p N.re := by
  subst hz
  have e : ((2 : ℂ) ^ (2 * b) * (S : ℂ)) * ((16 * (S : ℂ)) • (GaussianInt.toComplex N / 2 ^ p)) =
      (((2 ^ (2 * b) * S * 16 * S : ℝ) / 2 ^ p : ℝ) : ℂ) * GaussianInt.toComplex N := by
    rw [smul_eq_mul]; push_cast; ring
  rw [e, Complex.re_ofReal_mul, ← GaussianInt.intCast_re, rndCoeff, div_mul_eq_mul_div,
    mul_div_assoc]

/-! ### Bit lists -/

section Bits

variable {A : ℕ}

private lemma replicate_binSyms (k L y : ℕ) :
    (List.replicate k (bitSymbol false) ++ binSyms L y : List (Fin (A + 4))) =
      binSyms (k + L) (2 ^ k * y) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, ih, show k + 1 + L = (k + L) + 1 by ring,
        binSyms_succ]
      congr 2
      · simp [pow_succ, Nat.testBit_zero, Nat.mul_assoc, Nat.mul_mod_right, Nat.mul_left_comm _ 2]
      · rw [pow_succ, show 2 ^ k * 2 * y = 2 * (2 ^ k * y) by ring,
          Nat.mul_div_cancel_left _ two_pos]

private lemma head_reverse_binSyms {K x : ℕ} (hK : 1 ≤ K) :
    ((binSyms K x : List (Fin (A + 4))).reverse).head?.getD blank =
      bitSymbol (x.testBit (K - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  rw [binSyms_succ_last]
  simp

private lemma map_pairRe_coeffSyms (hA : 4 ≤ A) (w : ℕ) (z : GR w) :
    (coeffSyms A w z).map (fun x => bitSymbol (pairRe x)) =
      (binSyms w z.1.val : List (Fin (A + 4))) := by
  simp [coeffSyms, binSyms, List.map_ofFn, Function.comp_def, pairRe_pairSym hA]

private lemma map_mask_binSyms (w v : ℕ) :
    (binSyms w v : List (Fin (A + 4))).map
        (fun x => (bitSymbol (symBit x && !v.testBit (w - 1)) : Fin (A + 4))) =
      binSyms w (rndMag w v) := by
  unfold rndMag
  cases h : v.testBit (w - 1)
  · simp [binSyms, List.map_ofFn, Function.comp_def]
  · simp [binSyms, List.map_ofFn, Function.comp_def]

private lemma shift_binSyms (b L M : ℕ) :
    (List.replicate 4 (bitSymbol false) ++ (binSyms b 0 ++ (binSyms b 0 ++ binSyms L M)) :
      List (Fin (A + 4))) = binSyms (2 * b + 4 + L) (2 ^ (2 * b + 4) * M) := by
  rw [binSyms_zero_right, ← List.append_assoc, ← List.append_assoc, List.replicate_append_replicate,
    List.replicate_append_replicate, replicate_binSyms]
  congr 2 <;> ring

private lemma div_pow_lt {X L p : ℕ} (hX : X < 2 ^ L) : X / 2 ^ p < 2 ^ (L - p) := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  exact lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega))

private lemma length_flatMap_binSyms (W : ℕ) :
    ∀ l : List ℕ, (l.flatMap (binSyms W) : List (Fin (A + 4))).length = l.length * W
  | [] => by simp
  | c :: l => by
      rw [List.flatMap_cons, List.length_append, length_binSyms, length_flatMap_binSyms W l,
        List.length_cons]
      ring

end Bits

/-! ### Steps -/

section Steps

variable {T Q A : ℕ} {U : Type}

/-- One step of a map pass: peek the parameter register `prm` into its scan slot, pop `src`,
push `G` of the parameter top and the popped symbol onto `dst`. -/
def rndMapAct (prm src dst : Fin T) (G : Fin (A + 4) → Fin (A + 4) → Fin (A + 4))
    (k : Act T Q A U) : Act T Q A U :=
  .peek (.rt prm) (fun v o => { v with scan := Function.update v.scan prm (o.getD blank) })
    (.pop (.rt src) (fun v o => { v with sym := o })
      (.push (.rt dst) (fun v => G (v.scan prm) (v.sym.getD blank)) k))

/-- The register effect of `rndMapAct`. -/
private def mapFx (prm src dst : Fin T) (G : Fin (A + 4) → Fin (A + 4) → Fin (A + 4))
    (R : Regs T A) : Regs T A :=
  Function.update (Function.update R src (R src).tail) dst
    (G ((R prm).head?.getD blank) ((R src).head?.getD blank) :: R dst)

private lemma regFx_map {prm src dst : Fin T} (hsd : src ≠ dst)
    (G : Fin (A + 4) → Fin (A + 4) → Fin (A + 4)) :
    RegFx (Q := Q) (U := U) (rndMapAct prm src dst G) (fun _ => mapFx prm src dst G) := by
  intro x k v S _
  refine ⟨{ v with
    scan := Function.update v.scan prm ((S.R prm).head?.getD blank)
    sym := (S.R src).head? }, rfl, ?_⟩
  simp [rndMapAct, Action.run, update_rt, mapFx, Function.update_of_ne hsd.symm]

private lemma frame_map {a prm src dst : Fin T} (hp : a ≠ prm) (hs : a ≠ src) (hd : a ≠ dst)
    (G : Fin (A + 4) → Fin (A + 4) → Fin (A + 4)) :
    Frame a (fun _ => mapFx (T := T) prm src dst G) := by
  intro x R l
  funext k
  simp only [mapFx, Function.update_apply]
  split_ifs <;> simp_all

private lemma mapFx_iter {prm src dst : Fin T} (hsd : src ≠ dst) (hps : prm ≠ src)
    (hpd : prm ≠ dst) (G : Fin (A + 4) → Fin (A + 4) → Fin (A + 4)) :
    ∀ (n : ℕ) (R : Regs T A), n ≤ (R src).length →
      (mapFx prm src dst G)^[n] R = Function.update (Function.update R src ((R src).drop n)) dst
        ((((R src).take n).map (G ((R prm).head?.getD blank))).reverse ++ R dst) := by
  intro n
  induction n with
  | zero => intro R _; simp
  | succ n ih =>
      intro R hn
      obtain ⟨y, l, hl⟩ : ∃ y l, R src = y :: l := by
        cases h : R src with
        | nil => rw [h] at hn; simp at hn
        | cons y l => exact ⟨y, l, rfl⟩
      rw [Function.iterate_succ_apply,
        ih _ (by simp [mapFx, Function.update_of_ne hsd, hl]; simp [hl] at hn; omega)]
      funext k
      simp only [mapFx, Function.update_apply, hl]
      split_ifs <;> simp_all

/-- One step of the drop pass: pop `xc` and replace the top of `cy` by the popped bit. -/
def rndDropAct (xc cy : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt xc) (fun v o => { v with sym := o })
    (.pop (.rt cy) (fun v _ => v)
      (.push (.rt cy) (fun v => bitSymbol (symBit (v.sym.getD blank))) k))

/-- The register effect of `rndDropAct`. -/
private def dropFx (xc cy : Fin T) (R : Regs T A) : Regs T A :=
  Function.update (Function.update R xc (R xc).tail) cy
    (bitSymbol (symBit ((R xc).head?.getD blank)) :: (R cy).tail)

private lemma regFx_drop {xc cy : Fin T} (hxc : xc ≠ cy) :
    RegFx (Q := Q) (A := A) (U := U) (rndDropAct xc cy) (fun _ => dropFx xc cy) := by
  intro x k v S _
  refine ⟨{ v with sym := (S.R xc).head? }, rfl, ?_⟩
  simp [rndDropAct, Action.run, update_rt, dropFx, Function.update_of_ne hxc.symm]

private lemma frame_drop {a xc cy : Fin T} (h1 : a ≠ xc) (h2 : a ≠ cy) :
    Frame a (fun _ => dropFx (T := T) (A := A) xc cy) := by
  intro x R l
  funext k
  simp only [dropFx, Function.update_apply]
  split_ifs <;> simp_all

private lemma dropFx_iter {xc cy : Fin T} (hxc : xc ≠ cy) :
    ∀ (n : ℕ) (R : Regs T A) (L X : ℕ), X < 2 ^ L → R xc = binSyms L X → (R cy).tail = [] →
      (dropFx xc cy)^[n] R = Function.update (Function.update R xc (binSyms (L - n) (X / 2 ^ n))) cy
        (if n = 0 then R cy else [bitSymbol (X.testBit (n - 1))]) := by
  intro n
  induction n with
  | zero =>
      intro R L X _ hx _
      simp [← hx]
  | succ n ih =>
      intro R L X hX hx hc
      have h1 : dropFx xc cy R xc = binSyms (L - 1) (X / 2) := by
        simp [dropFx, Function.update_of_ne hxc, hx, tail_binSyms]
      have h2 : dropFx xc cy R cy = [bitSymbol (X.testBit 0)] := by
        simp [dropFx, hx, symBit_head_binSyms hX, hc]
      rw [Function.iterate_succ_apply, ih _ (L - 1) (X / 2) (div_two_lt hX) h1 (by rw [h2]; rfl)]
      rw [h2]
      funext k
      simp only [dropFx, Function.update_apply]
      have e1 : L - 1 - n = L - (n + 1) := by omega
      have e2 : X / 2 / 2 ^ n = X / 2 ^ (n + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ']
      have e3 : ∀ n, n ≠ 0 → (X / 2).testBit (n - 1) = X.testBit n := by
        intro n hn
        rw [Nat.testBit_div_two]; congr 1; omega
      split_ifs <;> simp_all

/-- One step of the increment pass: pop a bit `x` of `xc` and the carry `c` on top of `cy`, push
`x xor c` onto `acc` and `x && c` onto `cy`. -/
def rndIncAct (xc cy acc : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt xc) (fun v o => { v with sym := o })
    (.pop (.rt cy) (fun v o => { v with scan := Function.update v.scan cy (o.getD blank) })
      (.push (.rt acc) (fun v => bitSymbol (xor (symBit (v.sym.getD blank)) (symBit (v.scan cy))))
        (.push (.rt cy) (fun v => bitSymbol (symBit (v.sym.getD blank) && symBit (v.scan cy))) k)))

/-- The register effect of `rndIncAct`. -/
private def incFx (xc cy acc : Fin T) (R : Regs T A) : Regs T A :=
  Function.update (Function.update (Function.update R xc (R xc).tail) acc
    (bitSymbol (xor (symBit ((R xc).head?.getD blank)) (symBit ((R cy).head?.getD blank))) ::
      R acc)) cy
    (bitSymbol (symBit ((R xc).head?.getD blank) && symBit ((R cy).head?.getD blank)) ::
      (R cy).tail)

private lemma regFx_inc {xc cy acc : Fin T} (h1 : xc ≠ cy) (h2 : xc ≠ acc) (h3 : cy ≠ acc) :
    RegFx (Q := Q) (A := A) (U := U) (rndIncAct xc cy acc) (fun _ => incFx xc cy acc) := by
  intro x k v S _
  refine ⟨{ v with
    sym := (S.R xc).head?
    scan := Function.update v.scan cy ((S.R cy).head?.getD blank) }, rfl, ?_⟩
  simp [rndIncAct, Action.run, update_rt, incFx, Function.update_of_ne h1.symm,
    Function.update_of_ne h2.symm, Function.update_of_ne h3.symm,
    Function.update_of_ne h3]
  rw [Function.update_comm h3, Function.update_idem]

private lemma frame_inc {a xc cy acc : Fin T} (h1 : a ≠ xc) (h2 : a ≠ cy) (h3 : a ≠ acc) :
    Frame a (fun _ => incFx (T := T) (A := A) xc cy acc) := by
  intro x R l
  funext k
  simp only [incFx, Function.update_apply]
  split_ifs <;> simp_all

private lemma incFx_iter {xc cy acc : Fin T} (h1 : xc ≠ cy) (h2 : xc ≠ acc) (h3 : cy ≠ acc) :
    ∀ (n : ℕ) (R : Regs T A) (L Y : ℕ), Y < 2 ^ L → R xc = binSyms L Y → (R cy).tail = [] →
      (incFx xc cy acc)^[n] R = Function.update (Function.update (Function.update R xc
        (binSyms (L - n) (Y / 2 ^ n))) acc
        (((incBits (symBit ((R cy).head?.getD blank)) (binBits n Y)).map bitSymbol).reverse ++
          R acc)) cy
        (if n = 0 then R cy else
          [bitSymbol (IntegerMultBounds.MathlibTM2.Host.carryOut (symBit ((R cy).head?.getD blank)) (binBits n Y))]) := by
  intro n
  induction n with
  | zero =>
      intro R L Y _ hx _
      simp [← hx, incBits]
  | succ n ih =>
      intro R L Y hY hx hc
      set c := symBit ((R cy).head?.getD blank) with hcdef
      have hx0 : symBit ((R xc).head?.getD blank) = Y.testBit 0 := by
        rw [hx]; exact symBit_head_binSyms hY
      have g1 : incFx xc cy acc R xc = binSyms (L - 1) (Y / 2) := by
        simp [incFx, Function.update_of_ne h1, Function.update_of_ne h2, hx, tail_binSyms]
      have g2 : incFx xc cy acc R cy = [bitSymbol (Y.testBit 0 && c)] := by
        simp [incFx, hx0, hc, hcdef]
      have g3 : incFx xc cy acc R acc = bitSymbol (xor (Y.testBit 0) c) :: R acc := by
        simp [incFx, Function.update_of_ne h3.symm, hx0, hcdef]
      rw [Function.iterate_succ_apply, ih _ (L - 1) (Y / 2) (div_two_lt hY) g1 (by rw [g2]; rfl)]
      rw [g2, g3]
      have e1 : L - 1 - n = L - (n + 1) := by omega
      have e2 : Y / 2 / 2 ^ n = Y / 2 ^ (n + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ']
      have e4 : binBits (n + 1) Y = Y.testBit 0 :: binBits n (Y / 2) := binBits_succ n Y
      have e5 : symBit ((([bitSymbol (Y.testBit 0 && c)] : List (Fin (A + 4))).head?).getD blank) =
          (Y.testBit 0 && c) := by simp
      rw [e5, e4]
      funext k
      simp only [incFx, Function.update_apply]
      split_ifs <;> simp_all [incBits, IntegerMultBounds.MathlibTM2.Host.carryOut]

end Steps

/-! ### Registers and contracts -/

/-- Registers of the rounding stage: the stream `src` and the output `dst`; `w`, `m`, `topN m`,
`b`, `p`, `W` in unary on `wn`, `mn`, `nn`, `bn`, `pn`, `wo`; `S²` in binary on `sq`; the scratch
registers `tm`, `u1`, `sg`, `xa`, `xc`, `cy`, `acc`; and the inputs of `rndSquare`: `S` in binary
on `sb`, `topN ℓ` and `m - (topN ℓ + 1)` in unary on `ns` and `pd`. -/
inductive RndReg
  | src | dst | wn | mn | nn | sq | bn | pn | wo | tm | u1 | sg | xa | xc | cy | acc | sb | ns | pd
  deriving DecidableEq

section Contracts

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) (rg : RndReg → Fin T)
  (ι : Fin 64 → Fin T)

/-- The stacks `S` carry the register file `ρ`. -/
private def RHolds (S : Stacks T A) (ρ : RndReg → List (Fin (A + 4))) : Prop :=
  ∀ r, S.R (rg r) = ρ r

/-- `S'` agrees with `S` on `inp`, `out`, the left stacks and every register outside `rg`. -/
private def RFr (S S' : Stacks T A) : Prop :=
  S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ∀ k, (∀ r, rg r ≠ k) → S'.R k = S.R k

/-- The multiplier's registers are empty. -/
private def RClean (S : Stacks T A) : Prop := ∀ j, S.L (ι j) = [] ∧ S.R (ι j) = []

/-- The contract of a program on the register file: from `ρ` to `ρ'` within `b` steps. -/
private def RRuns (p : Pr P T Q A U) (ρ ρ' : RndReg → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ v S, RClean ι S → RHolds rg S ρ → ∃ v' S' n, v'.user = v.user ∧ n ≤ b ∧
    Exec body p (mk v S) n (mk v' S') ∧ RHolds rg S' ρ' ∧ RFr rg S S'

variable {body rg ι}

private lemma rfr_refl (S : Stacks T A) : RFr rg S S := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

private lemma rfr_trans {S₁ S₂ S₃ : Stacks T A} (h₁ : RFr rg S₁ S₂) (h₂ : RFr rg S₂ S₃) :
    RFr rg S₁ S₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun k hk => (h₂.2.2.2 k hk).trans (h₁.2.2.2 k hk)⟩

private lemma rclean_of_fr (hdisj : ∀ r j, rg r ≠ ι j) {S S' : Stacks T A} (hc : RClean ι S)
    (h : RFr rg S S') : RClean ι S' := fun j =>
  ⟨by rw [h.2.2.1]; exact (hc j).1, by rw [h.2.2.2 _ (fun r => hdisj r j)]; exact (hc j).2⟩

private theorem rruns_seq (hdisj : ∀ r j, rg r ≠ ι j) {p q : Pr P T Q A U}
    {ρ₁ ρ₂ ρ₃ : RndReg → List (Fin (A + 4))} {b₁ b₂ : ℕ} (h₁ : RRuns body rg ι p ρ₁ ρ₂ b₁)
    (h₂ : RRuns body rg ι q ρ₂ ρ₃ b₂) : RRuns body rg ι (.seq p q) ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hc hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hc hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := h₂ v₁ S₁ (rclean_of_fr hdisj hc hf₁) hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, rfr_trans hf₁ hf₂⟩

private theorem rruns_mono {p : Pr P T Q A U} {ρ ρ' : RndReg → List (Fin (A + 4))} {b b' : ℕ}
    (h : RRuns body rg ι p ρ ρ' b) (hb : b ≤ b') : RRuns body rg ι p ρ ρ' b' := by
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S hc hS
  exact ⟨v', S', n, hu, hn.trans hb, he, hS', hf⟩

private theorem rruns_congr {p : Pr P T Q A U} {ρ ρ' ρ'' : RndReg → List (Fin (A + 4))} {b : ℕ}
    (h : RRuns body rg ι p ρ ρ' b) (he : ρ' = ρ'') : RRuns body rg ι p ρ ρ'' b := he ▸ h

/-! #### Register files under updates -/

private lemma upd_comp (hcr : Function.Injective rg) {β : Type} (g : Fin T → β) (a : RndReg)
    (x : β) (r : RndReg) :
    Function.update g (rg a) x (rg r) = Function.update (fun r => g (rg r)) a x r := by
  by_cases h : r = a
  · subst h; simp
  · rw [Function.update_of_ne (hcr.ne h), Function.update_of_ne h]

private lemma holds_upd (hcr : Function.Injective rg) {R : Fin T → List (Fin (A + 4))}
    {ρ : RndReg → List (Fin (A + 4))} (h : ∀ r, R (rg r) = ρ r) (a : RndReg)
    (x : List (Fin (A + 4))) :
    ∀ r, Function.update R (rg a) x (rg r) = Function.update ρ a x r := by
  intro r
  rw [upd_comp hcr]
  have : (fun r => R (rg r)) = ρ := funext h
  rw [this]

private lemma upd_off {β : Type} (g : Fin T → β) (a : RndReg) (x : β) {k : Fin T}
    (hk : ∀ r, rg r ≠ k) : Function.update g (rg a) x k = g k :=
  Function.update_of_ne (hk a).symm _ _

/-! #### Primitive contracts -/

private lemma foldl_const_iter {α β : Type} (Φ : β → β) :
    ∀ (l : List α) (R : β), l.foldl (fun R _ => Φ R) R = Φ^[l.length] R
  | [], _ => rfl
  | x :: l, R => by
      rw [List.foldl_cons, foldl_const_iter Φ l, List.length_cons, Function.iterate_succ_apply]

variable (hcr : Function.Injective rg)
include hcr

private theorem moveR_runs {a b : RndReg} (hab : a ≠ b) {ρ : RndReg → List (Fin (A + 4))} {n : ℕ}
    (hn : (ρ a).length = n) :
    RRuns body rg ι (moveR (rg a) (rg b) id) ρ
      (Function.update (Function.update ρ a []) b ((ρ a).reverse ++ ρ b)) (2 * n + 2) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := moveR_exec body (rg a) (rg b) (hcr.ne hab) id v S
  refine ⟨v', _, _, hu, by rw [hS, hn], he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · intro r
    simp only [movedR, List.map_id]
    rw [holds_upd hcr (holds_upd hcr hS a []) b, hS, hS]
  · simp only [movedR, upd_off _ _ _ hk]

private theorem uclear_runs (a : RndReg) {ρ : RndReg → List (Fin (A + 4))} {n : ℕ}
    (hn : (ρ a).length ≤ n) :
    RRuns body rg ι (uclear (rg a)) ρ (Function.update ρ a []) (2 * n + 2) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := uclear_exec body (rg a) v S
  exact ⟨v', _, _, hu, by rw [hS]; omega, he, holds_upd hcr hS a [],
    ⟨rfl, rfl, rfl, fun k hk => upd_off _ _ _ hk⟩⟩

private theorem usub_runs {a b t : RndReg} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {ρ : RndReg → List (Fin (A + 4))} {n : ℕ} (hn : (ρ a).length = n) (ht : ρ t = []) :
    RRuns body rg ι (usub (rg a) (rg b) (rg t)) ρ (Function.update ρ b ((ρ b).drop n))
      (4 * n + 4) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := usub_exec body (hcr.ne hab) (hcr.ne hat) (hcr.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS, hn], he, ?_, ⟨rfl, rfl, rfl, fun k hk => upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [holds_upd hcr hS b, hS, hS, hn]

private theorem zeroBits_runs {len z t : RndReg} (hlz : len ≠ z) (hlt : len ≠ t) (hzt : z ≠ t)
    {ρ : RndReg → List (Fin (A + 4))} {n : ℕ} (hn : (ρ len).length = n) (ht : ρ t = []) :
    RRuns body rg ι (zeroBits (rg len) (rg z) (rg t)) ρ
      (Function.update ρ z (binSyms n 0 ++ ρ z)) (4 * n + 4) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := zeroBits_exec body (hcr.ne hlz) (hcr.ne hlt) (hcr.ne hzt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS, hn], he, ?_, ⟨rfl, rfl, rfl, fun k hk => upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [holds_upd hcr hS z, hS, hS, hn]

private theorem ssMul_runs (hdisj : ∀ r j, rg r ≠ ι j) (hι : Function.Injective ι) (hT : 64 ≤ T)
    (hQ : SS.states ≤ Q) {ra rb rn rc : RndReg} (hna : rn ≠ ra) (hnb : rn ≠ rb) {m a b : ℕ}
    (hm : 1 ≤ m) (ha : a < 2 ^ m) (hb : b < 2 ^ m) {ρ : RndReg → List (Fin (A + 4))}
    (hSa : ρ ra = binSyms m a) (hSb : ρ rb = binSyms m b)
    (hSn : (ρ rn).length = topN m) :
    RRuns body rg ι (ssMul ι hι hT hQ (rg ra) (rg rb) (rg rn) (rg rc)) ρ
      (Function.update ρ rc
        (binSyms (topN m + 1) (a * b) ++ ρ rc))
      ((T + 773) * ssCostBound m + 164 * m + 463) := by
  intro v S hc hS
  obtain ⟨v', n, hu, hn, he⟩ := ssMul_exec body ι hι hT hQ (fun j => (hdisj ra j).symm)
    (fun j => (hdisj rb j).symm) (fun j => (hdisj rn j).symm) (fun j => (hdisj rc j).symm)
    (hcr.ne hna) (hcr.ne hnb) hm ha hb v S (fun j => (hc j).1) (fun j => (hc j).2)
    (by rw [hS, hSa]) (by rw [hS, hSb]) (by rw [hS, hSn])
  refine ⟨v', _, n, hu, hn, he, ?_, ⟨rfl, rfl, rfl, fun k hk => upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [holds_upd hcr hS rc, hS]

/-- A single action that pushes onto one register. -/
private theorem act_runs (a : Act T Q A U) (r : RndReg) {ρ : RndReg → List (Fin (A + 4))}
    (x : List (Fin (A + 4)))
    (ha : ∀ (v : HS T Q A U) (S : Stacks T A), RHolds rg S ρ → ∃ v' : HS T Q A U,
      v'.user = v.user ∧ a.run (mk v S) = mk v' { S with R := Function.update S.R (rg r) x }) :
    RRuns body rg ι (.act a) ρ (Function.update ρ r x) 1 := by
  intro v S _ hS
  obtain ⟨v', hu, hrun⟩ := ha v S hS
  refine ⟨v', { S with R := Function.update S.R (rg r) x }, 1, hu, le_rfl, ?_,
    holds_upd hcr hS r x, ⟨rfl, rfl, rfl, fun k hk => upd_off _ _ _ hk⟩⟩
  rw [← hrun]
  exact Exec.act a (mk v S)

/-- A counted pass: `scanR` over a counter of `n` symbols whose step acts on the registers by `Φ`,
specified by its `n`-th iterate. -/
private theorem scan_runs {a t : RndReg} (hat : a ≠ t) {f : Act T Q A U → Act T Q A U}
    {Φ : Regs T A → Regs T A} (hf : RegFx f (fun _ => Φ)) (ha : Frame (rg a) (fun _ => Φ))
    (ht : Frame (rg t) (fun _ => Φ)) {ρ ρ' : RndReg → List (Fin (A + 4))} {n : ℕ}
    (hn : (ρ a).length = n) (htm : ρ t = [])
    (hΦ : ∀ R : Regs T A, (∀ r, R (rg r) = ρ r) →
      (∀ r, Φ^[n] R (rg r) = ρ' r) ∧ ∀ k, (∀ r, rg r ≠ k) → Φ^[n] R k = R k) :
    RRuns body rg ι (scanR (rg a) (rg t) f) ρ ρ' (4 * n + 4) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := scanR_exec' body (hcr.ne hat) hf ha ht v S (by rw [hS, htm])
  rw [foldl_const_iter, hS, hn] at he
  obtain ⟨h1, h2⟩ := hΦ S.R hS
  exact ⟨v', _, _, hu, le_rfl, he, h1, ⟨rfl, rfl, rfl, h2⟩⟩

private lemma phi2 {R : Regs T A} {ρ : RndReg → List (Fin (A + 4))} (hR : ∀ r, R (rg r) = ρ r)
    (a b : RndReg) (x y : List (Fin (A + 4))) :
    (∀ r, Function.update (Function.update R (rg a) x) (rg b) y (rg r) =
      Function.update (Function.update ρ a x) b y r) ∧
    ∀ k, (∀ r, rg r ≠ k) → Function.update (Function.update R (rg a) x) (rg b) y k = R k :=
  ⟨holds_upd hcr (holds_upd hcr hR a x) b y, fun k hk => by rw [upd_off _ _ _ hk, upd_off _ _ _ hk]⟩

private lemma phi3 {R : Regs T A} {ρ : RndReg → List (Fin (A + 4))} (hR : ∀ r, R (rg r) = ρ r)
    (a b c : RndReg) (x y z : List (Fin (A + 4))) :
    (∀ r, Function.update (Function.update (Function.update R (rg a) x) (rg b) y) (rg c) z (rg r) =
      Function.update (Function.update (Function.update ρ a x) b y) c z r) ∧
    ∀ k, (∀ r, rg r ≠ k) →
      Function.update (Function.update (Function.update R (rg a) x) (rg b) y) (rg c) z k = R k :=
  ⟨holds_upd hcr (holds_upd hcr (holds_upd hcr hR a x) b y) c z,
    fun k hk => by rw [upd_off _ _ _ hk, upd_off _ _ _ hk, upd_off _ _ _ hk]⟩

/-- The split pass: the real bits of the coefficient on top of `src` go onto `u1`, most
significant on top. -/
private theorem split_runs (hA : 4 ≤ A) {ρ : RndReg → List (Fin (A + 4))} {w : ℕ} (z : GR w)
    (rest : List (Fin (A + 4))) (hsrc : ρ .src = coeffSyms A w z ++ rest)
    (hwn : (ρ .wn).length = w) (htm : ρ .tm = []) :
    RRuns body rg ι (scanR (rg .wn) (rg .tm)
        (rndMapAct (rg .sg) (rg .src) (rg .u1) (fun _ x => bitSymbol (pairRe x)))) ρ
      (Function.update (Function.update ρ .src rest) .u1 ((binSyms w z.1.val).reverse ++ ρ .u1))
      (4 * w + 4) := by
  refine scan_runs hcr (by decide) (regFx_map (hcr.ne (by decide)) _)
    (frame_map (hcr.ne (by decide)) (hcr.ne (by decide)) (hcr.ne (by decide)) _)
    (frame_map (hcr.ne (by decide)) (hcr.ne (by decide)) (hcr.ne (by decide)) _) hwn htm ?_
  intro R hR
  have hl : R (rg .src) = coeffSyms A w z ++ rest := by rw [hR, hsrc]
  rw [mapFx_iter (hcr.ne (by decide)) (hcr.ne (by decide)) (hcr.ne (by decide)) _ w R
    (by rw [hl]; simp), hl, List.take_left' (by simp), List.drop_left' (by simp),
    map_pairRe_coeffSyms hA, hR]
  exact phi2 hcr hR _ _ _ _

/-- The mask pass: the residue on `u1` (most significant bit on top) moves onto `xa`, least
significant bit on top, zeroed when the sign bit on `sg` is set. -/
private theorem mask_runs {ρ : RndReg → List (Fin (A + 4))} {w v : ℕ}
    (hu1 : ρ .u1 = (binSyms w v).reverse) (hsg : ρ .sg = [bitSymbol (v.testBit (w - 1))])
    (hwn : (ρ .wn).length = w) (htm : ρ .tm = []) :
    RRuns body rg ι (scanR (rg .wn) (rg .tm)
        (rndMapAct (rg .sg) (rg .u1) (rg .xa) (fun s x => bitSymbol (symBit x && !symBit s)))) ρ
      (Function.update (Function.update ρ .u1 []) .xa (binSyms w (rndMag w v) ++ ρ .xa))
      (4 * w + 4) := by
  refine scan_runs hcr (by decide) (regFx_map (hcr.ne (by decide)) _)
    (frame_map (hcr.ne (by decide)) (hcr.ne (by decide)) (hcr.ne (by decide)) _)
    (frame_map (hcr.ne (by decide)) (hcr.ne (by decide)) (hcr.ne (by decide)) _) hwn htm ?_
  intro R hR
  have hl : R (rg .u1) = (binSyms w v).reverse := by rw [hR, hu1]
  rw [mapFx_iter (hcr.ne (by decide)) (hcr.ne (by decide)) (hcr.ne (by decide)) _ w R
    (by rw [hl]; simp), hl, List.take_of_length_le (by simp), List.drop_of_length_le (by simp),
    hR .sg, hsg, hR .xa]
  simp only [List.head?_cons, Option.getD_some, symBit_bitSymbol, List.map_reverse,
    List.reverse_reverse]
  rw [map_mask_binSyms]
  exact phi2 hcr hR _ _ _ _

/-- The drop pass: `p` bits of `xc` are dropped, the last one kept on `cy`. -/
private theorem drop_runs {ρ : RndReg → List (Fin (A + 4))} {L X p : ℕ} (hX : X < 2 ^ L)
    (hxc : ρ .xc = binSyms L X) (hcy : ρ .cy = []) (hpn : (ρ .pn).length = p)
    (htm : ρ .tm = []) :
    RRuns body rg ι (scanR (rg .pn) (rg .tm) (rndDropAct (rg .xc) (rg .cy))) ρ
      (Function.update (Function.update ρ .xc (binSyms (L - p) (X / 2 ^ p))) .cy
        (if p = 0 then [] else [bitSymbol (X.testBit (p - 1))]))
      (4 * p + 4) := by
  refine scan_runs hcr (by decide) (regFx_drop (hcr.ne (by decide)))
    (frame_drop (hcr.ne (by decide)) (hcr.ne (by decide)))
    (frame_drop (hcr.ne (by decide)) (hcr.ne (by decide))) hpn htm ?_
  intro R hR
  rw [dropFx_iter (hcr.ne (by decide)) p R L X hX (by rw [hR, hxc]) (by rw [hR, hcy]; rfl),
    hR, hcy]
  have : (if p = 0 then ([] : List (Fin (A + 4))) else [bitSymbol (X.testBit (p - 1))]) =
      (if p = 0 then [] else [bitSymbol (X.testBit (p - 1))]) := rfl
  exact phi2 hcr hR _ _ _ _

/-- The increment pass: `W` bits of `xc` plus the carry on top of `cy` go onto `acc`, most
significant bit on top. -/
private theorem inc_runs {ρ : RndReg → List (Fin (A + 4))} {L Y W : ℕ} (hY : Y < 2 ^ L)
    (hxc : ρ .xc = binSyms L Y) (hcy : (ρ .cy).tail = []) (hwo : (ρ .wo).length = W)
    (htm : ρ .tm = []) :
    RRuns body rg ι (scanR (rg .wo) (rg .tm) (rndIncAct (rg .xc) (rg .cy) (rg .acc))) ρ
      (Function.update (Function.update (Function.update ρ .xc (binSyms (L - W) (Y / 2 ^ W))) .acc
        ((binSyms W (Y + (symBit ((ρ .cy).head?.getD blank)).toNat)).reverse ++ ρ .acc)) .cy
        (if W = 0 then ρ .cy else
          [bitSymbol (IntegerMultBounds.MathlibTM2.Host.carryOut (symBit ((ρ .cy).head?.getD blank)) (binBits W Y))]))
      (4 * W + 4) := by
  refine scan_runs hcr (by decide) (regFx_inc (hcr.ne (by decide)) (hcr.ne (by decide))
      (hcr.ne (by decide)))
    (frame_inc (hcr.ne (by decide)) (hcr.ne (by decide)) (hcr.ne (by decide)))
    (frame_inc (hcr.ne (by decide)) (hcr.ne (by decide)) (hcr.ne (by decide))) hwo htm ?_
  intro R hR
  rw [incFx_iter (hcr.ne (by decide)) (hcr.ne (by decide)) (hcr.ne (by decide)) W R L Y hY
    (by rw [hR, hxc]) (by rw [hR]; exact hcy), hR, hR, incBits_binBits, ← binSyms_eq]
  exact phi3 hcr hR _ _ _ _ _ _

end Contracts

/-! ### The program -/

section Prog

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- Push the top bit of `u1` onto `sg`. -/
def rndSignAct (u1 sg : Fin T) : Act T Q A U :=
  .peek (.rt u1) (fun v o => { v with sym := o })
    (.push (.rt sg) (fun v => bitSymbol (symBit (v.sym.getD blank))) .done)

/-- Phase A of a coefficient: the real bits onto `u1` (`w` steps counted by `wn`), the sign bit
onto `sg`, `m - w` zero bits onto `xa`, the masked residue onto `xa`, `sg` cleared. -/
def rndPhaseA (rg : RndReg → Fin T) : Pr P T Q A U :=
  .seq (scanR (rg .wn) (rg .tm)
    (rndMapAct (rg .sg) (rg .src) (rg .u1) (fun _ x => bitSymbol (pairRe x))))
  (.seq (.act (rndSignAct (rg .u1) (rg .sg)))
  (.seq (zeroBits (rg .mn) (rg .xa) (rg .tm))
  (.seq (usub (rg .wn) (rg .xa) (rg .tm))
  (.seq (scanR (rg .wn) (rg .tm)
    (rndMapAct (rg .sg) (rg .u1) (rg .xa) (fun s x => bitSymbol (symBit x && !symBit s))))
    (uclear (rg .sg))))))

/-- Phase B of a coefficient: the product of `xa` and `sq` onto `xc` (`ssMul`), `xa` cleared,
`2 b + 4` zero bits pushed onto `xc` (the shift by `2 b + 4`). -/
noncomputable def rndPhaseB (rg : RndReg → Fin T) (ι : Fin 64 → Fin T) (hι : Function.Injective ι)
    (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (ssMul ι hι hT hQ (rg .xa) (rg .sq) (rg .nn) (rg .xc))
  (.seq (uclear (rg .xa))
  (.seq (zeroBits (rg .bn) (rg .xc) (rg .tm))
  (.seq (zeroBits (rg .bn) (rg .xc) (rg .tm))
    (.act (pushN (rg .xc) (fun _ => bitSymbol false) 4 .done)))))

/-- Phase C of a coefficient: `p` bits of `xc` dropped (the last kept on `cy`), `W` bits of the
quotient plus the kept bit onto `acc`, `cy` and `xc` cleared. -/
def rndPhaseC (rg : RndReg → Fin T) : Pr P T Q A U :=
  .seq (scanR (rg .pn) (rg .tm) (rndDropAct (rg .xc) (rg .cy)))
  (.seq (scanR (rg .wo) (rg .tm) (rndIncAct (rg .xc) (rg .cy) (rg .acc)))
  (.seq (uclear (rg .cy)) (uclear (rg .xc))))

/-- One coefficient: phases A, B and C. -/
noncomputable def rndCoeffProg (rg : RndReg → Fin T) (ι : Fin 64 → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (rndPhaseA rg) (.seq (rndPhaseB rg ι hι hT hQ) (rndPhaseC rg))

/-- Repeat `p` while register `g` is nonempty. -/
def rndWhile (g : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR g)) (.loop (·.flag) (.seq p (.act (peekR g))))

/-- The rounding stage: one coefficient per iteration while `src` is nonempty, then the words
move from `acc` onto `dst`. -/
noncomputable def roundStage (rg : RndReg → Fin T) (ι : Fin 64 → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (rndWhile (rg .src) (rndCoeffProg rg ι hι hT hQ)) (moveR (rg .acc) (rg .dst) id)

/-- The step bound of one coefficient. -/
def rndCoeffCost (T m w b p W : ℕ) : ℕ :=
  ((T + 773) * ssCostBound m + 164 * m + 463) + 12 * w + 14 * m + 12 * b + 4 * p + 4 * W + 56

/-- The step bound of the rounding stage on `S` coefficients. -/
def roundStageCost (T m w b p W S : ℕ) : ℕ :=
  S * (((T + 773) * ssCostBound m + 164 * m + 463) + 12 * w + 14 * m + 12 * b + 4 * p + 6 * W +
    58) + 4

end Prog

section Phases

private lemma signAct_run {T Q A : ℕ} {U : Type} (u1 sg : Fin T) (v : HS T Q A U)
    (S : Stacks T A) :
    (rndSignAct u1 sg : Act T Q A U).run (mk v S) = mk { v with sym := (S.R u1).head? }
      { S with R := (Function.update S.R sg
        (bitSymbol (symBit ((S.R u1).head?.getD blank)) :: S.R sg)) } := by
  simp [rndSignAct, Action.run, update_rt]

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RndReg → Fin T}
  {ι : Fin 64 → Fin T} (hcr : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hcr hdisj

private theorem phaseA_runs (hA : 4 ≤ A) {ρ : RndReg → List (Fin (A + 4))} {w m : ℕ} (hw : 1 ≤ w)
    (hwm : w ≤ m) (z : GR w) (rest : List (Fin (A + 4)))
    (hsrc : ρ .src = coeffSyms A w z ++ rest) (hwn : (ρ .wn).length = w)
    (hmn : (ρ .mn).length = m) (htm : ρ .tm = []) (hu1 : ρ .u1 = []) (hsg : ρ .sg = [])
    (hxa : ρ .xa = []) :
    RRuns body rg ι (rndPhaseA rg) ρ
      (Function.update (Function.update ρ .src rest) .xa (binSyms m (rndMag w z.1.val)))
      (12 * w + 4 * m + 21) := by
  set v := z.1.val with hv
  have hv2 : v < 2 ^ w := by rw [hv]; exact ZMod.val_lt _
  set ρ₁ := Function.update (Function.update ρ .src rest) .u1 (binSyms w v).reverse with hρ₁
  have s1 : RRuns body rg ι _ ρ ρ₁ (4 * w + 4) :=
    rruns_congr (split_runs hcr hA z rest hsrc hwn htm) (by rw [hu1, List.append_nil])
  set ρ₂ := Function.update ρ₁ .sg [bitSymbol (v.testBit (w - 1))] with hρ₂
  have s2 : RRuns body rg ι (.act (rndSignAct (rg .u1) (rg .sg))) ρ₁ ρ₂ 1 := by
    have hu1' : ρ₁ .u1 = (binSyms w v).reverse := by simp [ρ₁]
    have hsg' : ρ₁ .sg = [] := by simp [ρ₁, hsg]
    refine act_runs hcr _ .sg _ (fun v' S hS =>
      ⟨{ v' with sym := (S.R (rg .u1)).head? }, rfl, ?_⟩)
    rw [signAct_run, hS .u1, hS .sg, hu1', hsg', head_reverse_binSyms hw, symBit_bitSymbol]
  set ρ₃ := Function.update ρ₂ .xa (binSyms m 0) with hρ₃
  have s3 : RRuns body rg ι (zeroBits (rg .mn) (rg .xa) (rg .tm)) ρ₂ ρ₃ (4 * m + 4) :=
    rruns_congr (zeroBits_runs hcr (by decide) (by decide) (by decide)
      (by simp [ρ₂, ρ₁, hmn]) (by simp [ρ₂, ρ₁, htm])) (by simp [ρ₃, ρ₂, ρ₁, hxa])
  set ρ₄ := Function.update ρ₂ .xa (List.replicate (m - w) (bitSymbol false)) with hρ₄
  have s4 : RRuns body rg ι (usub (rg .wn) (rg .xa) (rg .tm)) ρ₃ ρ₄ (4 * w + 4) :=
    rruns_congr (usub_runs hcr (by decide) (by decide) (by decide)
      (by simp [ρ₃, ρ₂, ρ₁, hwn]) (by simp [ρ₃, ρ₂, ρ₁, htm]))
      (by simp [ρ₄, ρ₃, binSyms_zero_right, List.drop_replicate])
  set ρ₅ := Function.update (Function.update ρ₂ .u1 []) .xa (binSyms m (rndMag w v)) with hρ₅
  have s5 : RRuns body rg ι (scanR (rg .wn) (rg .tm) (rndMapAct (rg .sg) (rg .u1) (rg .xa)
      (fun s x => bitSymbol (symBit x && !symBit s)))) ρ₄ ρ₅ (4 * w + 4) := by
    refine rruns_congr (mask_runs hcr (w := w) (v := v) (by simp [ρ₄, ρ₂, ρ₁])
      (by simp [ρ₄, ρ₂]) (by simp [ρ₄, ρ₂, ρ₁, hwn]) (by simp [ρ₄, ρ₂, ρ₁, htm])) ?_
    rw [show (ρ₄ .xa) = List.replicate (m - w) (bitSymbol false) by simp [ρ₄],
      SS.binSyms_append_replicate (rndMag_lt w v hv2) hwm]
    funext r
    simp only [ρ₅, ρ₄, Function.update_apply]
    split_ifs <;> simp_all
  have s6 : RRuns body rg ι (uclear (rg .sg)) ρ₅ (Function.update ρ₅ .sg []) (2 * 1 + 2) :=
    uclear_runs hcr .sg (by simp [ρ₅, ρ₂])
  refine rruns_mono (rruns_congr (rruns_seq hdisj s1 (rruns_seq hdisj s2 (rruns_seq hdisj s3
    (rruns_seq hdisj s4 (rruns_seq hdisj s5 s6))))) ?_) (by omega)
  funext r
  simp only [ρ₅, ρ₂, ρ₁, Function.update_apply]
  split_ifs <;> simp_all

private theorem phaseB_runs (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    {ρ : RndReg → List (Fin (A + 4))} {m a S b : ℕ} (hm : 1 ≤ m) (ha : a < 2 ^ m)
    (hS : S * S < 2 ^ m) (hxa : ρ .xa = binSyms m a) (hsq : ρ .sq = binSyms m (S * S))
    (hnn : (ρ .nn).length = topN m)
    (hbn : (ρ .bn).length = b) (htm : ρ .tm = []) (hxc : ρ .xc = []) :
    RRuns body rg ι (rndPhaseB rg ι hι hT hQ) ρ
      (Function.update (Function.update ρ .xa []) .xc
        (binSyms (2 * b + 4 + (topN m + 1))
          (2 ^ (2 * b + 4) * (a * (S * S)))))
      ((T + 773) * ssCostBound m + 164 * m + 463 + (2 * m + 2) + (4 * b + 4) + (4 * b + 4) +
        1) := by
  set N := topN m with hN
  set ρ₁ := Function.update ρ .xc (binSyms (N + 1) (a * (S * S))) with hρ₁
  have t1 : RRuns body rg ι (ssMul ι hι hT hQ (rg .xa) (rg .sq) (rg .nn) (rg .xc)) ρ ρ₁
      ((T + 773) * ssCostBound m + 164 * m + 463) :=
    rruns_congr (ssMul_runs hcr hdisj hι hT hQ (rc := .xc) (by decide) (by decide) hm ha hS hxa
      hsq hnn) (by rw [hxc, List.append_nil])
  set ρ₂ := Function.update ρ₁ .xa [] with hρ₂
  have t2 : RRuns body rg ι (uclear (rg .xa)) ρ₁ ρ₂ (2 * m + 2) :=
    uclear_runs hcr .xa (by simp [ρ₁, hxa])
  set ρ₃ := Function.update ρ₂ .xc (binSyms b 0 ++ ρ₂ .xc) with hρ₃
  have t3 : RRuns body rg ι (zeroBits (rg .bn) (rg .xc) (rg .tm)) ρ₂ ρ₃ (4 * b + 4) :=
    zeroBits_runs hcr (by decide) (by decide) (by decide) (by simp [ρ₂, ρ₁, hbn])
      (by simp [ρ₂, ρ₁, htm])
  set ρ₄ := Function.update ρ₃ .xc (binSyms b 0 ++ ρ₃ .xc) with hρ₄
  have t4 : RRuns body rg ι (zeroBits (rg .bn) (rg .xc) (rg .tm)) ρ₃ ρ₄ (4 * b + 4) :=
    zeroBits_runs hcr (by decide) (by decide) (by decide) (by simp [ρ₃, ρ₂, ρ₁, hbn])
      (by simp [ρ₃, ρ₂, ρ₁, htm])
  set ρ₅ := Function.update ρ₄ .xc (List.replicate 4 (bitSymbol false) ++ ρ₄ .xc) with hρ₅
  have t5 : RRuns body rg ι (.act (pushN (rg .xc) (fun _ => bitSymbol false) 4 .done)) ρ₄ ρ₅ 1 := by
    refine act_runs hcr _ .xc _ (fun v' S' hS' => ⟨v', rfl, ?_⟩)
    rw [pushN_run, run_done, hS' .xc]
  refine rruns_mono (rruns_congr (rruns_seq hdisj t1 (rruns_seq hdisj t2 (rruns_seq hdisj t3
    (rruns_seq hdisj t4 t5)))) ?_) (by omega)
  have hx : ρ₅ .xc = binSyms (2 * b + 4 + (N + 1)) (2 ^ (2 * b + 4) * (a * (S * S))) := by
    simp only [ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, Function.update_self]
    rw [Function.update_of_ne (by decide), Function.update_self, shift_binSyms]
  funext r
  by_cases h : r = .xc
  · subst h; rw [hx]; simp
  · rw [Function.update_of_ne h]
    simp only [ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, Function.update_of_ne h, Function.update_apply]

private theorem phaseC_runs {ρ : RndReg → List (Fin (A + 4))} {L X p W : ℕ} (hX : X < 2 ^ L)
    (hxc : ρ .xc = binSyms L X) (hcy : ρ .cy = []) (hpn : (ρ .pn).length = p)
    (hwo : (ρ .wo).length = W) (htm : ρ .tm = []) :
    RRuns body rg ι (rndPhaseC rg) ρ
      (Function.update (Function.update ρ .xc []) .acc ((binSyms W (rndDiv p X)).reverse ++ ρ .acc))
      ((4 * p + 4) + (4 * W + 4) + (2 * 1 + 2) + (2 * (L - p - W) + 2)) := by
  set rb : List (Fin (A + 4)) := if p = 0 then [] else [bitSymbol (X.testBit (p - 1))] with hrb
  have hrb1 : rb.tail = [] := by rw [hrb]; split_ifs <;> rfl
  have hrb2 : symBit (rb.head?.getD blank) = rndBit p X := by
    rw [hrb, rndBit]
    split_ifs with h
    · simp [h, symBit_blank]
    · simp [h]
  have hrb3 : rb.length ≤ 1 := by rw [hrb]; split_ifs <;> simp
  set ρ₁ := Function.update (Function.update ρ .xc (binSyms (L - p) (X / 2 ^ p))) .cy rb with hρ₁
  have c1 : RRuns body rg ι (scanR (rg .pn) (rg .tm) (rndDropAct (rg .xc) (rg .cy))) ρ ρ₁
      (4 * p + 4) := drop_runs hcr hX hxc hcy hpn htm
  set cy₂ : List (Fin (A + 4)) := if W = 0 then rb else
    [bitSymbol (IntegerMultBounds.MathlibTM2.Host.carryOut (rndBit p X) (binBits W (X / 2 ^ p)))] with hcy₂
  have hcy₂1 : cy₂.length ≤ 1 := by rw [hcy₂]; split_ifs <;> simp [hrb3]
  set ρ₂ := Function.update (Function.update (Function.update ρ₁ .xc
    (binSyms (L - p - W) (X / 2 ^ p / 2 ^ W))) .acc
    ((binSyms W (rndDiv p X)).reverse ++ ρ .acc)) .cy cy₂ with hρ₂
  have c2 : RRuns body rg ι (scanR (rg .wo) (rg .tm) (rndIncAct (rg .xc) (rg .cy) (rg .acc))) ρ₁ ρ₂
      (4 * W + 4) := by
    have h1 : ρ₁ .cy = rb := by simp [ρ₁]
    refine rruns_congr (inc_runs hcr (div_pow_lt (p := p) hX) (by simp [ρ₁])
      (by rw [h1]; exact hrb1)
      (by simp [ρ₁, hwo]) (by simp [ρ₁, htm])) ?_
    rw [h1, hrb2]
    simp [ρ₂, ρ₁, cy₂, rndDiv]
  have c3 : RRuns body rg ι (uclear (rg .cy)) ρ₂ (Function.update ρ₂ .cy []) (2 * 1 + 2) :=
    uclear_runs hcr .cy (by simp [ρ₂, hcy₂1])
  have c4 : RRuns body rg ι (uclear (rg .xc)) (Function.update ρ₂ .cy [])
      (Function.update (Function.update ρ₂ .cy []) .xc []) (2 * (L - p - W) + 2) :=
    uclear_runs hcr .xc (by simp [ρ₂, ρ₁])
  refine rruns_mono (rruns_congr (rruns_seq hdisj c1 (rruns_seq hdisj c2 (rruns_seq hdisj c3 c4)))
    ?_) (by omega)
  funext r
  simp only [ρ₂, ρ₁, Function.update_apply]
  split_ifs <;> simp_all

private theorem coeff_runs (hA : 4 ≤ A) (hι : Function.Injective ι) (hT : 64 ≤ T)
    (hQ : SS.states ≤ Q) {ρ : RndReg → List (Fin (A + 4))} {w m b p W S : ℕ} (hw : 1 ≤ w)
    (hwm : w ≤ m) (hSm : S * S < 2 ^ m) (N : GaussianInt) (hN : |N.re| < 2 ^ (w - 1))
    (rest : List (Fin (A + 4))) (hsrc : ρ .src = coeffSyms A w (red w N) ++ rest)
    (hwn : (ρ .wn).length = w) (hmn : (ρ .mn).length = m)
    (hnn : (ρ .nn).length = topN m)
    (hsq : ρ .sq = binSyms m (S * S)) (hbn : (ρ .bn).length = b) (hpn : (ρ .pn).length = p)
    (hwo : (ρ .wo).length = W) (htm : ρ .tm = []) (hu1 : ρ .u1 = []) (hsg : ρ .sg = [])
    (hxa : ρ .xa = []) (hxc : ρ .xc = []) (hcy : ρ .cy = []) :
    RRuns body rg ι (rndCoeffProg rg ι hι hT hQ) ρ
      (Function.update (Function.update ρ .src rest) .acc
        ((binSyms W (rndCoeff b S p N.re)).reverse ++ ρ .acc))
      (rndCoeffCost T m w b p W) := by
  have hm : 1 ≤ m := le_trans hw hwm
  obtain ⟨hNlt, hNle, -⟩ := topN_facts hm
  set v := (red w N).1.val with hv
  have hv2 : v < 2 ^ w := ZMod.val_lt _
  set mag := rndMag w v with hmag
  have hmag2 : mag < 2 ^ w := rndMag_lt w v hv2
  have hmagm : mag < 2 ^ m := lt_of_lt_of_le hmag2 (Nat.pow_le_pow_right (by norm_num) hwm)
  set ρA := Function.update (Function.update ρ .src rest) .xa (binSyms m mag) with hρA
  have sA : RRuns body rg ι (rndPhaseA rg) ρ ρA (12 * w + 4 * m + 21) :=
    phaseA_runs hcr hdisj hA hw hwm (red w N) rest hsrc hwn hmn htm hu1 hsg hxa
  set L := 2 * b + 4 + (topN m + 1) with hL
  set X := 2 ^ (2 * b + 4) * (mag * (S * S)) with hX
  have hXL : X < 2 ^ L := by
    have h1 : mag * (S * S) < 2 ^ (topN m + 1) := by
      calc mag * (S * S) < 2 ^ m * 2 ^ m := Nat.mul_lt_mul'' hmagm hSm
        _ = 2 ^ (2 * m) := by rw [← pow_add]; ring_nf
        _ ≤ 2 ^ (topN m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ L = 2 ^ (2 * b + 4) * 2 ^ (topN m + 1) := by rw [hL, pow_add]
    rw [h2, hX]
    exact Nat.mul_lt_mul_of_pos_left (k := 2 ^ (2 * b + 4)) h1 (by positivity)
  set ρB := Function.update (Function.update ρA .xa []) .xc (binSyms L X) with hρB
  have sB : RRuns body rg ι (rndPhaseB rg ι hι hT hQ) ρA ρB
      ((T + 773) * ssCostBound m + 164 * m + 463 + (2 * m + 2) + (4 * b + 4) + (4 * b + 4) + 1) :=
    phaseB_runs hcr hdisj hι hT hQ hm hmagm hSm (by simp [ρA]) (by simp [ρA, hsq])
      (by simp [ρA, hnn]) (by simp [ρA, hbn]) (by simp [ρA, htm]) (by simp [ρA, hxc])
  have sC : RRuns body rg ι (rndPhaseC rg) ρB
      (Function.update (Function.update ρB .xc []) .acc
        ((binSyms W (rndDiv p X)).reverse ++ ρB .acc))
      ((4 * p + 4) + (4 * W + 4) + (2 * 1 + 2) + (2 * (L - p - W) + 2)) :=
    phaseC_runs hcr hdisj hXL (by simp [ρB]) (by simp [ρB, ρA, hcy]) (by simp [ρB, ρA, hpn])
      (by simp [ρB, ρA, hwo]) (by simp [ρB, ρA, htm])
  have hrd : rndDiv p X = rndCoeff b S p N.re := by
    rw [hX, hmag, hv]
    exact rndCoeff_eq hw b S p hN
  refine rruns_mono (rruns_congr (rruns_seq hdisj sA (rruns_seq hdisj sB sC)) ?_) ?_
  · rw [hrd]
    funext r
    simp only [ρB, ρA, Function.update_apply]
    split_ifs <;> simp_all
  · unfold rndCoeffCost
    have : L - p - W ≤ 2 * b + 4 + (4 * m + 1) := by omega
    omega

end Phases

/-! ### The loop -/

section Loop

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RndReg → Fin T}
  {ι : Fin 64 → Fin T}

/-- A loop over a list: the register file `st l done` holds the remaining elements `l` and the
processed ones `done`; register `g` is nonempty exactly while elements remain, and each element
satisfying `ok` is processed by `p` within `b` steps. -/
private theorem while_runs (hdisj : ∀ r j, rg r ≠ ι j) {α : Type} (g : RndReg)
    (p : Pr P T Q A U) (ok : α → Prop) (st : List α → List α → RndReg → List (Fin (A + 4)))
    (b : ℕ) (hstep : ∀ a rest done, ok a →
      RRuns body rg ι p (st (a :: rest) done) (st rest (done ++ [a])) b)
    (hne : ∀ a rest done, st (a :: rest) done g ≠ [])
    (hend : ∀ done, st [] done g = []) :
    ∀ l done, (∀ a ∈ l, ok a) →
      RRuns body rg ι (rndWhile (rg g) p) (st l done) (st [] (done ++ l))
        (l.length * (b + 2) + 2) := by
  have key : ∀ (l done : List α), (∀ a ∈ l, ok a) → ∀ (v : HS T Q A U) (S : Stacks T A),
      RClean ι S → RHolds rg S (st l done) → v.flag = (S.R (rg g)).head?.isSome →
      ∃ v' S' n, v'.user = v.user ∧ n ≤ l.length * (b + 2) + 1 ∧
        Exec body (.loop (·.flag) (.seq p (.act (peekR (rg g))))) (mk v S) n (mk v' S') ∧
        RHolds rg S' (st [] (done ++ l)) ∧ RFr rg S S' := by
    intro l
    induction l with
    | nil =>
        intro done _ v S _ hS hf
        refine ⟨v, S, 1, rfl, by simp, .loop_false ?_, by simpa using hS, rfr_refl S⟩
        rw [mk_var, hf, hS g, hend]; rfl
    | cons a rest ih =>
        intro done hok v S hc hS hf
        obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ :=
          hstep a rest done (hok a (by simp)) v S hc hS
        have e₂ := peekR_run (rg g) v₁ S₁ ▸ Exec.act (body := body) (peekR (rg g)) (mk v₁ S₁)
        obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hS₃, hf₃⟩ := ih (done ++ [a])
          (fun x hx => hok x (by simp [hx])) { v₁ with flag := (S₁.R (rg g)).head?.isSome } S₁
          (rclean_of_fr hdisj hc hf₁) hS₁ rfl
        have hft : v.flag = true := by
          rw [hf, hS g]
          cases h : st (a :: rest) done g with
          | nil => exact absurd h (hne a rest done)
          | cons _ _ => rfl
        refine ⟨v₃, S₃, n₁ + 1 + n₃ + 1, hu₃.trans hu₁, ?_,
          Exec.loop_true (by simpa using hft) (Exec.seq he₁ e₂) he₃, ?_, rfr_trans hf₁ hf₃⟩
        · simp only [List.length_cons]
          nlinarith
        · simpa using hS₃
  intro l done hok v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ :=
    key l done hok { v with flag := (S.R (rg g)).head?.isSome } S hc hS rfl
  exact ⟨v', S', 1 + n, hu, by omega,
    Exec.seq (peekR_run (rg g) v S ▸ Exec.act (body := body) (peekR (rg g)) (mk v S)) he, hS', hf⟩

end Loop

/-! ### The stage -/

section Stage

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- The register file of the loop: the coefficients `l` still on `src`, the words of `done` on
`acc` (latest on top). -/
private noncomputable def rndSt (ρ₀ : RndReg → List (Fin (A + 4))) (w W b S p : ℕ)
    (l done : List GaussianInt) :
    RndReg → List (Fin (A + 4)) :=
  Function.update (Function.update ρ₀ .src ((l.map (red w)).flatMap (coeffSyms A w))) .acc
    (((done.map fun N => rndCoeff b S p N.re).flatMap (binSyms W)).reverse)

/-- **The rounding stage.** The register `src` holds the coefficient stream of the Gaussian
numerators `N i` (`w` pair symbols each); afterwards `src` is empty and `dst` gains the words
`binSyms W (rndCoeff b S p (N i).re)`, word `0` on top, each least significant bit on top. Every
other register, the left stacks, `inp`, `out` and `user` are unchanged. -/
theorem roundStage_exec (body : P → Pr P T Q A U) {rg : RndReg → Fin T}
    (hcr : Function.Injective rg) {ι : Fin 64 → Fin T} (hι : Function.Injective ι)
    (hdisj : ∀ r j, rg r ≠ ι j) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 4 ≤ A)
    {w m b p W S : ℕ} (hw : 1 ≤ w) (hwm : w ≤ m) (hSm : S * S < 2 ^ m)
    (N : Fin S → GaussianInt) (hN : ∀ i, |(N i).re| < 2 ^ (w - 1))
    (v : HS T Q A U) (St : Stacks T A) (hL : ∀ j, St.L (ι j) = []) (hR : ∀ j, St.R (ι j) = [])
    (hsrc : St.R (rg .src) = (List.ofFn fun i => red w (N i)).flatMap (coeffSyms A w))
    (hwn : (St.R (rg .wn)).length = w) (hmn : (St.R (rg .mn)).length = m)
    (hnn : (St.R (rg .nn)).length = topN m) (hsq : St.R (rg .sq) = binSyms m (S * S))
    (hbn : (St.R (rg .bn)).length = b) (hpn : (St.R (rg .pn)).length = p)
    (hwo : (St.R (rg .wo)).length = W) (htm : St.R (rg .tm) = []) (hu1 : St.R (rg .u1) = [])
    (hsg : St.R (rg .sg) = []) (hxa : St.R (rg .xa) = []) (hxc : St.R (rg .xc) = [])
    (hcy : St.R (rg .cy) = []) (hacc : St.R (rg .acc) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ roundStageCost T m w b p W S ∧
      Exec body (roundStage rg ι hι hT hQ) (mk v St) n
        (mk v' { St with R := (Function.update (Function.update St.R (rg .src) []) (rg .dst)
          ((List.ofFn fun i => rndCoeff b S p (N i).re).flatMap (binSyms W) ++
            St.R (rg .dst))) }) := by
  set ρ₀ : RndReg → List (Fin (A + 4)) := fun r => St.R (rg r) with hρ₀
  set Ns := List.ofFn N with hNs
  set st := rndSt ρ₀ w W b S p with hst
  have hstep : ∀ a rest done, |a.re| < 2 ^ (w - 1) →
      RRuns body rg ι (rndCoeffProg rg ι hι hT hQ) (st (a :: rest) done) (st rest (done ++ [a]))
        (rndCoeffCost T m w b p W) := by
    intro a rest done ha
    refine rruns_congr (coeff_runs hcr hdisj hA hι hT hQ hw hwm hSm a ha
      ((rest.map (red w)).flatMap (coeffSyms A w)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      ?_ <;> simp [st, rndSt, ρ₀, hwn, hmn, hnn, hsq, hbn, hpn, hwo, htm, hu1, hsg, hxa, hxc, hcy]
    funext r
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  have hne : ∀ a rest done, st (a :: rest) done .src ≠ [] := by
    intro a rest done
    have : 0 < (st (a :: rest) done .src).length := by simp [st, rndSt]; omega
    intro h; rw [h] at this; simp at this
  have hend : ∀ done, st [] done .src = [] := by intro done; simp [st, rndSt]
  have hok : ∀ a ∈ Ns, |a.re| < 2 ^ (w - 1) := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    exact hN i
  have hloop := while_runs hdisj .src (rndCoeffProg rg ι hι hT hQ) _ st _ hstep hne hend Ns [] hok
  have hmove := moveR_runs (body := body) (ι := ι) hcr (a := .acc) (b := .dst) (by decide)
    (ρ := st [] ([] ++ Ns)) (n := S * W)
    (by simp only [st, rndSt, Function.update_self, List.length_reverse, length_flatMap_binSyms,
          List.length_map, Ns, List.length_ofFn, List.nil_append])
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := rruns_seq hdisj hloop hmove v St
    (fun j => ⟨hL j, hR j⟩) (by
      intro r
      simp only [st, rndSt, Function.update_apply]
      split_ifs with h1 h2
      · subst h1; simp [hacc]
      · subst h2; simp [hsrc, Ns, List.map_ofFn, Function.comp_def]
      · rfl)
  refine ⟨v', n, hu, ?_, ?_⟩
  · have e : roundStageCost T m w b p W S =
        S * (rndCoeffCost T m w b p W + 2) + 2 + (2 * (S * W) + 2) := by
      unfold roundStageCost rndCoeffCost; ring
    rw [e]
    simpa [Ns] using hn
  · obtain ⟨h1, h2, h3, h4⟩ := hf
    have hSe : S' = { St with R := (Function.update (Function.update St.R (rg .src) []) (rg .dst)
        ((List.ofFn fun i => rndCoeff b S p (N i).re).flatMap (binSyms W) ++
          St.R (rg .dst))) } := by
      refine Stacks.ext h1 h2 h3 ?_
      funext k
      dsimp only
      by_cases hk : ∃ r, rg r = k
      · obtain ⟨r, rfl⟩ := hk
        rw [hS' r, holds_upd hcr (holds_upd hcr (fun r => rfl) .src []) .dst]
        simp only [st, rndSt, Function.update_apply]
        split_ifs <;> simp_all [Ns, List.map_ofFn, Function.comp_def]
      · push Not at hk
        rw [h4 k hk, upd_off _ _ _ hk, upd_off _ _ _ hk]
    rw [← hSe]
    exact he

/-- `roundStageCost` with the multiplier's bound in logarithms (`ssMul_cost_le`). -/
theorem roundStageCost_le (T : ℕ) {m : ℕ} (hm : 1 ≤ m) (w b p W S : ℕ) :
    roundStageCost T m w b p W S ≤
      S * (ssMulConst * (T + 1) * mLogLog m + 12 * w + 14 * m + 12 * b + 4 * p + 6 * W + 58) +
        4 := by
  have h := ssMul_cost_le T hm
  unfold roundStageCost
  gcongr

end Stage

/-! ### The square -/

section Square

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- `S²` in binary on `sq`: `ssMul` squares `sb` onto `xc`, and the product word moves onto `sq`
with `|pd|` zero bits appended at its most significant end. -/
noncomputable def rndSquare (rg : RndReg → Fin T) (ι : Fin 64 → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (ssMul ι hι hT hQ (rg .sb) (rg .sb) (rg .ns) (rg .xc))
  (.seq (moveR (rg .xc) (rg .tm) id)
  (.seq (zeroBits (rg .pd) (rg .tm) (rg .u1))
    (moveR (rg .tm) (rg .sq) id)))

/-- **The square.** From `binSyms ℓ S` on `sb`, `topN ℓ` and `m - (topN ℓ + 1)` in unary on `ns`
and `pd`, the empty `sq` ends holding `binSyms m (S * S)`; every other register, the left stacks,
`inp`, `out` and `user` are unchanged. -/
theorem rndSquare_exec (body : P → Pr P T Q A U) {rg : RndReg → Fin T}
    (hcr : Function.Injective rg) {ι : Fin 64 → Fin T} (hι : Function.Injective ι)
    (hdisj : ∀ r j, rg r ≠ ι j) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) {ℓ m S : ℕ} (hℓ : 1 ≤ ℓ)
    (hS : S < 2 ^ ℓ) (hm : topN ℓ + 1 ≤ m) (v : HS T Q A U) (St : Stacks T A)
    (hL : ∀ j, St.L (ι j) = []) (hR : ∀ j, St.R (ι j) = []) (hsb : St.R (rg .sb) = binSyms ℓ S)
    (hns : (St.R (rg .ns)).length = topN ℓ) (hpd : (St.R (rg .pd)).length = m - (topN ℓ + 1))
    (hxc : St.R (rg .xc) = []) (htm : St.R (rg .tm) = []) (hu1 : St.R (rg .u1) = [])
    (hsq : St.R (rg .sq) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (T + 773) * ssCostBound ℓ + 164 * ℓ + 463 + 8 * m + 8 ∧
      Exec body (rndSquare rg ι hι hT hQ) (mk v St) n
        (mk v' { St with R := Function.update St.R (rg .sq) (binSyms m (S * S)) }) := by
  set ρ₀ : RndReg → List (Fin (A + 4)) := fun r => St.R (rg r) with hρ₀
  obtain ⟨hlt, -, -⟩ := topN_facts hℓ
  set N := topN ℓ with hN
  have hSS : S * S < 2 ^ (N + 1) := by
    calc S * S < 2 ^ ℓ * 2 ^ ℓ := Nat.mul_lt_mul'' hS hS
      _ = 2 ^ (2 * ℓ) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set ρ₁ := Function.update ρ₀ .xc (binSyms (N + 1) (S * S)) with hρ₁
  have q1 : RRuns body rg ι (ssMul ι hι hT hQ (rg .sb) (rg .sb) (rg .ns) (rg .xc)) ρ₀ ρ₁
      ((T + 773) * ssCostBound ℓ + 164 * ℓ + 463) :=
    rruns_congr (ssMul_runs hcr hdisj hι hT hQ (rc := .xc) (by decide) (by decide) hℓ hS hS
      hsb hsb hns) (by rw [show ρ₀ .xc = [] from hxc, List.append_nil])
  set ρ₂ := Function.update ρ₀ .tm (binSyms (N + 1) (S * S)).reverse with hρ₂
  have q2 : RRuns body rg ι (moveR (rg .xc) (rg .tm) id) ρ₁ ρ₂ (2 * (N + 1) + 2) := by
    refine rruns_congr (moveR_runs hcr (by decide) (by simp [ρ₁])) ?_
    funext r
    simp only [ρ₂, ρ₁, ρ₀, Function.update_apply]
    split_ifs <;> simp_all
  set d := m - (N + 1) with hd
  set ρ₃ := Function.update ρ₀ .tm (binSyms d 0 ++ (binSyms (N + 1) (S * S)).reverse) with hρ₃
  have q3 : RRuns body rg ι (zeroBits (rg .pd) (rg .tm) (rg .u1)) ρ₂ ρ₃ (4 * d + 4) :=
    rruns_congr (zeroBits_runs hcr (by decide) (by decide) (by decide) (by simp [ρ₂, ρ₀, hpd])
      (by simp [ρ₂, ρ₀, hu1])) (by simp [ρ₃, ρ₂])
  have q4 : RRuns body rg ι (moveR (rg .tm) (rg .sq) id) ρ₃
      (Function.update ρ₀ .sq (binSyms m (S * S))) (2 * (d + (N + 1)) + 2) := by
    refine rruns_congr (moveR_runs hcr (by decide) (by simp [ρ₃])) ?_
    have e : (binSyms d 0 ++ (binSyms (N + 1) (S * S)).reverse).reverse ++ ρ₃ .sq =
        (binSyms m (S * S) : List (Fin (A + 4))) := by
      rw [show ρ₃ .sq = [] by simp [ρ₃, ρ₀, hsq], List.append_nil, List.reverse_append,
        List.reverse_reverse, binSyms_zero_right, List.reverse_replicate,
        SS.binSyms_append_replicate hSS hm]
    rw [show ρ₃ .tm = binSyms d 0 ++ (binSyms (N + 1) (S * S)).reverse by simp [ρ₃], e]
    funext r
    simp only [ρ₃, ρ₀, Function.update_apply]
    split_ifs <;> simp_all
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := rruns_seq hdisj q1 (rruns_seq hdisj q2
    (rruns_seq hdisj q3 q4)) v St (fun j => ⟨hL j, hR j⟩) (fun r => rfl)
  refine ⟨v', n, hu, by omega, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hSe : S' = { St with R := Function.update St.R (rg .sq) (binSyms m (S * S)) } := by
    refine Stacks.ext h1 h2 h3 ?_
    funext k
    dsimp only
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hk
      rw [hS' r, holds_upd hcr (fun r => rfl) .sq]
    · push Not at hk
      rw [h4 k hk, upd_off _ _ _ hk]
  rw [← hSe]
  exact he

end Square

end IntegerMultBounds.MathlibTM2.Fast
