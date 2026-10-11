module

public import IntegerMultBounds.Spec.SyntheticTransform
public import IntegerMultBounds.NLogN.SynthMultiD
public import IntegerMultBounds.NLogN.SynthConv
public import Mathlib.Data.List.GetD

/-! Sanity facts for the synthetic transform statement: mixed-radix addresses
and their digits are inverse; bit reversal of every axis address is an
involution of the record addresses; the multi-axis transforms invert each
other up to `1/M` (`oppT_fwdT`, the paper's `lem:synthetic-characters`); and
the stored order of the exact counterparts is consistent, for every layout
(`oppExact_fwdExact`). -/

@[expose] public section

namespace IntegerMultBounds.Spec.SignedRingProduct

open NLogN

/-! ### Addresses -/

theorem undigits_nil (ds : ℕ → ℕ) : undigits [] ds = 0 := by simp [undigits]

theorem undigits_cons (t : ℕ) (ts : List ℕ) (ds : ℕ → ℕ) :
    undigits (t :: ts) ds = ds 0 * ts.prod + undigits ts (fun i => ds (i + 1)) := by
  simp only [undigits, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
    List.sum_cons]
  simp only [List.drop_succ_cons, List.drop_zero]
  congr 1

theorem digit_cons_zero (t : ℕ) (ts : List ℕ) (n : ℕ) : digit (t :: ts) 0 n = n / ts.prod % t := by
  simp [digit]

theorem digit_cons_succ (t : ℕ) (ts : List ℕ) (i n : ℕ) : digit (t :: ts) (i + 1) n = digit ts i n := by
  simp [digit]

/-- The digit's block divides the whole size. -/
theorem block_dvd : ∀ (ts : List ℕ) (i : ℕ), (ts.drop (i + 1)).prod * ts.getD i 1 ∣ ts.prod
  | [], i => by simp
  | t :: ts, 0 => by simp [mul_comm]
  | t :: ts, i + 1 => by
    simp only [List.drop_succ_cons, List.getD_cons_succ, List.prod_cons]
    exact Dvd.dvd.mul_left (block_dvd ts i) t

theorem digit_mod (ts : List ℕ) (i n : ℕ) : digit ts i (n % ts.prod) = digit ts i n := by
  unfold digit
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self n,
    Nat.mod_mod_of_dvd _ (block_dvd ts i)]

theorem prod_pos {ts : List ℕ} (h : ∀ t ∈ ts, 0 < t) : 0 < ts.prod := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.prod_cons]
    exact Nat.mul_pos (h t (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem getD_pos {ts : List ℕ} (h : ∀ t ∈ ts, 0 < t) (i : ℕ) : 0 < ts.getD i 1 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hi : ts[i]? with _ | x
  · simp
  · simpa using h x (List.mem_of_getElem? hi)

theorem digit_lt {ts : List ℕ} (h : ∀ t ∈ ts, 0 < t) (i n : ℕ) : digit ts i n < ts.getD i 1 :=
  Nat.mod_lt _ (getD_pos h i)

theorem undigits_lt : ∀ (ts : List ℕ) (ds : ℕ → ℕ), (∀ i < ts.length, ds i < ts.getD i 1) →
    undigits ts ds < ts.prod
  | [], _, _ => by simp [undigits]
  | t :: ts, ds, h => by
    rw [undigits_cons, List.prod_cons]
    have h0 := h 0 (by simp)
    have ih := undigits_lt ts (fun i => ds (i + 1)) (fun i hi => by
      have := h (i + 1) (by simp; omega); simpa using this)
    simp only [List.getD_cons_zero] at h0
    have : (ds 0 + 1) * ts.prod ≤ t * ts.prod := Nat.mul_le_mul_right _ h0
    nlinarith

theorem digit_undigits : ∀ (ts : List ℕ) (ds : ℕ → ℕ), (∀ i < ts.length, ds i < ts.getD i 1) →
    ∀ i < ts.length, digit ts i (undigits ts ds) = ds i
  | [], _, _, i, hi => by simp at hi
  | t :: ts, ds, h, 0, _ => by
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    have hu := undigits_lt ts (fun i => ds (i + 1)) (fun i hi => by
      have := h (i + 1) (by simp; omega); simpa using this)
    rw [digit_cons_zero, undigits_cons]
    have hp : 0 < ts.prod := by omega
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hu, zero_add, Nat.mod_eq_of_lt h0]
  | t :: ts, ds, h, i + 1, hi => by
    have hu := undigits_lt ts (fun i => ds (i + 1)) (fun i hi => by
      have := h (i + 1) (by simp; omega); simpa using this)
    rw [digit_cons_succ, undigits_cons, ← digit_mod, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hu]
    exact digit_undigits ts (fun i => ds (i + 1)) (fun i hi => by
      have := h (i + 1) (by simp; omega); simpa using this) i (by simpa using hi)

theorem undigits_digit : ∀ (ts : List ℕ) (n : ℕ), n < ts.prod → undigits ts (fun i => digit ts i n) = n
  | [], n, hn => by simp at hn; simp [undigits]; omega
  | t :: ts, n, hn => by
    rw [undigits_cons]
    rw [List.prod_cons] at hn
    have hp : 0 < ts.prod := Nat.pos_of_ne_zero (by rintro h; rw [h] at hn; simp at hn)
    have e : (fun i => digit (t :: ts) (i + 1) n) = fun i => digit ts i (n % ts.prod) := by
      funext i; rw [digit_cons_succ, digit_mod]
    rw [e, undigits_digit ts (n % ts.prod) (Nat.mod_lt _ hp), digit_cons_zero,
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hn))]
    exact Nat.div_add_mod' n ts.prod

theorem undigits_congr (ts : List ℕ) {ds es : ℕ → ℕ} (h : ∀ i < ts.length, ds i = es i) :
    undigits ts ds = undigits ts es := by
  unfold undigits
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

/-! ### Bit reversal -/

theorem bitrev_zero (j : ℕ) : bitrev 0 j = 0 := by simp [bitrev]

theorem bitrev_succ (a j : ℕ) : bitrev (a + 1) j = 2 * bitrev a j + j / 2 ^ a % 2 := by
  simp only [bitrev, List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one, add_zero]
  congr 1
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro h hh
  have := List.mem_range.mp hh
  rw [show a - h = (a - 1 - h) + 1 by omega, pow_succ]
  ring

theorem bitrev_lt (a j : ℕ) : bitrev a j < 2 ^ a := by
  induction a with
  | zero => simp [bitrev]
  | succ a ih =>
    rw [bitrev_succ, pow_succ]
    have := Nat.mod_lt (j / 2 ^ a) (show 0 < 2 by norm_num)
    omega

theorem bitrev_bit : ∀ (a j h : ℕ), h < a → bitrev a j / 2 ^ h % 2 = j / 2 ^ (a - 1 - h) % 2
  | 0, _, _, hh => absurd hh (Nat.not_lt_zero _)
  | a + 1, j, 0, _ => by
    rw [bitrev_succ, pow_zero, Nat.div_one, Nat.mul_add_mod]
    simp
  | a + 1, j, h + 1, hh => by
    rw [bitrev_succ, pow_succ', ← Nat.div_div_eq_div_mul,
      show (2 * bitrev a j + j / 2 ^ a % 2) / 2 = bitrev a j by omega,
      bitrev_bit a j h (by omega)]
    congr 3; omega

theorem eq_of_bits {x y a : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ a) (h : ∀ i < a, x / 2 ^ i % 2 = y / 2 ^ i % 2) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hi : i < a
  · rw [h i hi]
  · have e1 : x / 2 ^ i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have e2 : y / 2 ^ i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [e1, e2]

theorem bitrev_bitrev {a j : ℕ} (hj : j < 2 ^ a) : bitrev a (bitrev a j) = j := by
  apply eq_of_bits (bitrev_lt a _) hj
  intro i hi
  rw [bitrev_bit a _ i hi, bitrev_bit a j _ (by omega), show a - 1 - (a - 1 - i) = i by omega]

/-- Axis lengths that are powers of two dividing `2r`. -/
def PowAxes (r : ℕ) (ts : List ℕ) : Prop := ∀ t ∈ ts, ∃ a, t = 2 ^ a ∧ 2 ^ a ∣ 2 * r

theorem PowAxes.pos {r : ℕ} {ts : List ℕ} (h : PowAxes r ts) : ∀ t ∈ ts, 0 < t := by
  intro t ht; obtain ⟨a, rfl, -⟩ := h t ht; positivity

theorem PowAxes.getD {r : ℕ} {ts : List ℕ} (h : PowAxes r ts) {i : ℕ} (hi : i < ts.length) :
    ∃ a, ts.getD i 1 = 2 ^ a ∧ 2 ^ a ∣ 2 * r := by
  rw [List.getD_eq_getElem (l := ts) (d := 1) hi]
  exact h _ (List.getElem_mem hi)

theorem bitrev_axis_lt {r : ℕ} {ts : List ℕ} (h : PowAxes r ts) {i : ℕ} (hi : i < ts.length) (n : ℕ) :
    bitrev (Nat.log 2 (ts.getD i 1)) (digit ts i n) < ts.getD i 1 := by
  obtain ⟨a, ha, -⟩ := h.getD hi
  have := bitrev_lt (Nat.log 2 (ts.getD i 1)) (digit ts i n)
  rwa [ha, Nat.log_pow (by norm_num)] at this ⊢

theorem bitrevAddr_lt {r : ℕ} {ts : List ℕ} (h : PowAxes r ts) (n : ℕ) : bitrevAddr ts n < ts.prod :=
  undigits_lt ts _ fun _i hi => bitrev_axis_lt h hi n

theorem digit_bitrevAddr {r : ℕ} {ts : List ℕ} (h : PowAxes r ts) (n : ℕ) {i : ℕ} (hi : i < ts.length) :
    digit ts i (bitrevAddr ts n) = bitrev (Nat.log 2 (ts.getD i 1)) (digit ts i n) :=
  digit_undigits ts _ (fun _i hi => bitrev_axis_lt h hi n) i hi

theorem bitrevAddr_bitrevAddr {r : ℕ} {ts : List ℕ} (h : PowAxes r ts) {n : ℕ} (hn : n < ts.prod) :
    bitrevAddr ts (bitrevAddr ts n) = n := by
  conv_rhs => rw [← undigits_digit ts n hn]
  show undigits ts (fun i => bitrev (Nat.log 2 (ts.getD i 1)) (digit ts i (bitrevAddr ts n))) = _
  apply undigits_congr
  intro i hi
  rw [digit_bitrevAddr h n hi]
  obtain ⟨a, ha, -⟩ := h.getD hi
  have hd := digit_lt h.pos i n
  rw [ha] at hd ⊢
  rw [Nat.log_pow (by norm_num)]
  exact bitrev_bitrev hd

/-! ### Character cancellation -/

theorem sum_range_mul {V : Type*} [AddCommMonoid V] (f : ℕ → V) (M : ℕ) :
    ∀ t, ∑ k ∈ Finset.range (t * M), f k = ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range M, f (a * M + b)
  | 0 => by simp
  | t + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul f M t, Finset.sum_range_succ]

theorem shiftNegZ_zero_vec {r : ℕ} [NeZero r] (e : ℕ) : shiftNegZ e (0 : Fin r → ℂ) = 0 := by
  rw [← shiftZCLM_apply, map_zero]

theorem exp_mod_axis {r t : ℕ} (ht : t ∣ 2 * r) (D a : ℕ) :
    2 * r / t * D * a % (2 * r) = 2 * r / t * (D % t) * a % (2 * r) := by
  have hc : 2 * r / t * t = 2 * r := Nat.div_mul_cancel ht
  conv_lhs => rw [← Nat.mod_add_div D t]
  have e : 2 * r / t * (D % t + t * (D / t)) * a = 2 * r / t * (D % t) * a + (2 * r / t * t) * (D / t * a) := by
    ring
  rw [e, hc, Nat.add_mul_mod_self_left]

/-- The exponent `Σᵢ (2r/tᵢ) Dᵢ kᵢ`. -/
def axisExp (r : ℕ) (ts : List ℕ) (D : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((List.range ts.length).map fun i => (2 * r / ts.getD i 1) * D i * digit ts i k).sum

theorem axisExp_cons (r t : ℕ) (ts : List ℕ) (D : ℕ → ℕ) {a b : ℕ} (ha : a < t) (hb : b < ts.prod) :
    axisExp r (t :: ts) D (a * ts.prod + b) = 2 * r / t * D 0 * a + axisExp r ts (fun i => D (i + 1)) b := by
  simp only [axisExp, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
  congr 1
  · rw [List.getD_cons_zero, digit_cons_zero, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt hb, zero_add, Nat.mod_eq_of_lt ha]
  · congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.getD_cons_succ, digit_cons_succ]
    rw [← digit_mod ts i, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- Orthogonality over all addresses. -/
theorem sum_axisExp {r : ℕ} [NeZero r] : ∀ (ts : List ℕ), PowAxes r ts → ∀ (D : ℕ → ℕ) (v : Fin r → ℂ),
    ∑ k ∈ Finset.range ts.prod, shiftNegZ (axisExp r ts D k) v =
      if ∀ i < ts.length, D i % ts.getD i 1 = 0 then (ts.prod : ℂ) • v else 0
  | [], _, D, v => by simp [axisExp, shiftNegZ_zero]
  | t :: ts, h, D, v => by
    have ht : PowAxes r ts := fun x hx => h x (by simp [hx])
    obtain ⟨f, hf, hdvd'⟩ := h t (by simp)
    have hdvd : t ∣ 2 * r := hf ▸ hdvd'
    have htp : 0 < t := by rw [hf]; positivity
    rw [List.prod_cons, Nat.mul_comm t, Nat.mul_comm, sum_range_mul _ ts.prod t]
    have e : ∀ a ∈ Finset.range t, ∑ b ∈ Finset.range ts.prod, shiftNegZ (axisExp r (t :: ts) D (a * ts.prod + b)) v
        = shiftNegZ (2 * r / t * D 0 * a) (∑ b ∈ Finset.range ts.prod,
            shiftNegZ (axisExp r ts (fun i => D (i + 1)) b) v) := by
      intro a ha
      rw [shiftNegZ_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [axisExp_cons r t ts D (Finset.mem_range.mp ha) (Finset.mem_range.mp hb), shiftNegZ_add]
    rw [Finset.sum_congr rfl e, sum_axisExp ts ht (fun i => D (i + 1)) v]
    by_cases hall : ∀ i < ts.length, D (i + 1) % ts.getD i 1 = 0
    · rw [ite_eq_left hall]
      simp only [shiftNegZ_smul, ← Finset.smul_sum]
      by_cases h0 : D 0 % t = 0
      · have hc : ∀ i < (t :: ts).length, D i % (t :: ts).getD i 1 = 0 := by
          intro i hi
          cases i with
          | zero => simpa using h0
          | succ i => simpa using hall i (by simpa using hi)
        rw [ite_eq_left hc]
        have hz : ∀ a ∈ Finset.range t, shiftNegZ (2 * r / t * D 0 * a) v = v := fun a _ => by
          rw [shiftNegZ_congr_mod (e₂ := 0) (by rw [exp_mod_axis hdvd, h0]; simp), shiftNegZ_zero]
        rw [Finset.sum_congr rfl hz, Finset.sum_const, Finset.card_range,
          ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
        congr 1; push_cast; ring
      · have hc : ¬ ∀ i < (t :: ts).length, D i % (t :: ts).getD i 1 = 0 := fun hc =>
          h0 (by simpa using hc 0 (by simp))
        rw [ite_eq_right hc]
        have hz : ∑ a ∈ Finset.range t, shiftNegZ (2 * r / t * D 0 * a) v =
            ∑ a : Fin t, shiftNegZ ((2 * r / t) * (D 0 % t) * a.val) v := by
          rw [Finset.sum_range]
          apply Finset.sum_congr rfl
          intro a _
          exact shiftNegZ_congr_mod (exp_mod_axis hdvd _ _) v
        rw [hz, sum_shiftNegZ_eq_zero hdvd hf (Nat.pos_of_ne_zero h0) (Nat.mod_lt _ htp), smul_zero]
    · have hc : ¬ ∀ i < (t :: ts).length, D i % (t :: ts).getD i 1 = 0 := fun hc =>
        hall fun i hi => by simpa using hc (i + 1) (by simpa using hi)
      rw [ite_eq_right hall, ite_eq_right hc]
      simp [shiftNegZ_zero_vec]

theorem list_sum_map_sub {R : Type*} [AddCommGroup R] (L : List ℕ) (b c : ℕ → R) :
    (L.map b).sum - (L.map c).sum = (L.map fun i => b i - c i).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]; abel

/-- The composite exponent `F⁺` after `F⁻` is the axis exponent of the digit differences. -/
theorem exp_compose {r : ℕ} [NeZero r] {ts : List ℕ} (h : PowAxes r ts) (n k m : ℕ) :
    (synthExpL r ts n k + (2 * r - synthExpL r ts k m % (2 * r)) % (2 * r)) % (2 * r) =
      axisExp r ts (fun i => digit ts i n + (ts.getD i 1 - digit ts i m)) k % (2 * r) := by
  rw [← ZMod.natCast_eq_natCast_iff']
  have hle : synthExpL r ts k m % (2 * r) ≤ 2 * r := (Nat.mod_lt _ (by have := NeZero.pos r; omega)).le
  push_cast [ZMod.natCast_mod, Nat.cast_sub hle, ZMod.natCast_self]
  simp only [synthExpL, axisExp, Nat.cast_list_sum, List.map_map]
  have h2r : (2 : ZMod (2 * r)) * (r : ZMod (2 * r)) = 0 := by exact_mod_cast ZMod.natCast_self (2 * r)
  rw [h2r, zero_sub, ← sub_eq_add_neg, list_sum_map_sub]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  obtain ⟨a, ha, hdvd⟩ := h.getD hi'
  have hm := digit_lt h.pos i m
  have hc : (2 * r / ts.getD i 1 * ts.getD i 1 : ℕ) = 2 * r := by rw [ha]; exact Nat.div_mul_cancel hdvd
  have hc' : ((2 * r / ts.getD i 1 : ℕ) : ZMod (2 * r)) * (ts.getD i 1 : ℕ) = 0 := by
    rw [← Nat.cast_mul, hc, ZMod.natCast_self]
  simp only [Function.comp_apply]
  push_cast [Nat.cast_sub hm.le]
  linear_combination -(digit ts i k : ZMod (2 * r)) * hc'

theorem digits_eq {ts : List ℕ} (_h : ∀ t ∈ ts, 0 < t) {n m : ℕ} (hn : n < ts.prod) (hm : m < ts.prod)
    (hd : ∀ i < ts.length, digit ts i n = digit ts i m) : n = m := by
  rw [← undigits_digit ts n hn, ← undigits_digit ts m hm]
  exact undigits_congr ts hd

theorem diff_mod_eq_zero {t x y : ℕ} (hx : x < t) (hy : y < t) : (x + (t - y)) % t = 0 ↔ x = y := by
  constructor
  · intro h
    by_cases hxy : y ≤ x
    · rw [show x + (t - y) = (x - y) + t by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
  · rintro rfl; rw [show x + (t - x) = t by omega, Nat.mod_self]

/-- `lem:synthetic-characters` for the multi-axis transforms: `F⁺ F⁻ = M⁻¹ I`. -/
theorem oppT_fwdT {r : ℕ} [NeZero r] {ts : List ℕ} (h : PowAxes r ts) (z : ℕ → Fin r → ℂ) {n : ℕ}
    (hn : n < ts.prod) : oppT ts (fwdT ts z) n = (1 / (ts.prod : ℂ)) • z n := by
  have hM : (ts.prod : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (prod_pos h.pos).ne'
  simp only [oppT, fwdT, shiftInv, shiftNegZ_smul, shiftNegZ_sum, shiftNegZ_add, ← Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hterm : ∀ m ∈ Finset.range ts.prod, ∑ k ∈ Finset.range ts.prod,
      shiftNegZ (synthExpL r ts n k + (2 * r - synthExpL r ts k m % (2 * r)) % (2 * r)) (z m) =
      if m = n then (ts.prod : ℂ) • z m else 0 := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    rw [Finset.sum_congr rfl (fun k _ => shiftNegZ_congr_mod (exp_compose h n k m) (z m)),
      sum_axisExp ts h _ (z m)]
    congr 1
    apply propext
    constructor
    · intro hc
      exact (digits_eq h.pos hm' hn fun i hi =>
        ((diff_mod_eq_zero (digit_lt h.pos i n) (digit_lt h.pos i m)).mp (hc i hi)).symm)
    · rintro rfl i _
      exact (diff_mod_eq_zero (digit_lt h.pos i m) (digit_lt h.pos i m)).mpr rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr hn), smul_smul]
  congr 1
  field_simp

/-! ### The stored order -/

/-- The opposite counterpart undoes the forward counterpart for every layout: `F⁺B⁻¹L⁻¹ · LBF⁻ = M⁻¹ I`. -/
theorem oppExact_fwdExact {r : ℕ} [NeZero r] {ts : List ℕ} (h : PowAxes r ts) (Lp : Equiv.Perm (Fin ts.prod))
    (z : ℕ → Fin r → ℂ) {n : ℕ} (hn : n < ts.prod) :
    oppExact ts Lp (fwdExact ts Lp z) n = (1 / (ts.prod : ℂ)) • z n := by
  rw [← oppT_fwdT h z hn]
  unfold oppExact oppT
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hb := bitrevAddr_lt h j
  rw [dite_eq_left (by rw [Nat.mod_eq_of_lt hb]; exact hb)]
  congr 1
  unfold fwdExact
  rw [dite_eq_left (Lp ⟨bitrevAddr ts j % ts.prod, _⟩).isLt]
  simp only [Fin.eta, Equiv.symm_apply_apply, Nat.mod_eq_of_lt hb, bitrevAddr_bitrevAddr h hj']

end IntegerMultBounds.Spec.SignedRingProduct
