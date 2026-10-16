module

public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.MathlibTM2.Mult.Rounds

/-!
# Arithmetic of the twiddle pass

**Monomials on numerators.** A record of `ℛ_r = ℂ[y]/(y^r + 1)` with grid coefficients
`Z c / 2^p` (`Z : Fin r → GaussianInt`) is multiplied by `y^e` coefficientwise on the
numerators: `twShiftZ e Z` (`twShiftZ_toComplex`: `shiftNegZ e` of the grid record is the grid
record of `twShiftZ e Z`). On coefficient lists, for `r = 2^ℓ` (`twShiftL_ofFn`): with
`s = e mod r`, the list is split at `r - s`, the tail moves before the head, the wrapped part is
negated, and the whole record is negated when bit `ℓ` of `e` is set (`y^r = -1`).

**Coefficient streams.** `tw_cstream_take`, `tw_cstream_drop`: cutting a stream `cstream A w l`
after `k w` symbols cuts `l` after `k` coefficients; `tw_cstream_neg`: the stream of the
residues of `-z`.

**The exponent scan.** The address `n` of a record is read least significant bit first,
`binBits N n` with `N = es.sum` (`tw_binBits_sum`: it is the concatenation of the coordinates of
the axes `d - 1, …, 0`). Round `h` attaches a role to every address bit (`twRoles es h`, from
`twSeg (aᵢ) h` per axis): the low bits `0, …, h - 1` of a participating axis (`h < aᵢ`) are
`low` (`bitSymbol true`), bit `h` is `sel` (`separator`), every other bit is `skip`
(`bitSymbol false`). The scan `twStep h` keeps the low bits read so far (latest first) and a sum
`F` modulo `2^(h+1)`: at `sel` with bit `1` it adds the value of the low bits, and at every
`sel` it forgets them. `twFold_roles`: after the whole address, `F = twF h es n mod 2^(h+1)`,
where `twF h es n = Σ_{i : h < aᵢ} bitₕ(xᵢ) (xᵢ mod 2^h)` (`twF_eq_sum`). `twGood_roles`: at
every `sel` the scan holds exactly `h` low bits (the hypothesis of the machine's addition).
`twE_mod`: for `h ≤ ℓ`, `twE es (2^ℓ) h (parts es h) n mod 2^(ℓ+1) = 2^(ℓ-h) (F mod 2^(h+1))`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult.Rounds

set_option linter.unusedSimpArgs false

/-! ### Monomials on numerators -/

section Shift

variable {r : ℕ} [NeZero r]

/-- Multiplication by `y^e` modulo `y^r + 1` on the numerators of a record: output `i` is the
signed source coefficient of `shiftNegZ_apply`. -/
def twShiftZ (e : ℕ) (Z : Fin r → GaussianInt) : Fin r → GaussianInt :=
  fun i => (-1) ^ (((shiftSrc r e i).val + e) / r) * Z (shiftSrc r e i)

/-- `twShiftZ` computes `shiftNegZ` on grid records. -/
theorem twShiftZ_toComplex (p e : ℕ) (Z : Fin r → GaussianInt) (i : Fin r) :
    GaussianInt.toComplex (twShiftZ e Z i) / 2 ^ p =
      shiftNegZ e (fun c => GaussianInt.toComplex (Z c) / 2 ^ p) i := by
  rw [shiftNegZ_apply, twShiftZ]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem twShiftZ_toComplex_fun (p e : ℕ) (Z : Fin r → GaussianInt) :
    (fun i => GaussianInt.toComplex (twShiftZ e Z i) / 2 ^ p) =
      shiftNegZ e (fun c => GaussianInt.toComplex (Z c) / 2 ^ p) :=
  funext (twShiftZ_toComplex p e Z)

lemma tw_neg_one_pow (k : ℕ) : ((-1 : GaussianInt) ^ k) = if k % 2 = 1 then -1 else 1 := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [ite_eq_right (by omega)]
    exact Even.neg_one_pow (Nat.even_iff.mpr h)
  · rw [ite_eq_left h]
    exact Odd.neg_one_pow (Nat.odd_iff.mpr h)

/-- Outputs below `s = e mod r` come from the wrapped tail, with sign `-(-1)^(e / r)`. -/
lemma twShiftZ_lt (e : ℕ) (Z : Fin r → GaussianInt) (i : Fin r) (hi : i.val < e % r) :
    twShiftZ e Z i = (if (e / r) % 2 = 1 then 1 else -1) *
      Z ⟨r - e % r + i.val, by have := Nat.mod_lt e (NeZero.pos r); omega⟩ := by
  have hr := NeZero.pos r
  have hs := Nat.mod_lt e hr
  have hsrc : (shiftSrc r e i).val = r - e % r + i.val := by
    show (i.val + (r - e % r)) % r = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hq : ((shiftSrc r e i).val + e) / r = e / r + 1 := by
    rw [hsrc]
    have he := Nat.mod_add_div e r
    rw [show r - e % r + i.val + e = i.val + r * (e / r + 1) by
      rw [Nat.mul_add, Nat.mul_one]; generalize r * (e / r) = q at he ⊢; omega]
    rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [twShiftZ, hq, tw_neg_one_pow]
  congr 1
  · rcases Nat.mod_two_eq_zero_or_one (e / r) with h | h <;> simp [h, Nat.add_mod]
  · exact congrArg Z (Fin.ext hsrc)

/-- Outputs from `s = e mod r` on come from the head, with sign `(-1)^(e / r)`. -/
lemma twShiftZ_ge (e : ℕ) (Z : Fin r → GaussianInt) (i : Fin r) (hi : e % r ≤ i.val) :
    twShiftZ e Z i = (if (e / r) % 2 = 1 then -1 else 1) *
      Z ⟨i.val - e % r, by have := i.isLt; omega⟩ := by
  have hr := NeZero.pos r
  have hsrc : (shiftSrc r e i).val = i.val - e % r := by
    simp only [shiftSrc]
    rw [show i.val + (r - e % r) = (i.val - e % r) + r by have := i.isLt; omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have hq : ((shiftSrc r e i).val + e) / r = e / r := by
    rw [hsrc]
    have he := Nat.mod_add_div e r
    rw [show i.val - e % r + e = i.val + r * (e / r) by omega,
      Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  rw [twShiftZ, hq, tw_neg_one_pow]
  exact congrArg _ (congrArg Z (Fin.ext hsrc))

/-- `twShiftZ` has period `2r` in the exponent. -/
lemma twShiftZ_mod (e : ℕ) (Z : Fin r → GaussianInt) :
    twShiftZ (e % (2 * r)) Z = twShiftZ e Z := by
  have hr := NeZero.pos r
  funext i
  have h1 : e % (2 * r) % r = e % r := Nat.mod_mod_of_dvd e (dvd_mul_left r 2)
  have h2 : e % (2 * r) / r % 2 = e / r % 2 := by
    rw [Nat.mul_comm 2 r, Nat.mod_mul_right_div_self, Nat.mod_mod]
  by_cases hi : i.val < e % r
  · rw [twShiftZ_lt _ _ _ (by rw [h1]; exact hi), twShiftZ_lt _ _ _ hi, h2]
    simp only [h1]
  · rw [twShiftZ_ge _ _ _ (by rw [h1]; omega), twShiftZ_ge _ _ _ (by omega), h2]
    simp only [h1]

end Shift

/-- The list form of `y^e` on a record of `2^ℓ` coefficients: split at `r - s`, `s = e mod r`,
the tail before the head, the wrapped part negated, everything negated when bit `ℓ` of `e` is
set. -/
def twShiftL (ℓ e : ℕ) (l : List GaussianInt) : List GaussianInt :=
  if e.testBit ℓ then
    l.drop (2 ^ ℓ - e % 2 ^ ℓ) ++ (l.take (2 ^ ℓ - e % 2 ^ ℓ)).map (fun z => -z)
  else (l.drop (2 ^ ℓ - e % 2 ^ ℓ)).map (fun z => -z) ++ l.take (2 ^ ℓ - e % 2 ^ ℓ)

lemma tw_testBit_eq (ℓ e : ℕ) : e.testBit ℓ = decide (e / 2 ^ ℓ % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]

theorem twShiftL_ofFn {ℓ : ℕ} (e : ℕ) (Z : Fin (2 ^ ℓ) → GaussianInt) :
    twShiftL ℓ e (List.ofFn Z) = List.ofFn (twShiftZ e Z) := by
  have hr : 0 < 2 ^ ℓ := by positivity
  have hs := Nat.mod_lt e hr
  apply List.ext_getElem
  · unfold twShiftL
    split_ifs <;> simp only [List.length_append, List.length_drop, List.length_map,
      List.length_take, List.length_ofFn] <;> omega
  · intro i h1 h2
    rw [List.getElem_ofFn]
    have hi : i < 2 ^ ℓ := by simpa using h2
    unfold twShiftL
    have hb := tw_testBit_eq ℓ e
    by_cases hlt : i < e % 2 ^ ℓ
    · rw [twShiftZ_lt e Z ⟨i, hi⟩ hlt]
      split_ifs with hg
      · rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_drop, List.getElem_ofFn]
        have : e / 2 ^ ℓ % 2 = 1 := by simpa [hb] using hg
        simp [this]
      · rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_map, List.getElem_drop, List.getElem_ofFn]
        have : ¬ e / 2 ^ ℓ % 2 = 1 := by simpa [hb] using hg
        simp [this]
    · rw [twShiftZ_ge e Z ⟨i, hi⟩ (by show e % 2 ^ ℓ ≤ i; omega)]
      split_ifs with hg
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map, List.getElem_take, List.getElem_ofFn, List.length_drop,
          List.length_ofFn]
        have : e / 2 ^ ℓ % 2 = 1 := by simpa [hb] using hg
        simp only [this, ↓reduceIte, neg_mul, one_mul]
        congr 3
        omega
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_take, List.getElem_ofFn, List.length_map, List.length_drop,
          List.length_ofFn]
        have : ¬ e / 2 ^ ℓ % 2 = 1 := by simpa [hb] using hg
        simp only [this, ↓reduceIte, one_mul]
        congr 2
        omega

/-! ### Coefficient streams -/

section Streams

variable {A w : ℕ}

lemma tw_csyms_length (x : GaussianInt) : (csyms A w x).length = w := by simp [csyms]

lemma tw_cstream_take : ∀ (l : List GaussianInt) (k : ℕ),
    (cstream A w l).take (k * w) = cstream A w (l.take k)
  | [], k => by simp
  | x :: l, 0 => by simp
  | x :: l, k + 1 => by
      rw [cstream_cons, List.take_append, tw_csyms_length,
        List.take_of_length_le (by rw [tw_csyms_length]; nlinarith),
        show (k + 1) * w - w = k * w by rw [Nat.succ_mul]; omega, tw_cstream_take l k,
        List.take_succ_cons, cstream_cons]

lemma tw_cstream_drop : ∀ (l : List GaussianInt) (k : ℕ),
    (cstream A w l).drop (k * w) = cstream A w (l.drop k)
  | [], k => by simp
  | x :: l, 0 => by simp
  | x :: l, k + 1 => by
      rw [cstream_cons, show (k + 1) * w = w + k * w by ring, ← List.drop_drop,
        List.drop_left' (tw_csyms_length x), tw_cstream_drop l k, List.drop_succ_cons]

lemma tw_cstream_eq (l : List GaussianInt) :
    cstream A w l = (l.map (red w)).flatMap (coeffSyms A w) := by
  simp [cstream, csyms, List.flatMap_map]

lemma tw_cstream_neg (l : List GaussianInt) :
    ((l.map (red w)).map (fun z => -z)).flatMap (coeffSyms A w) =
      cstream A w (l.map fun z => -z) := by
  rw [tw_cstream_eq, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z _
  simp [red_neg]

end Streams

/-! ### Bit lists -/

/-- The value of a bit list, least significant bit first. -/
def twVal : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * twVal l

lemma twVal_lt : ∀ l : List Bool, twVal l < 2 ^ l.length
  | [] => by simp [twVal]
  | b :: l => by
      have := twVal_lt l
      have := Bool.toNat_le b
      simp only [twVal, List.length_cons, pow_succ]
      omega

lemma twVal_binBits : ∀ (L x : ℕ), twVal (binBits L x) = x % 2 ^ L
  | 0, x => by simp [twVal, Nat.mod_one]
  | L + 1, x => by
      rw [binBits_succ, twVal, twVal_binBits L, mod_two_pow_succ' x L]
      have : (x.testBit 0).toNat = x % 2 := by
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Nat.testBit_zero, h]
      rw [this]; ring

lemma twVal_append_false : ∀ l : List Bool, twVal (l ++ [false]) = twVal l
  | [] => by simp [twVal]
  | b :: l => by simp [twVal, twVal_append_false l]

lemma tw_map_bitSymbol {A : ℕ} : ∀ l : List Bool,
    (l.map bitSymbol : List (Fin (A + 4))) = binSyms l.length (twVal l)
  | [] => by simp [binSyms]
  | b :: l => by
      rw [List.map_cons, List.length_cons, binSyms_succ, tw_map_bitSymbol l]
      have h1 : (twVal (b :: l)).testBit 0 = b := by
        cases b <;> simp [twVal, Nat.testBit_zero]
      have h2 : twVal (b :: l) / 2 = twVal l := by
        have := Bool.toNat_le b
        simp only [twVal]
        omega
      rw [h1, h2]

/-- `binBits` splits at bit `L`. -/
lemma tw_binBits_append (L e x : ℕ) : binBits (L + e) x = binBits L x ++ binBits e (x / 2 ^ L) := by
  induction L generalizing x with
  | zero => simp
  | succ L ih =>
      rw [Nat.add_right_comm, binBits_succ, binBits_succ, ih, pow_succ', ← Nat.div_div_eq_div_mul]
      rfl

/-! ### The exponent scan -/

section Scan

variable {A : ℕ}

/-- The roles of the `a` bits of one axis in round `h`. -/
def twSeg (A a h : ℕ) : List (Fin (A + 4)) :=
  if h < a then
    List.replicate h (bitSymbol true) ++ separator :: List.replicate (a - h - 1) (bitSymbol false)
  else List.replicate a (bitSymbol false)

/-- The roles of the address bits in round `h`, least significant first: the axes from the last
(least significant) to the first. -/
def twRoles (A : ℕ) : List ℕ → ℕ → List (Fin (A + 4))
  | [], _ => []
  | e :: es, h => twRoles A es h ++ twSeg A e h

lemma twSeg_length (a h : ℕ) : (twSeg A a h).length = a := by
  unfold twSeg
  split_ifs with hh
  · simp only [List.length_append, List.length_replicate, List.length_cons]; omega
  · simp

lemma twRoles_length : ∀ (es : List ℕ) (h : ℕ), (twRoles A es h).length = es.sum
  | [], _ => rfl
  | e :: es, h => by
      rw [twRoles, List.length_append, twRoles_length es h, twSeg_length, List.sum_cons]; ring

lemma tw_sep_ne_true : (separator : Fin (A + 4)) ≠ bitSymbol true := by
  simp [separator, bitSymbol, Fin.ext_iff]

lemma tw_sep_ne_false : (separator : Fin (A + 4)) ≠ bitSymbol false := by
  simp [separator, bitSymbol, Fin.ext_iff]

lemma tw_true_ne_false : (bitSymbol true : Fin (A + 4)) ≠ bitSymbol false := by
  simp [bitSymbol, Fin.ext_iff]

/-- One step of the scan on a role symbol `x` and an address bit `b`: the low bits `V` read so
far (latest first) and the sum `F` modulo `2^(h+1)`. -/
def twStep (h : ℕ) (s : List Bool × ℕ) (q : Fin (A + 4) × Bool) : List Bool × ℕ :=
  if q.1 = separator then ([], if q.2 then (s.2 + twVal s.1.reverse) % 2 ^ (h + 1) else s.2)
  else if q.1 = bitSymbol true then (q.2 :: s.1, s.2) else s

/-- The scan over the first `j` pairs. -/
def twSt (h : ℕ) (L : List (Fin (A + 4) × Bool)) (s : List Bool × ℕ) (j : ℕ) : List Bool × ℕ :=
  (L.take j).foldl (twStep h) s

lemma twSt_succ (h : ℕ) (L : List (Fin (A + 4) × Bool)) (s : List Bool × ℕ) {j : ℕ}
    (hj : j < L.length) : twSt h L s (j + 1) = twStep h (twSt h L s j) L[j] := by
  unfold twSt
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.foldl_append]
  rfl

/-- The scan needs `h` low bits and a reduced sum at every `sel`. -/
def twPre (h : ℕ) (q : Fin (A + 4) × Bool) (s : List Bool × ℕ) : Prop :=
  q.1 = separator → s.1.length = h ∧ s.2 < 2 ^ (h + 1)

/-- The scan meets `twPre` at every position. -/
def twGood (h : ℕ) (L : List (Fin (A + 4) × Bool)) (s : List Bool × ℕ) : Prop :=
  ∀ j (hj : j < L.length), twPre h L[j] (twSt h L s j)

lemma twGood_append {h : ℕ} {L₁ L₂ : List (Fin (A + 4) × Bool)} {s : List Bool × ℕ}
    (h₁ : twGood h L₁ s) (h₂ : twGood h L₂ (L₁.foldl (twStep h) s)) :
    twGood h (L₁ ++ L₂) s := by
  intro j hj
  by_cases hj1 : j < L₁.length
  · rw [List.getElem_append_left hj1]
    have := h₁ j hj1
    unfold twSt at this ⊢
    rwa [List.take_append_of_le_length hj1.le]
  · rw [List.getElem_append_right (by omega)]
    have := h₂ (j - L₁.length) (by simp at hj; omega)
    unfold twSt at this ⊢
    rw [List.take_append, List.take_of_length_le (by omega), List.foldl_append]
    exact this

lemma twFold_low {h : ℕ} : ∀ (bs V : List Bool) (F : ℕ),
    ((List.replicate bs.length (bitSymbol true : Fin (A + 4))).zip bs).foldl (twStep h) (V, F) =
      (bs.reverse ++ V, F)
  | [], V, F => by simp
  | b :: bs, V, F => by
      rw [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.foldl_cons]
      have : twStep h (V, F) ((bitSymbol true : Fin (A + 4)), b) = (b :: V, F) := by
        simp [twStep, tw_sep_ne_true.symm]
      rw [this, twFold_low bs (b :: V) F]
      simp

lemma twFold_skip {h : ℕ} : ∀ (k : ℕ) (bs : List Bool) (s : List Bool × ℕ),
    ((List.replicate k (bitSymbol false : Fin (A + 4))).zip bs).foldl (twStep h) s = s
  | 0, bs, s => by simp
  | k + 1, [], s => by simp
  | k + 1, b :: bs, s => by
      rw [List.replicate_succ, List.zip_cons_cons, List.foldl_cons]
      have : twStep h s ((bitSymbol false : Fin (A + 4)), b) = s := by
        simp [twStep, tw_sep_ne_false.symm, tw_true_ne_false.symm]
      rw [this, twFold_skip k bs s]

lemma twGood_low {h : ℕ} (bs : List Bool) (s : List Bool × ℕ) :
    twGood h ((List.replicate bs.length (bitSymbol true : Fin (A + 4))).zip bs) s := by
  intro j hj hx
  simp only [List.getElem_zip, List.getElem_replicate] at hx
  exact absurd hx tw_sep_ne_true.symm

lemma twGood_skip {h : ℕ} (k : ℕ) (bs : List Bool) (s : List Bool × ℕ) :
    twGood h ((List.replicate k (bitSymbol false : Fin (A + 4))).zip bs) s := by
  intro j hj hx
  simp only [List.getElem_zip, List.getElem_replicate] at hx
  exact absurd hx tw_sep_ne_false.symm

/-- The term of one axis: `bitₕ(x) (x mod 2^h)` when the axis participates. -/
def twTerm (a h x : ℕ) : ℕ := if h < a then x / 2 ^ h % 2 * (x % 2 ^ h) else 0

lemma tw_seg_split {a h : ℕ} (hh : h < a) (x : ℕ) :
    (twSeg A a h).zip (binBits a x) =
      (List.replicate (binBits h x).length (bitSymbol true : Fin (A + 4))).zip (binBits h x) ++
        ((separator : Fin (A + 4)), x.testBit h) ::
          (List.replicate (a - h - 1) (bitSymbol false : Fin (A + 4))).zip
            (binBits (a - h - 1) (x / 2 ^ h / 2)) := by
  have e1 : binBits a x = binBits h x ++ binBits (a - h) (x / 2 ^ h) := by
    rw [← tw_binBits_append]; congr 1; omega
  have e2 : binBits (a - h) (x / 2 ^ h) =
      x.testBit h :: binBits (a - h - 1) (x / 2 ^ h / 2) := by
    obtain ⟨k, hk⟩ : ∃ k, a - h = k + 1 := ⟨a - h - 1, by omega⟩
    rw [hk, binBits_succ, Nat.testBit_div_two_pow, Nat.zero_add]
    rfl
  rw [twSeg, ite_eq_left hh, e1, e2, List.zip_append (by simp), length_binBits, List.zip_cons_cons]

lemma twFold_seg {h : ℕ} (a x F : ℕ) (hF : F < 2 ^ (h + 1)) :
    ((twSeg A a h).zip (binBits a x)).foldl (twStep h) ([], F) =
      ([], (F + twTerm a h x) % 2 ^ (h + 1)) := by
  unfold twTerm
  by_cases hh : h < a
  · rw [tw_seg_split hh, List.foldl_append, twFold_low, List.foldl_cons, twFold_skip, ite_eq_left hh]
    simp only [twStep, ite_eq_left rfl, List.append_nil, List.reverse_reverse, twVal_binBits]
    rw [tw_testBit_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ h) with hb | hb
    · simp [hb, Nat.mod_eq_of_lt hF]
    · simp [hb]
  · rw [twSeg, ite_eq_right hh, twFold_skip, ite_eq_right hh, Nat.add_zero, Nat.mod_eq_of_lt hF]

lemma twGood_seg {h : ℕ} (a x F : ℕ) (hF : F < 2 ^ (h + 1)) :
    twGood h ((twSeg A a h).zip (binBits a x)) ([], F) := by
  by_cases hh : h < a
  · rw [tw_seg_split hh, ← List.singleton_append, ← List.append_assoc]
    refine twGood_append (twGood_append (twGood_low _ _) ?_) (twGood_skip _ _ _)
    rw [twFold_low]
    intro j hj _
    simp only [List.length_singleton] at hj
    obtain rfl : j = 0 := by omega
    simp [twSt, hF]
  · rw [twSeg, ite_eq_right hh]
    exact twGood_skip _ _ _

/-- The unreduced sum of the scan: `Σ_{i : h < aᵢ} bitₕ(xᵢ) (xᵢ mod 2^h)`, axis `0` last. -/
def twF (h : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | e :: es, n => twF h es n + twTerm e h (n / 2 ^ es.sum)

lemma tw_binBits_sum (e : ℕ) (es : List ℕ) (n : ℕ) :
    binBits (e :: es).sum n = binBits es.sum n ++ binBits e (n / 2 ^ es.sum) := by
  rw [List.sum_cons, Nat.add_comm, tw_binBits_append]

/-- **The scan over the whole address.** -/
theorem twFold_roles (h : ℕ) : ∀ (es : List ℕ) (n F : ℕ), F < 2 ^ (h + 1) →
    ((twRoles A es h).zip (binBits es.sum n)).foldl (twStep h) ([], F) =
      ([], (F + twF h es n) % 2 ^ (h + 1))
  | [], n, F, hF => by simp [twRoles, twF, Nat.mod_eq_of_lt hF]
  | e :: es, n, F, hF => by
      rw [twRoles, tw_binBits_sum, List.zip_append (by rw [twRoles_length, length_binBits]),
        List.foldl_append, twFold_roles h es n F hF,
        twFold_seg e _ _ (Nat.mod_lt _ (by positivity)), twF, Nat.mod_add_mod, Nat.add_assoc]

theorem twGood_roles (h : ℕ) : ∀ (es : List ℕ) (n F : ℕ), F < 2 ^ (h + 1) →
    twGood h ((twRoles A es h).zip (binBits es.sum n)) ([], F)
  | [], n, F, hF => by intro j hj; simp at hj
  | e :: es, n, F, hF => by
      rw [twRoles, tw_binBits_sum, List.zip_append (by rw [twRoles_length, length_binBits])]
      refine twGood_append (twGood_roles h es n F hF) ?_
      rw [twFold_roles h es n F hF]
      exact twGood_seg e _ _ (Nat.mod_lt _ (by positivity))

/-! ### The sum and the twiddle exponent -/

lemma tw_ax_cons (e : ℕ) (es : List ℕ) (i : ℕ) : ax (e :: es) (i + 1) = ax es i := by
  simp [ax]

lemma tw_off_cons (e : ℕ) (es : List ℕ) (i : ℕ) : off (e :: es) (i + 1) = off es i := by
  simp [off]

lemma tw_dg_cons (e : ℕ) (es : List ℕ) (i n : ℕ) : dg (e :: es) (i + 1) n = dg es i n := by
  rw [dg_eq, dg_eq, tw_ax_cons, tw_off_cons]

lemma tw_dg_zero (e : ℕ) (es : List ℕ) (n : ℕ) : dg (e :: es) 0 n = n / 2 ^ es.sum % 2 ^ e := by
  rw [dg_eq]; simp [off, ax]

lemma twTerm_mod {a h : ℕ} (x : ℕ) : twTerm a h (x % 2 ^ a) = twTerm a h x := by
  unfold twTerm
  split_ifs with hh
  · congr 1
    · have e : 2 ^ a = 2 ^ h * 2 ^ (a - h) := by rw [← pow_add]; congr 1; omega
      rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (by
        obtain ⟨k, hk⟩ : ∃ k, a - h = k + 1 := ⟨a - h - 1, by omega⟩
        rw [hk, pow_succ]; exact dvd_mul_left 2 _)]
    · exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hh.le)
  · rfl

/-- `twF` is the sum over the participating axes. -/
theorem twF_eq_sum (h : ℕ) : ∀ (es : List ℕ) (n : ℕ),
    twF h es n = ((parts es h).map fun i => dg es i n / 2 ^ h % 2 * (dg es i n % 2 ^ h)).sum
  | [], n => by simp [twF, parts]
  | e :: es, n => by
      have hp : parts (e :: es) h =
          (if h < e then [0] else []) ++ (parts es h).map (· + 1) := by
        unfold parts
        rw [List.length_cons, List.range_succ_eq_map, List.filter_cons]
        simp only [List.filter_map, Function.comp_def]
        simp only [ax, List.getD_cons_zero, List.getD_cons_succ]
        by_cases hhe : h < e <;> simp [hhe]
      rw [twF, twF_eq_sum h es n, hp, List.map_append, List.sum_append, List.map_map]
      have h2 : ((parts es h).map ((fun i => dg (e :: es) i n / 2 ^ h % 2 *
          (dg (e :: es) i n % 2 ^ h)) ∘ (· + 1))) =
          (parts es h).map fun i => dg es i n / 2 ^ h % 2 * (dg es i n % 2 ^ h) := by
        apply List.map_congr_left
        intro i _
        simp only [Function.comp, tw_dg_cons]
      rw [h2, Nat.add_comm]
      congr 1
      rw [← twTerm_mod, ← tw_dg_zero]
      unfold twTerm
      split_ifs <;> simp

/-- **The exponent modulo `2r`.** For `r = 2^ℓ` and `h ≤ ℓ`, the twiddle exponent of round `h`
modulo `2r` is `2^(ℓ-h)` times the scan sum modulo `2^(h+1)`. -/
theorem twE_mod {ℓ h : ℕ} (hh : h ≤ ℓ) (es : List ℕ) (n : ℕ) :
    twE es (2 ^ ℓ) h (parts es h) n % (2 * 2 ^ ℓ) =
      2 ^ (ℓ - h) * (twF h es n % 2 ^ (h + 1)) := by
  have hc : 2 * 2 ^ ℓ / 2 ^ (h + 1) = 2 ^ (ℓ - h) := by
    rw [show 2 * 2 ^ ℓ = 2 ^ (ℓ - h) * 2 ^ (h + 1) by
      rw [← pow_succ', ← pow_add]; congr 1; omega]
    exact Nat.mul_div_cancel _ (by positivity)
  have hE : twE es (2 ^ ℓ) h (parts es h) n = 2 ^ (ℓ - h) * twF h es n := by
    rw [twF_eq_sum, twE, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [twA, hc]; ring
  rw [hE, show 2 * 2 ^ ℓ = 2 ^ (ℓ - h) * 2 ^ (h + 1) by
    rw [← pow_succ', ← pow_add]; congr 1; omega, Nat.mul_mod_mul_left]

/-- The negated exponent: `(2r - E mod 2r) mod 2r = 2^(ℓ-h) ((2^(h+1) - F') mod 2^(h+1))` with
`F' = F mod 2^(h+1)`. -/
theorem twE_neg_mod {ℓ h : ℕ} (hh : h ≤ ℓ) (es : List ℕ) (n : ℕ) :
    (2 * 2 ^ ℓ - twE es (2 ^ ℓ) h (parts es h) n % (2 * 2 ^ ℓ)) % (2 * 2 ^ ℓ) =
      2 ^ (ℓ - h) * ((0 + 2 ^ (h + 1) - twF h es n % 2 ^ (h + 1)) % 2 ^ (h + 1)) := by
  have h2 : 2 * 2 ^ ℓ = 2 ^ (ℓ - h) * 2 ^ (h + 1) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [twE_mod hh, h2, ← Nat.mul_sub, Nat.mul_mod_mul_left, Nat.zero_add]

end Scan

end IntegerMultBounds.MathlibTM2.Fast
