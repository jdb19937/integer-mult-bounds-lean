module

public import IntegerMultBounds.Spec.SyntheticTransformFacts

/-!
# Transform rounds: addresses, butterflies, twiddles

Shared definitions for the iterative form of the synthetic transforms `fwdT` and `oppT`
(`IntegerMultBounds.MathlibTM2.Mult.Rounds`). Axis `i` has length `2^(aᵢ)` with `aᵢ = ax es i` read from the exponent
list `es`, and `tsOf es` is the vendored axis list. Coordinate `i` of an address `n`,
`dg es i n = digit (tsOf es) i n`, occupies bits `off es i, …, off es i + aᵢ - 1` of `n`, where
`off es i` counts the bits of the later axes (`dg_eq`, `testBit_dg`). Flipping bit `off es i + h`
of `n` flips bit `h` of coordinate `i` and leaves the other coordinates unchanged (`dg_xor_self`,
`dg_xor_ne`).

* `bfly q`: the normalized butterfly `H₀(u, v) = ((u + v)/2, (u - v)/2)` on bit `q` of the
  address, in the convention of `IntegerMultBounds.MathlibTM2.Layer.hBit`; `bflyL l`: butterflies on the bits `l`.
* `mulY e`, `mulYInv e`: multiplication of the record at `n` by `y^(e n)`, `y^(-e n)` modulo
  `y^r + 1`. A twiddle whose exponent is invariant under flipping bit `q` commutes with `bfly q`
  (`mulY_bfly`).
* `twA es r h i n = (2r/2^(h+1)) · bitₕ(xᵢ) · (xᵢ mod 2^h)` with `xᵢ = dg es i n`; `twE` sums it
  over a list of axes. `parts es h` lists the axes with `h < aᵢ`, and `selBits es h` their bit
  `h` as positions of the address.
* `fwdRound es h`: `bflyL (selBits es h)`, then `mulYInv (twE es r h (parts es h))`.
  `oppRound es h`: `mulY (twE es r h (parts es h))`, then `bflyL (selBits es h)`.
  `fwdRounds es k` runs the forward rounds at `h = k - 1, …, 0`; `oppRounds es k` the opposite
  rounds at `h = 0, …, k - 1`.
* Locality: the rounds read only addresses below `2^(Σ aᵢ)` (`fwdRounds_eqBelow`,
  `oppRounds_eqBelow`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.Rounds

open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct

/-! ### Bits of one coordinate -/

theorem bit_eq_toNat (x h : ℕ) : x / 2 ^ h % 2 = (x.testBit h).toNat := (Nat.toNat_testBit x h).symm

theorem xor_two_pow_mod (x h : ℕ) : (x ^^^ 2 ^ h) % 2 ^ h = x % 2 ^ h := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hj : j < h
  · simp [hj, show h ≠ j by omega]
  · simp [hj]

theorem xor_two_pow_div_succ (x h : ℕ) : (x ^^^ 2 ^ h) / 2 ^ (h + 1) = x / 2 ^ (h + 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
  simp [show h ≠ j + (h + 1) by omega]

theorem xor_two_pow_bit (x h : ℕ) : (x ^^^ 2 ^ h) / 2 ^ h % 2 = 1 - x / 2 ^ h % 2 := by
  rw [bit_eq_toNat, bit_eq_toNat, Nat.testBit_xor, Nat.testBit_two_pow]
  cases x.testBit h <;> simp

theorem bit_le_one (x h : ℕ) : x / 2 ^ h % 2 ≤ 1 := by
  have := Nat.mod_lt (x / 2 ^ h) (show 0 < 2 by norm_num); omega

/-- `x mod 2^(h+1)` determines and is determined by `x mod 2^h` and bit `h`. -/
theorem mod_succ_eq_iff (x y h : ℕ) :
    x % 2 ^ (h + 1) = y % 2 ^ (h + 1) ↔ x % 2 ^ h = y % 2 ^ h ∧ x / 2 ^ h % 2 = y / 2 ^ h % 2 := by
  constructor
  · intro e
    constructor
    · rw [← Nat.mod_mod_of_dvd x (pow_dvd_pow 2 (Nat.le_succ h)),
        ← Nat.mod_mod_of_dvd y (pow_dvd_pow 2 (Nat.le_succ h)), e]
    · rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self y, ← pow_succ, e]
  · rintro ⟨e1, e2⟩
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ (x := y), e1, e2]

/-- `x / 2^h` determines and is determined by `x / 2^(h+1)` and bit `h`. -/
theorem div_eq_iff_succ (x y h : ℕ) :
    x / 2 ^ h = y / 2 ^ h ↔ x / 2 ^ (h + 1) = y / 2 ^ (h + 1) ∧ x / 2 ^ h % 2 = y / 2 ^ h % 2 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  omega

/-- Bit reversal with the lowest bit split off. -/
theorem bitrev_succ' : ∀ (s j : ℕ), bitrev (s + 1) j = bitrev s (j / 2) + j % 2 * 2 ^ s
  | 0, j => by simp [bitrev_succ, bitrev_zero]
  | s + 1, j => by
    rw [bitrev_succ, bitrev_succ' s j, bitrev_succ s (j / 2), Nat.div_div_eq_div_mul, ← pow_succ']
    ring

/-! ### Mixed-radix addresses with power-of-two axes -/

section Addr

variable (es : List ℕ)

/-- The exponent `aᵢ` of axis `i` (zero past the last axis). -/
def ax (i : ℕ) : ℕ := es.getD i 0

/-- The offset of axis `i` in the flattened address: the number of bits of the later axes. -/
def off (i : ℕ) : ℕ := (es.drop (i + 1)).sum

/-- The axis lengths `tᵢ = 2^aᵢ`. -/
def tsOf : List ℕ := es.map (2 ^ ·)

/-- Coordinate `i` of the address `n`. -/
def dg (i n : ℕ) : ℕ := digit (tsOf es) i n

theorem prod_map_two_pow : ∀ l : List ℕ, (l.map (2 ^ ·)).prod = 2 ^ l.sum
  | [] => by simp
  | a :: l => by simp [prod_map_two_pow l, pow_add]

theorem tsOf_prod : (tsOf es).prod = 2 ^ es.sum := prod_map_two_pow es

theorem tsOf_length : (tsOf es).length = es.length := by simp [tsOf]

theorem tsOf_getD (i : ℕ) : (tsOf es).getD i 1 = 2 ^ ax es i := by
  unfold tsOf ax
  have := List.getD_map es 0 (n := i) (2 ^ ·)
  simpa using this

theorem dg_eq (i n : ℕ) : dg es i n = n / 2 ^ off es i % 2 ^ ax es i := by
  unfold dg digit off
  rw [tsOf_getD, tsOf, ← List.map_drop, prod_map_two_pow]

theorem dg_lt (i n : ℕ) : dg es i n < 2 ^ ax es i := by
  rw [dg_eq]; exact Nat.mod_lt _ (by positivity)

theorem testBit_dg (i n w : ℕ) :
    (dg es i n).testBit w = (decide (w < ax es i) && n.testBit (off es i + w)) := by
  rw [dg_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm w]

theorem drop_sum (i : ℕ) : (es.drop i).sum = ax es i + off es i := by
  unfold ax off
  by_cases hi : i < es.length
  · rw [List.drop_eq_getElem_cons hi, List.sum_cons, List.getD_eq_getElem _ _ hi]
  · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega),
      List.getD_eq_default _ _ (by omega)]
    simp

theorem sum_drop_le (l : List ℕ) (i : ℕ) : (l.drop i).sum ≤ l.sum := by
  have := List.sum_take_add_sum_drop l i; omega

theorem off_add_ax_le (i : ℕ) : off es i + ax es i ≤ es.sum := by
  have := drop_sum es i; have := sum_drop_le es i; omega

theorem off_le_of_lt {i j : ℕ} (hij : i < j) : off es j + ax es j ≤ off es i := by
  have h1 := drop_sum es j
  have h3 : off es i = (es.drop (i + 1)).sum := rfl
  rw [h3]
  have : es.drop j = (es.drop (i + 1)).drop (j - (i + 1)) := by
    rw [List.drop_drop]; congr 1; omega
  have h2 := sum_drop_le (es.drop (i + 1)) (j - (i + 1))
  rw [← this] at h2
  omega

theorem lt_length_of_lt_ax {i h : ℕ} (hh : h < ax es i) : i < es.length := by
  by_contra hc
  unfold ax at hh
  rw [List.getD_eq_default _ _ (by omega)] at hh
  omega

theorem ax_mem {i : ℕ} (hi : i < es.length) : ax es i ∈ es := by
  unfold ax; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

/-- Flipping bit `h` of axis `i` in the flattened address flips bit `h` of coordinate `i`. -/
theorem dg_xor_self {i h : ℕ} (hh : h < ax es i) (n : ℕ) :
    dg es i (n ^^^ 2 ^ (off es i + h)) = dg es i n ^^^ 2 ^ h := by
  apply Nat.eq_of_testBit_eq
  intro w
  rw [testBit_dg, Nat.testBit_xor, Nat.testBit_xor, testBit_dg, Nat.testBit_two_pow,
    Nat.testBit_two_pow]
  by_cases hw : w < ax es i
  · by_cases hwh : h = w
    · subst hwh; simp [hw]
    · simp [hw, hwh]
  · simp [hw, show h ≠ w by omega]

/-- Flipping a bit of axis `i` leaves every other coordinate unchanged. -/
theorem dg_xor_ne {i j h : ℕ} (hh : h < ax es i) (hji : j ≠ i) (n : ℕ) :
    dg es j (n ^^^ 2 ^ (off es i + h)) = dg es j n := by
  apply Nat.eq_of_testBit_eq
  intro w
  rw [testBit_dg, testBit_dg, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hw : w < ax es j
  · have hne : off es i + h ≠ off es j + w := by
      rcases Nat.lt_or_gt_of_ne hji with hlt | hlt
      · have := off_le_of_lt es hlt; omega
      · have := off_le_of_lt es hlt; omega
    simp [hw, hne]
  · simp [hw]

theorem testBit_off (n : ℕ) {i h : ℕ} (hh : h < ax es i) :
    n.testBit (off es i + h) = decide (dg es i n / 2 ^ h % 2 = 1) := by
  have := testBit_dg es i n h
  simp only [hh, decide_true, Bool.true_and] at this
  rw [← this, Nat.testBit_eq_decide_div_mod_eq]

theorem sum_range_getD (l : List ℕ) : ∑ i ∈ Finset.range l.length, ax l i = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ← ih, add_comm]
    simp [ax]

theorem list_sum_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

end Addr

/-! ### Monomials -/

section Shift

variable {r : ℕ} [NeZero r]

theorem shiftInv_eq (e : ℕ) (a : Fin r → ℂ) : shiftInv e a = shiftNegZ ((2 * r - 1) * e) a := by
  unfold shiftInv
  apply shiftNegZ_congr_mod
  rw [← ZMod.natCast_eq_natCast_iff']
  have h1 : 1 ≤ 2 * r := by have := NeZero.pos r; omega
  have hle : e % (2 * r) ≤ 2 * r := (Nat.mod_lt _ (by omega)).le
  have h2r : (2 : ZMod (2 * r)) * (r : ZMod (2 * r)) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 * r)
  push_cast [ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_sub h1]
  linear_combination (1 - (e : ZMod (2 * r))) * h2r

theorem shiftInv_add (e₁ e₂ : ℕ) (a : Fin r → ℂ) :
    shiftInv (e₁ + e₂) a = shiftInv e₁ (shiftInv e₂ a) := by
  rw [shiftInv_eq, shiftInv_eq, shiftInv_eq, shiftNegZ_add, mul_add]

theorem shiftInv_zero (a : Fin r → ℂ) : shiftInv 0 a = a := by
  rw [shiftInv_eq, mul_zero, shiftNegZ_zero]

theorem shiftInv_add_two_r_mul (e q : ℕ) (a : Fin r → ℂ) :
    shiftInv (e + 2 * r * q) a = shiftInv e a := by
  rw [shiftInv_eq, shiftInv_eq,
    show (2 * r - 1) * (e + 2 * r * q) = (2 * r - 1) * e + 2 * r * ((2 * r - 1) * q) by ring,
    shiftNegZ_add_two_r_mul]

theorem shiftInv_r (a : Fin r → ℂ) : shiftInv r a = -a := by
  have hr := NeZero.pos r
  rw [shiftInv_eq, show (2 * r - 1) * r = r + 2 * r * (r - 1) by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show 2 * (s + 1) - 1 = 2 * s + 1 by omega]; ring,
    shiftNegZ_add_two_r_mul, shiftNegZ_r]

theorem shiftInv_smul (e : ℕ) (c : ℂ) (a : Fin r → ℂ) : shiftInv e (c • a) = c • shiftInv e a := by
  rw [shiftInv_eq, shiftInv_eq, shiftNegZ_smul]

theorem shiftInv_add_vec (e : ℕ) (a b : Fin r → ℂ) :
    shiftInv e (a + b) = shiftInv e a + shiftInv e b := by
  rw [shiftInv_eq, shiftInv_eq, shiftInv_eq, shiftNegZ_add_vec]

theorem shiftInv_sum {ι : Type*} (e : ℕ) (s : Finset ι) (f : ι → Fin r → ℂ) :
    shiftInv e (∑ i ∈ s, f i) = ∑ i ∈ s, shiftInv e (f i) := by
  rw [shiftInv_eq, shiftNegZ_sum]
  simp only [shiftInv_eq]

/-- `y^(-b r)` for a bit `b` is the sign `(-1)^b`. -/
theorem shiftInv_bit_r {b : ℕ} (hb : b ≤ 1) (a : Fin r → ℂ) :
    shiftInv (b * r) a = (if b = 1 then (-1 : ℂ) else 1) • a := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · simp [shiftInv_zero]
  · simp [shiftInv_r]

theorem shiftNegZ_bit_r {b : ℕ} (hb : b ≤ 1) (a : Fin r → ℂ) :
    shiftNegZ (b * r) a = (if b = 1 then (-1 : ℂ) else 1) • a := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · simp [shiftNegZ_zero]
  · simp [shiftNegZ_r]

end Shift

/-! ### Butterflies and monomials on arrays -/

/-- Arrays of polynomial records of `ℛ_r`, indexed by the flattened address. -/
abbrev Recs (r : ℕ) := ℕ → Fin r → ℂ

section Arrays

variable {r : ℕ}

/-- The normalized butterfly `H₀` on bit `q` of the flattened address, in the convention of
`IntegerMultBounds.MathlibTM2.Layer.hBit`: with `n' = n xor 2^q`, the record at `n` becomes `(u n + u n')/2` if bit `q`
of `n` is clear and `(u n' - u n)/2` if it is set. -/
noncomputable def bfly (q : ℕ) (u : Recs r) : Recs r :=
  fun n => (1 / 2 : ℂ) • ((if n.testBit q then (-1 : ℂ) else 1) • u n + u (n ^^^ 2 ^ q))

/-- Butterflies on the bits `l`, the head applied last (the order of `IntegerMultBounds.MathlibTM2.Layer.Hl`). -/
noncomputable def bflyL (l : List ℕ) (u : Recs r) : Recs r := l.foldr bfly u

variable [NeZero r]

/-- Multiplication of the record at address `n` by `y^(e n)`. -/
noncomputable def mulY (e : ℕ → ℕ) (u : Recs r) : Recs r := fun n => shiftNegZ (e n) (u n)

/-- Multiplication of the record at address `n` by `y^(-e n)`. -/
noncomputable def mulYInv (e : ℕ → ℕ) (u : Recs r) : Recs r := fun n => shiftInv (e n) (u n)

theorem mulYInv_eq (e : ℕ → ℕ) (u : Recs r) :
    mulYInv e u = mulY (fun n => (2 * r - 1) * e n) u := by
  funext n; exact shiftInv_eq _ _

theorem mulY_bfly {e : ℕ → ℕ} {q : ℕ} (he : ∀ n, e (n ^^^ 2 ^ q) = e n) (u : Recs r) :
    mulY e (bfly q u) = bfly q (mulY e u) := by
  funext n
  simp only [mulY, bfly, shiftNegZ_smul, shiftNegZ_add_vec, he]

theorem mulYInv_bfly {e : ℕ → ℕ} {q : ℕ} (he : ∀ n, e (n ^^^ 2 ^ q) = e n) (u : Recs r) :
    mulYInv e (bfly q u) = bfly q (mulYInv e u) := by
  rw [mulYInv_eq, mulYInv_eq, mulY_bfly (fun n => by simp only [he])]

theorem mulY_bflyL {e : ℕ → ℕ} {l : List ℕ} (he : ∀ q ∈ l, ∀ n, e (n ^^^ 2 ^ q) = e n)
    (u : Recs r) : mulY e (bflyL l u) = bflyL l (mulY e u) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    show mulY e (bfly q (bflyL l u)) = bfly q (bflyL l (mulY e u))
    rw [mulY_bfly (he q (by simp)), ih (fun q' hq' => he q' (by simp [hq']))]

end Arrays

/-! ### Rounds -/

section Rounds

variable (es : List ℕ)

/-- The twiddle exponent of axis `i` at named position `h` and address `n`:
`(2r/2^(h+1)) · bitₕ(xᵢ) · (xᵢ mod 2^h)` with `xᵢ` coordinate `i` of `n`. -/
def twA (r h i n : ℕ) : ℕ := 2 * r / 2 ^ (h + 1) * (dg es i n / 2 ^ h % 2) * (dg es i n % 2 ^ h)

/-- The combined twiddle exponent of the axes `l` at named position `h` and address `n`. -/
def twE (r h : ℕ) (l : List ℕ) (n : ℕ) : ℕ := (l.map fun i => twA es r h i n).sum

/-- The axes participating in the round at named position `h`: those with `h < aᵢ`. -/
def parts (h : ℕ) : List ℕ := (List.range es.length).filter fun i => h < ax es i

/-- The selected bits of the round at named position `h`: bit `h` of every participating axis,
as a position in the flattened address. -/
def selBits (h : ℕ) : List ℕ := (parts es h).map fun i => off es i + h

/-- The forward round at named position `h`: the butterflies on the selected bits, then the
recordwise monomial `y^(-E_h)`. -/
noncomputable def fwdRound {r : ℕ} [NeZero r] (h : ℕ) (u : Recs r) : Recs r :=
  mulYInv (twE es r h (parts es h)) (bflyL (selBits es h) u)

/-- The opposite round at named position `h`: the recordwise monomial `y^(E_h)`, then the
butterflies on the selected bits. -/
noncomputable def oppRound {r : ℕ} [NeZero r] (h : ℕ) (u : Recs r) : Recs r :=
  bflyL (selBits es h) (mulY (twE es r h (parts es h)) u)

/-- The forward rounds at named positions `h = k - 1, …, 0`, in this order. -/
noncomputable def fwdRounds {r : ℕ} [NeZero r] : ℕ → Recs r → Recs r
  | 0, u => u
  | k + 1, u => fwdRounds k (fwdRound es k u)

/-- The opposite rounds at named positions `h = 0, …, k - 1`, in this order. -/
noncomputable def oppRounds {r : ℕ} [NeZero r] : ℕ → Recs r → Recs r
  | 0, u => u
  | k + 1, u => oppRound es k (oppRounds k u)

theorem mem_parts {h i : ℕ} : i ∈ parts es h ↔ i < es.length ∧ h < ax es i := by
  simp [parts]

theorem parts_nodup (h : ℕ) : (parts es h).Nodup := List.nodup_range.filter _

theorem twA_xor_ne {r h h' i j : ℕ} (hh' : h' < ax es j) (hij : i ≠ j) (n : ℕ) :
    twA es r h i (n ^^^ 2 ^ (off es j + h')) = twA es r h i n := by
  unfold twA; rw [dg_xor_ne es hh' hij]

theorem twE_xor_ne {r h h' j : ℕ} {l : List ℕ} (hh' : h' < ax es j) (hj : j ∉ l) (n : ℕ) :
    twE es r h l (n ^^^ 2 ^ (off es j + h')) = twE es r h l n := by
  unfold twE
  congr 1
  apply List.map_congr_left
  intro i hi
  exact twA_xor_ne es hh' (fun e => hj (e ▸ hi)) n

end Rounds

/-! ### Sum manipulations -/

theorem sum_eq_add_of_ne {M : Type*} [AddCommMonoid M] {s : Finset ℕ} {i : ℕ} (hi : i ∈ s)
    {f g : ℕ → M} (hfg : ∀ j ∈ s, j ≠ i → f j = g j) {δ : M} (hδ : f i = g i + δ) :
    ∑ j ∈ s, f j = ∑ j ∈ s, g j + δ := by
  rw [← Finset.add_sum_erase s f hi, ← Finset.add_sum_erase s g hi, hδ,
    Finset.sum_congr rfl fun j hj =>
      hfg j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)]
  abel

theorem sum_filter_split {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (P Q R T : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] [DecidablePred T]
    (h1 : ∀ k, P k ∧ Q k ↔ R k) (h2 : ∀ k, P k ∧ ¬ Q k ↔ T k) (f : ℕ → M) :
    ∑ k ∈ s.filter P, f k = ∑ k ∈ s.filter R, f k + ∑ k ∈ s.filter T, f k := by
  rw [← Finset.sum_filter_add_sum_filter_not (s.filter P) Q, Finset.filter_filter,
    Finset.filter_filter]
  congr 1
  · exact Finset.sum_congr (Finset.filter_congr fun k _ => h1 k) fun _ _ => rfl
  · exact Finset.sum_congr (Finset.filter_congr fun k _ => h2 k) fun _ _ => rfl

/-- The twiddle decomposition `b w k = w b (k mod P) + b bₖ r + 2r (b ⌊k / 2P⌋)`. -/
theorem twiddle_decomp_fwd {b w L bk Q dk r P : ℕ} (e1 : L + P * bk + P * 2 * Q = dk)
    (hw1 : w * (P * 2) = 2 * r) (hw2 : w * P = r) :
    b * w * dk = w * b * L + b * bk * r + 2 * r * (b * Q) := by
  subst e1
  calc b * w * (L + P * bk + P * 2 * Q)
      = w * b * L + b * bk * (w * P) + b * Q * (w * (P * 2)) := by ring
    _ = _ := by rw [hw1, hw2]; ring

/-- The twiddle decomposition of the opposite step:
`w (L + P b)(2R + e) = 2w L R + (w e L + b e r + 2r (b R))` when `w P = r`. -/
theorem twiddle_decomp_opp {w L P b R e r : ℕ} (hw2 : w * P = r) :
    w * (L + P * b) * (2 * R + e) = 2 * w * L * R + (w * e * L + b * e * r + 2 * r * (b * R)) := by
  calc w * (L + P * b) * (2 * R + e) = 2 * w * L * R + w * e * L + b * (2 * R + e) * (w * P) := by
        ring
    _ = _ := by rw [hw2]; ring

theorem powAxes_tsOf {r : ℕ} (es : List ℕ) (hr : ∀ e ∈ es, 2 ^ e ∣ 2 * r) :
    PowAxes r (tsOf es) := by
  intro t ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  exact ⟨e, rfl, hr e he⟩

/-! ### Locality -/

section Local

variable {r : ℕ}

/-- Arrays agreeing on the addresses below `2^N`. -/
def EqBelow (N : ℕ) (u v : Recs r) : Prop := ∀ n < 2 ^ N, u n = v n

theorem bfly_eqBelow {N q : ℕ} (hq : q < N) {u v : Recs r} (h : EqBelow N u v) :
    EqBelow N (bfly q u) (bfly q v) := by
  intro n hn
  have hq' : 2 ^ q < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) hq
  simp only [bfly, h n hn, h _ (Nat.xor_lt_two_pow hn hq')]

theorem bflyL_eqBelow {N : ℕ} {l : List ℕ} (hl : ∀ q ∈ l, q < N) {u v : Recs r}
    (h : EqBelow N u v) : EqBelow N (bflyL l u) (bflyL l v) := by
  induction l with
  | nil => exact h
  | cons q l ih =>
    exact bfly_eqBelow (hl q (by simp)) (ih fun q' hq' => hl q' (by simp [hq']))

theorem selBits_lt (es : List ℕ) {h q : ℕ} (hq : q ∈ selBits es h) : q < es.sum := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  rw [mem_parts] at hi
  have := off_add_ax_le es i
  omega

theorem mulY_eqBelow {N : ℕ} (e : ℕ → ℕ) {u v : Recs r} (h : EqBelow N u v) :
    EqBelow N (mulY e u) (mulY e v) := by
  intro n hn; simp only [mulY, h n hn]

variable [NeZero r]

theorem mulYInv_eqBelow {N : ℕ} (e : ℕ → ℕ) {u v : Recs r} (h : EqBelow N u v) :
    EqBelow N (mulYInv e u) (mulYInv e v) := by
  intro n hn; simp only [mulYInv, h n hn]

theorem fwdRounds_eqBelow (es : List ℕ) {u v : Recs r} (h : EqBelow es.sum u v) :
    ∀ k, EqBelow es.sum (fwdRounds es k u) (fwdRounds es k v)
  | 0 => h
  | k + 1 => by
    have := mulYInv_eqBelow (twE es r k (parts es k))
      (bflyL_eqBelow (l := selBits es k) (fun q hq => selBits_lt es (h := k) hq) h)
    exact fwdRounds_eqBelow es this k

theorem oppRounds_eqBelow (es : List ℕ) {u v : Recs r} (h : EqBelow es.sum u v) :
    ∀ k, EqBelow es.sum (oppRounds es k u) (oppRounds es k v)
  | 0 => h
  | k + 1 =>
    bflyL_eqBelow (l := selBits es k) (fun _ hq => selBits_lt es (h := k) hq)
      (mulY_eqBelow _ (oppRounds_eqBelow es h k))

end Local

end IntegerMultBounds.MathlibTM2.Mult.Rounds
