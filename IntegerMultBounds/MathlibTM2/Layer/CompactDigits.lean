module

public import IntegerMultBounds.MathlibTM2.Host.Index

/-!
# Replacing one digit of a mixed-radix index

`setDigit len f v i` is the index `i` with digit `f` (in the mixed radix with field lengths
`len`, `IntegerMultBounds.MathlibTM2.Host.digit`) replaced by `v` modulo `2 ^ len f`. Every
other digit and every bit above all fields is kept (`digit_setDigit`, `setDigit_div`).

`window p w i = i / 2 ^ p % 2 ^ w` is the `w`-bit window of `i` at bit `p`; `digit` is the
window at the field offset. `window_add_mul` reads a window of a sum whose low part fits below
the window.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactDigits

open IntegerMultBounds.MathlibTM2.Host

/-! ### Bit windows -/

/-- The `w`-bit window of `i` at bit `p`. -/
def window (p w i : ℕ) : ℕ := i / 2 ^ p % 2 ^ w

lemma window_lt (p w i : ℕ) : window p w i < 2 ^ w := Nat.mod_lt _ (by positivity)

/-- The low `p` bits, the window and the high part reassemble the index. -/
lemma window_decomp (p w i : ℕ) :
    i = i % 2 ^ p + window p w i * 2 ^ p + i / 2 ^ (p + w) * 2 ^ (p + w) := by
  have h1 := Nat.mod_add_div i (2 ^ p)
  have h2 := Nat.mod_add_div (i / 2 ^ p) (2 ^ w)
  have h3 : i / 2 ^ p / 2 ^ w = i / 2 ^ (p + w) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  unfold window
  rw [h3] at h2
  calc i = i % 2 ^ p + 2 ^ p * (i / 2 ^ p) := h1.symm
    _ = i % 2 ^ p + 2 ^ p * (i / 2 ^ p % 2 ^ w + 2 ^ w * (i / 2 ^ (p + w))) := by rw [h2]
    _ = _ := by rw [Nat.pow_add]; ring

/-- A window of a sum `c + x * 2 ^ q` with `c < 2 ^ q` and the window above `q`. -/
lemma window_add_mul_high {p w q c x : ℕ} (hc : c < 2 ^ q) (hq : q ≤ p) :
    window p w (c + x * 2 ^ q) = window (p - q) w x := by
  unfold window
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hq
  have h : (c + x * 2 ^ q) / 2 ^ q = x := by
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hc, Nat.zero_add]
  rw [show q + e - q = e by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul, h]

/-- The window of `i` at `p` reads only `i` modulo `2 ^ q` for `p + w ≤ q`. -/
lemma window_mod {p w q : ℕ} (hq : p + w ≤ q) (i : ℕ) :
    window p w (i % 2 ^ q) = window p w i := by
  unfold window
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self i, ← Nat.pow_add,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hq)]

lemma window_add_mul_low {p w q c x : ℕ} (hq : p + w ≤ q) :
    window p w (c + x * 2 ^ q) = window p w c := by
  rw [← window_mod hq, Nat.add_mul_mod_self_right, window_mod hq]

lemma window_mul_pow (p w x : ℕ) : window p w (x * 2 ^ p) = x % 2 ^ w := by
  simp [window]

lemma div_window_split {p w i : ℕ} : i / 2 ^ p / 2 ^ w = i / 2 ^ (p + w) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_add]

/-! ### Field offsets -/

variable {nf : ℕ} (len : Fin nf → ℕ)

lemma digit_eq_window (f : Fin nf) (i : ℕ) :
    digit len f i = window (fieldOff len f) (len f) i := rfl

/-- A lower field ends below a higher one. -/
lemma fieldOff_add_le_of_lt {f g : Fin nf} (h : g < f) :
    fieldOff len g + len g ≤ fieldOff len f := by
  unfold fieldOff
  rw [Nat.add_comm, ← Finset.sum_insert (s := Finset.univ.filter (· < g)) (by simp)]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with rfl | hx
  · exact h
  · exact hx.trans h

/-- The total length of all fields. -/
def fieldsLen : ℕ := ∑ f, len f

lemma fieldOff_add_le_total (f : Fin nf) : fieldOff len f + len f ≤ fieldsLen len :=
  fieldOff_add_le len f

/-! ### Replacing a digit -/

/-- The index `i` with digit `f` replaced by `v % 2 ^ len f`. -/
def setDigit (f : Fin nf) (v i : ℕ) : ℕ :=
  i % 2 ^ fieldOff len f + v % 2 ^ len f * 2 ^ fieldOff len f +
    i / 2 ^ (fieldOff len f + len f) * 2 ^ (fieldOff len f + len f)

private lemma low_lt {p w a b : ℕ} (ha : a < 2 ^ p) (hb : b < 2 ^ w) :
    a + b * 2 ^ p < 2 ^ (p + w) := by
  rw [Nat.pow_add]
  have : (b + 1) * 2 ^ p ≤ 2 ^ w * 2 ^ p := Nat.mul_le_mul_right _ hb
  nlinarith

private lemma setDigit_low (f : Fin nf) (v i : ℕ) :
    i % 2 ^ fieldOff len f + v % 2 ^ len f * 2 ^ fieldOff len f < 2 ^ (fieldOff len f + len f) :=
  low_lt (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))

lemma setDigit_mod (f : Fin nf) (v i : ℕ) :
    setDigit len f v i % 2 ^ fieldOff len f = i % 2 ^ fieldOff len f := by
  unfold setDigit
  rw [show i % 2 ^ fieldOff len f + v % 2 ^ len f * 2 ^ fieldOff len f +
      i / 2 ^ (fieldOff len f + len f) * 2 ^ (fieldOff len f + len f) =
      i % 2 ^ fieldOff len f + (v % 2 ^ len f + i / 2 ^ (fieldOff len f + len f) * 2 ^ len f) *
        2 ^ fieldOff len f by rw [Nat.pow_add]; ring, Nat.add_mul_mod_self_right, Nat.mod_mod]

lemma setDigit_div (f : Fin nf) (v i : ℕ) :
    setDigit len f v i / 2 ^ (fieldOff len f + len f) = i / 2 ^ (fieldOff len f + len f) := by
  unfold setDigit
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (setDigit_low len f v i),
    Nat.zero_add]

lemma digit_setDigit_self (f : Fin nf) (v i : ℕ) :
    digit len f (setDigit len f v i) = v % 2 ^ len f := by
  rw [digit_eq_window, setDigit]
  rw [show i % 2 ^ fieldOff len f + v % 2 ^ len f * 2 ^ fieldOff len f +
      i / 2 ^ (fieldOff len f + len f) * 2 ^ (fieldOff len f + len f) =
      i % 2 ^ fieldOff len f + (v % 2 ^ len f + i / 2 ^ (fieldOff len f + len f) * 2 ^ len f) *
        2 ^ fieldOff len f by rw [Nat.pow_add]; ring]
  rw [window_add_mul_high (Nat.mod_lt _ (by positivity)) le_rfl, Nat.sub_self]
  simp [window, Nat.add_mul_mod_self_right]

lemma digit_setDigit_ne (f g : Fin nf) (hg : g ≠ f) (v i : ℕ) :
    digit len g (setDigit len f v i) = digit len g i := by
  rcases lt_or_gt_of_ne hg with h | h
  · have hle := fieldOff_add_le_of_lt len h
    rw [digit_eq_window, digit_eq_window, ← window_mod hle, setDigit_mod, window_mod hle]
  · have hle := fieldOff_add_le_of_lt len h
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
    rw [digit_eq_window, digit_eq_window, window, window, he, Nat.pow_add,
      ← Nat.div_div_eq_div_mul (setDigit len f v i), ← Nat.div_div_eq_div_mul i, setDigit_div]

lemma digit_setDigit (f g : Fin nf) (v i : ℕ) :
    digit len g (setDigit len f v i) = if g = f then v % 2 ^ len f else digit len g i := by
  split_ifs with h
  · subst h; exact digit_setDigit_self len g v i
  · exact digit_setDigit_ne len f g h v i

lemma setDigit_digit (f : Fin nf) (i : ℕ) : setDigit len f (digit len f i) i = i := by
  unfold setDigit
  have h : digit len f i % 2 ^ len f = digit len f i :=
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by positivity))
  rw [h]
  exact (window_decomp (fieldOff len f) (len f) i).symm

/-- Above all fields nothing changes. -/
lemma setDigit_div_total (f : Fin nf) (v i : ℕ) :
    setDigit len f v i / 2 ^ fieldsLen len = i / 2 ^ fieldsLen len := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (fieldOff_add_le_total len f)
  rw [he, Nat.pow_add, ← Nat.div_div_eq_div_mul (setDigit len f v i),
    ← Nat.div_div_eq_div_mul i, setDigit_div]

/-- Above any bit at or above the end of field `f` nothing changes. -/
lemma setDigit_div_of_le (f : Fin nf) {q : ℕ} (hq : fieldOff len f + len f ≤ q) (v i : ℕ) :
    setDigit len f v i / 2 ^ q = i / 2 ^ q := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul (setDigit len f v i), ← Nat.div_div_eq_div_mul i,
    setDigit_div]

lemma setDigit_setDigit_self (f : Fin nf) (v v' i : ℕ) :
    setDigit len f v' (setDigit len f v i) = setDigit len f v' i := by
  have h1 := setDigit_mod len f v i
  have h2 := setDigit_div len f v i
  simp only [setDigit] at h1 h2 ⊢
  rw [h1, h2]

/-- Two indices with equal digits and equal parts above all fields are equal. -/
lemma eq_of_digit_eq {i j : ℕ} (hd : ∀ f, digit len f i = digit len f j)
    (hhi : i / 2 ^ fieldsLen len = j / 2 ^ fieldsLen len) : i = j := by
  have key : ∀ (k : ℕ) (h : k ≤ nf), i % 2 ^ (∑ f : Fin nf with f.val < k, len f) =
      j % 2 ^ (∑ f : Fin nf with f.val < k, len f) := by
    intro k
    induction k with
    | zero => intro _; simp [Nat.mod_one]
    | succ k ih =>
      intro hk
      have hsplit : (∑ f : Fin nf with f.val < k + 1, len f) =
          (∑ f : Fin nf with f.val < k, len f) + len ⟨k, hk⟩ := by
        have hs : (Finset.univ.filter fun f : Fin nf => f.val < k + 1) =
            insert ⟨k, hk⟩ (Finset.univ.filter fun f : Fin nf => f.val < k) := by
          ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        rw [hs, Finset.sum_insert (by simp), Nat.add_comm]
      have hoff : fieldOff len ⟨k, hk⟩ = ∑ f : Fin nf with f.val < k, len f := by
        unfold fieldOff
        congr 1
      rw [hsplit, Nat.pow_add, Nat.mod_mul, Nat.mod_mul, ih (by omega)]
      congr 2
      have := hd ⟨k, hk⟩
      rw [digit_eq_window, digit_eq_window, window, window, hoff] at this
      exact this
  have hall := key nf le_rfl
  have hs : (∑ f : Fin nf with f.val < nf, len f) = fieldsLen len := by
    unfold fieldsLen
    congr 1
    ext f
    simp
  rw [hs] at hall
  rw [← Nat.mod_add_div i (2 ^ fieldsLen len), ← Nat.mod_add_div j (2 ^ fieldsLen len), hall,
    hhi]

/-- The bits of an index with a replaced digit. -/
lemma testBit_setDigit (f : Fin nf) (v i t : ℕ) :
    (setDigit len f v i).testBit t = if fieldOff len f ≤ t ∧ t < fieldOff len f + len f then
      v.testBit (t - fieldOff len f) else i.testBit t := by
  set o := fieldOff len f
  set l := len f
  have e : setDigit len f v i = 2 ^ o * (2 ^ l * (i / 2 ^ (o + l)) + v % 2 ^ l) + i % 2 ^ o := by
    unfold setDigit; rw [Nat.pow_add]; ring
  rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))]
  by_cases h1 : t < o
  · simp only [h1, ↓reduceIte, Nat.testBit_mod_two_pow, decide_true, Bool.true_and,
      show ¬(o ≤ t ∧ t < o + l) by omega]
  · simp only [h1, ↓reduceIte]
    rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))]
    by_cases h2 : t - o < l
    · simp only [h2, ↓reduceIte, Nat.testBit_mod_two_pow, decide_true, Bool.true_and,
        show o ≤ t ∧ t < o + l by omega, and_self]
    · simp only [h2, ↓reduceIte, Nat.testBit_div_two_pow, show ¬(o ≤ t ∧ t < o + l) by omega]
      congr 1; omega

/-! ### The bits of an index, field by field -/

omit len in
lemma binBits_add (p q x : ℕ) : binBits (p + q) x = binBits p x ++ binBits q (x / 2 ^ p) := by
  unfold binBits
  rw [List.ofFn_add]
  congr 1
  apply List.ofFn_inj.mpr
  funext t
  simp [Nat.testBit_div_two_pow, Nat.add_comm]

omit len in
lemma binBits_mod (L y : ℕ) : binBits L (y % 2 ^ L) = binBits L y := by
  unfold binBits
  apply List.ofFn_inj.mpr
  funext t
  simp [Nat.testBit_mod_two_pow, t.isLt]

/-- **The bits of an index are the bits of its digits**, field `0` first. -/
theorem flatMap_binBits_digit (x : ℕ) :
    (List.finRange nf).flatMap (fun f => binBits (len f) (digit len f x)) =
      binBits (fieldsLen len) x := by
  let S : ℕ → ℕ := fun j => ∑ g : Fin nf, if g.val < j then len g else 0
  have hS : ∀ j (h : j < nf), S (j + 1) = S j + len ⟨j, h⟩ := fun j h => by
    have e : ∀ g : Fin nf, (if g.val < j + 1 then len g else 0) =
        (if g.val < j then len g else 0) + (if g = ⟨j, h⟩ then len g else 0) := fun g => by
      have := Fin.ext_iff (a := g) (b := ⟨j, h⟩)
      split_ifs <;> simp_all <;> omega
    simp only [S, e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hoff : ∀ j (h : j < nf), fieldOff len ⟨j, h⟩ = S j := fun j h => by
    simp only [fieldOff, S, Finset.sum_filter, Fin.lt_def]
  have key : ∀ j ≤ nf, ((List.finRange nf).take j).flatMap
      (fun f => binBits (len f) (digit len f x)) = binBits (S j) x := by
    intro j
    induction j with
    | zero => intro _; simp [S, binBits]
    | succ j ih =>
      intro hj
      rw [List.take_add_one, List.flatMap_append, ih (by omega),
        List.getElem?_eq_getElem (by simpa using hj)]
      simp only [List.getElem_finRange, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [hS j hj, binBits_add, digit, binBits_mod]
      congr 3
      rw [← hoff j (by omega)]
      rfl
  have h := key nf le_rfl
  rw [List.take_of_length_le (by simp)] at h
  rw [h]
  congr 1
  simp [S, fieldsLen]

end IntegerMultBounds.MathlibTM2.Layer.CompactDigits
