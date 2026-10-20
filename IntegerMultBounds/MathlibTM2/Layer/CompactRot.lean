module

public import IntegerMultBounds.MathlibTM2.Layer.CompactGadget

/-!
# Rotating one digit of a record index

`rotIdx len f neg off i` rotates digit `f` of the index `i` by `± off i` modulo `2 ^ len f`
(`rotv`). When the offset reads only the bits above the field (`OffHigh`), the rotation is a
class move in the sense of `IntegerMultBounds.MathlibTM2.Host.classMove`: the input class of an
index is whether its rotation wraps around (`wrapIn`), the output class of an index is the input
class of its preimage (`wrapOut`), they match (`wrapOut_rotIdx`), and within one input class the
rotation keeps the rank order (`rotIdx_lt`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactGadget

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Host

/-- The input class of a value `c` under the rotation by `± off` modulo `2 ^ W`: it wraps. -/
def wrapIn (W : ℕ) (neg : Bool) (off c : ℕ) : Bool :=
  if neg then decide (c < off) else decide (2 ^ W ≤ c + off)

/-- The output class of a value `c'`: its preimage wraps. -/
def wrapOut (W : ℕ) (neg : Bool) (off c' : ℕ) : Bool :=
  if neg then decide (2 ^ W ≤ c' + off) else decide (c' < off)

/-- The shift of a rotation by `± off` on a value of wrap class `w`. -/
def rotShift (W : ℕ) (neg : Bool) (off : ℕ) (w : Bool) : ℤ :=
  (if neg then -(off : ℤ) else off) + (if w then (if neg then 2 ^ W else -2 ^ W) else 0)

/-- A rotation adds the shift of its wrap class. -/
lemma rotv_eq_shift (W : ℕ) (neg : Bool) {off c : ℕ} (ho : off < 2 ^ W) (hc : c < 2 ^ W) :
    (rotv W neg off c : ℤ) = c + rotShift W neg off (wrapIn W neg off c) := by
  have h0 : 0 < 2 ^ W := by positivity
  unfold rotv rotShift wrapIn
  cases neg
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hw : 2 ^ W ≤ c + off
    · simp only [hw, decide_true, ite_true]
      rw [Nat.mod_eq_sub_mod hw, Nat.mod_eq_of_lt (by omega)]
      push_cast [hw]
      ring
    · simp only [hw, decide_false, Bool.false_eq_true, ite_false]
      rw [Nat.mod_eq_of_lt (by omega)]
      push_cast
      ring
  · simp only [ite_true, Nat.mod_eq_of_lt ho]
    by_cases hw : c < off
    · simp only [hw, decide_true, ite_true]
      rw [Nat.mod_eq_of_lt (by omega)]
      push_cast [show off ≤ 2 ^ W by omega]
      ring
    · simp only [hw, decide_false, Bool.false_eq_true, ite_false]
      rw [show c + (2 ^ W - off) = c - off + 2 ^ W by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      push_cast [show off ≤ c by omega]
      ring

/-- The output class of a rotated value is the input class of the value. -/
lemma wrapOut_rotv (W : ℕ) (neg : Bool) {off c : ℕ} (ho : off < 2 ^ W) (hc : c < 2 ^ W) :
    wrapOut W neg off (rotv W neg off c) = wrapIn W neg off c := by
  have h := rotv_eq_shift W neg ho hc
  have hr := rotv_lt W neg off c
  generalize rotv W neg off c = r at h hr ⊢
  have hP : ((2 : ℤ) ^ W) = ((2 ^ W : ℕ) : ℤ) := by push_cast; rfl
  cases neg <;> cases hw : wrapIn W _ off c <;>
    simp only [wrapIn, Bool.false_eq_true, ite_false, ite_true, decide_eq_true_eq,
      decide_eq_false_iff_not] at hw <;>
    simp only [rotShift, Bool.false_eq_true, ite_false, ite_true, wrapOut, decide_eq_true_eq,
      decide_eq_false_iff_not, hP] at h ⊢ <;> omega

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- Rotate digit `f` of `i` by `± off i`. -/
def rotIdx (f : Fin nf) (neg : Bool) (off : ℕ → ℕ) (i : ℕ) : ℕ :=
  setDigit len f (rotv (len f) neg (off i) (digit len f i)) i

/-- The offset reads only the bits above field `f`. -/
def OffHigh (f : Fin nf) (off : ℕ → ℕ) : Prop :=
  ∀ i j, i / 2 ^ (fieldOff len f + len f) = j / 2 ^ (fieldOff len f + len f) → off i = off j

variable {len}

lemma digit_lt' (f : Fin nf) (i : ℕ) : digit len f i < 2 ^ len f := Nat.mod_lt _ (by positivity)

lemma rotIdx_div {f : Fin nf} (neg : Bool) (off : ℕ → ℕ) (i : ℕ) :
    rotIdx len f neg off i / 2 ^ (fieldOff len f + len f) = i / 2 ^ (fieldOff len f + len f) :=
  setDigit_div len f _ i

lemma rotIdx_mod {f : Fin nf} (neg : Bool) (off : ℕ → ℕ) (i : ℕ) :
    rotIdx len f neg off i % 2 ^ fieldOff len f = i % 2 ^ fieldOff len f :=
  setDigit_mod len f _ i

lemma digit_rotIdx {f : Fin nf} (neg : Bool) (off : ℕ → ℕ) (i : ℕ) :
    digit len f (rotIdx len f neg off i) = rotv (len f) neg (off i) (digit len f i) := by
  rw [rotIdx, digit_setDigit_self, Nat.mod_eq_of_lt (rotv_lt _ _ _ _)]

/-- **Code match.** -/
theorem wrapOut_rotIdx {f : Fin nf} (neg : Bool) {off : ℕ → ℕ} (hoff : OffHigh len f off)
    (hlt : ∀ i, off i < 2 ^ len f) (i : ℕ) :
    wrapOut (len f) neg (off (rotIdx len f neg off i)) (digit len f (rotIdx len f neg off i)) =
      wrapIn (len f) neg (off i) (digit len f i) := by
  rw [hoff _ i (rotIdx_div neg off i), digit_rotIdx]
  exact wrapOut_rotv _ neg (hlt i) (digit_lt' f i)

/-- An index from its low part, digit `f` and high part. -/
private lemma idx_decomp (f : Fin nf) (i : ℕ) :
    i = i % 2 ^ fieldOff len f + digit len f i * 2 ^ fieldOff len f +
      i / 2 ^ (fieldOff len f + len f) * 2 ^ (fieldOff len f + len f) :=
  window_decomp _ _ i

/-- The order of indices with low part `a < 2 ^ p`, digit `d < 2 ^ W` and high part `h`. -/
private lemma lex3_lt {p W a a' d d' h h' : ℕ} (ha : a < 2 ^ p) (ha' : a' < 2 ^ p)
    (hd : d < 2 ^ W) (hd' : d' < 2 ^ W) :
    a + d * 2 ^ p + h * 2 ^ (p + W) < a' + d' * 2 ^ p + h' * 2 ^ (p + W) ↔
      h < h' ∨ (h = h' ∧ (d < d' ∨ (d = d' ∧ a < a'))) := by
  have hpw : (2 : ℕ) ^ (p + W) = 2 ^ p * 2 ^ W := Nat.pow_add 2 p W
  have hlow : ∀ x y, x < 2 ^ p → y < 2 ^ W → x + y * 2 ^ p < 2 ^ (p + W) := by
    intro x y hx hy
    rw [hpw]
    have : (y + 1) * 2 ^ p ≤ 2 ^ W * 2 ^ p := Nat.mul_le_mul_right _ hy
    nlinarith
  have l1 := hlow a d ha hd
  have l2 := hlow a' d' ha' hd'
  constructor
  · intro hlt
    rcases lt_trichotomy h h' with hh | rfl | hh
    · exact Or.inl hh
    · right; refine ⟨rfl, ?_⟩
      rcases lt_trichotomy d d' with hd₁ | rfl | hd₁
      · exact Or.inl hd₁
      · right; exact ⟨rfl, by omega⟩
      · exfalso
        have : (d' + 1) * 2 ^ p ≤ d * 2 ^ p := Nat.mul_le_mul_right _ hd₁
        nlinarith
    · exfalso
      have : (h' + 1) * 2 ^ (p + W) ≤ h * 2 ^ (p + W) := Nat.mul_le_mul_right _ hh
      nlinarith
  · rintro (hh | ⟨rfl, hd₁ | ⟨rfl, ha₁⟩⟩)
    · have : (h + 1) * 2 ^ (p + W) ≤ h' * 2 ^ (p + W) := Nat.mul_le_mul_right _ hh
      nlinarith
    · have : (d + 1) * 2 ^ p ≤ d' * 2 ^ p := Nat.mul_le_mul_right _ hd₁
      nlinarith
    · omega

/-- **Order match.** Within one input class the rotation keeps the rank order. -/
theorem rotIdx_lt {f : Fin nf} (neg : Bool) {off : ℕ → ℕ} (hoff : OffHigh len f off)
    (hlt : ∀ i, off i < 2 ^ len f) {i j : ℕ} (hij : i < j)
    (hw : wrapIn (len f) neg (off i) (digit len f i) = wrapIn (len f) neg (off j) (digit len f j)) :
    rotIdx len f neg off i < rotIdx len f neg off j := by
  have hi := idx_decomp (len := len) f i
  have hj := idx_decomp (len := len) f j
  have hri := idx_decomp (len := len) f (rotIdx len f neg off i)
  have hrj := idx_decomp (len := len) f (rotIdx len f neg off j)
  rw [rotIdx_div, rotIdx_mod, digit_rotIdx] at hri hrj
  have hli := Nat.mod_lt i (show 0 < 2 ^ fieldOff len f by positivity)
  have hlj := Nat.mod_lt j (show 0 < 2 ^ fieldOff len f by positivity)
  have hdi := digit_lt' (len := len) f i
  have hdj := digit_lt' (len := len) f j
  have hri' := rotv_lt (len f) neg (off i) (digit len f i)
  have hrj' := rotv_lt (len f) neg (off j) (digit len f j)
  rw [hi, hj, lex3_lt hli hlj hdi hdj] at hij
  rw [hri, hrj, lex3_lt hli hlj hri' hrj']
  rcases hij with hh | ⟨hh, hd⟩
  · exact Or.inl hh
  · right
    refine ⟨hh, ?_⟩
    have ho : off i = off j := hoff i j hh
    rw [← ho] at hw ⊢
    have hsh := rotv_eq_shift (len f) neg (hlt i) hdi
    have hsh' := rotv_eq_shift (len f) neg (hlt i) hdj
    rw [← hw] at hsh'
    rcases hd with hd | ⟨hd, ha⟩
    · left
      have : ((rotv (len f) neg (off i) (digit len f i) : ℕ) : ℤ) <
          ((rotv (len f) neg (off i) (digit len f j) : ℕ) : ℤ) := by
        rw [hsh, hsh']
        have : ((digit len f i : ℕ) : ℤ) < ((digit len f j : ℕ) : ℤ) := by exact_mod_cast hd
        linarith
      exact_mod_cast this
    · right
      exact ⟨by rw [hd], ha⟩

/-! ### The rotation as a permutation -/

/-- Rotating back undoes a rotation. -/
theorem rotIdx_rotIdx {f : Fin nf} (neg : Bool) {off : ℕ → ℕ} (hoff : OffHigh len f off)
    (i : ℕ) : rotIdx len f (!neg) off (rotIdx len f neg off i) = i := by
  have h1 := hoff _ i (rotIdx_div neg off i)
  have h2 := digit_rotIdx (len := len) (f := f) neg off i
  conv_lhs => rw [rotIdx]
  rw [h1, h2, rotv_rotv neg _ (digit_lt' f i), rotIdx, setDigit_setDigit_self,
    setDigit_digit]

lemma rotIdx_div_of_le {f : Fin nf} (neg : Bool) (off : ℕ → ℕ) {q : ℕ}
    (hq : fieldOff len f + len f ≤ q) (i : ℕ) : rotIdx len f neg off i / 2 ^ q = i / 2 ^ q :=
  setDigit_div_of_le len f hq _ i

lemma rotIdx_lt_mul {f : Fin nf} (neg : Bool) (off : ℕ → ℕ) {q R : ℕ}
    (hq : fieldOff len f + len f ≤ q) {i : ℕ} (hi : i < R * 2 ^ q) :
    rotIdx len f neg off i < R * 2 ^ q := by
  have h := rotIdx_div_of_le neg off hq i
  have hpos : 0 < 2 ^ q := by positivity
  have h1 : i / 2 ^ q < R := (Nat.div_lt_iff_lt_mul hpos).2 hi
  rw [← h] at h1
  exact (Nat.div_lt_iff_lt_mul hpos).1 h1

/-- The rotation as a permutation of the ranks below `R 2^q`. -/
def rotPerm {f : Fin nf} (neg : Bool) {off : ℕ → ℕ} (hoff : OffHigh len f off) {q R : ℕ}
    (hq : fieldOff len f + len f ≤ q) : Equiv.Perm (Fin (R * 2 ^ q)) where
  toFun i := ⟨rotIdx len f neg off i, rotIdx_lt_mul neg off hq i.isLt⟩
  invFun i := ⟨rotIdx len f (!neg) off i, rotIdx_lt_mul (!neg) off hq i.isLt⟩
  left_inv i := Fin.ext (rotIdx_rotIdx neg hoff i)
  right_inv i := Fin.ext (by
    have := rotIdx_rotIdx (!neg) hoff (i : ℕ)
    rwa [Bool.not_not] at this)

/-- An offset reading only digits of fields above `f` reads only the bits above `f`. -/
theorem offHigh_of_digits {f : Fin nf} {off : ℕ → ℕ} (G : Finset (Fin nf))
    (hG : ∀ g ∈ G, f < g) (hoff : ∀ i j, (∀ g ∈ G, digit len g i = digit len g j) → off i = off j) :
    OffHigh len f off := by
  intro i j hij
  apply hoff
  intro g hg
  have hle := CompactDigits.fieldOff_add_le_of_lt len (hG g hg)
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  rw [digit_eq_window, digit_eq_window, window, window, he, Nat.pow_add,
    ← Nat.div_div_eq_div_mul i, ← Nat.div_div_eq_div_mul j, hij]

end IntegerMultBounds.MathlibTM2.Layer.CompactGadget
