module

public import IntegerMultBounds.MathlibTM2.Layer.CompactBad
public import IntegerMultBounds.MathlibTM2.Layer.CompactGadgetIndex

/-!
# The ideal map as an exclusive or

Toggling every used segment of `y` by the selected bit of `x` flips exactly the selected bits of
`y` where `x` has a one: `togY p (par x) y = y ⊕ (x ∧ sel)` with `sel` the mask of the selected
bits (`togY_xor`). On indices the ideal map replaces the digit of `y` by `y ⊕ (x ∧ sel)`
(`idealIdx_xor`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactGadget

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactMasks
  IntegerMultBounds.MathlibTM2.Host Finset

lemma xor_mod_two_pow (a b k : ℕ) : (a ^^^ b) % 2 ^ k = a % 2 ^ k ^^^ b % 2 ^ k :=
  Nat.eq_of_testBit_eq fun t => by
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    cases decide (t < k) <;> simp

lemma xor_div_two_pow (a b k : ℕ) : (a ^^^ b) / 2 ^ k = a / 2 ^ k ^^^ b / 2 ^ k :=
  Nat.eq_of_testBit_eq fun t => by simp only [Nat.testBit_div_two_pow, Nat.testBit_xor]

lemma window_xor (q w a b : ℕ) : window q w (a ^^^ b) = window q w a ^^^ window q w b := by
  rw [window, xor_div_two_pow, xor_mod_two_pow]; rfl

lemma tog_toNat (s : ℕ) (b : Bool) : tog s b.toNat = s ^^^ b.toNat := by
  cases b
  · simp [tog]
  · refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_xor]
    rcases Nat.mod_two_eq_zero_or_one s with h | h
    · cases i with
      | zero => simp [tog, Nat.testBit_zero, h]; omega
      | succ i =>
        simp only [Nat.testBit_succ, Bool.toNat_true]
        rw [show (tog s 1) / 2 = s / 2 by simp [tog, h]; omega]
        simp
    · cases i with
      | zero => simp [tog, Nat.testBit_zero, h]; omega
      | succ i =>
        simp only [Nat.testBit_succ, Bool.toNat_true]
        rw [show (tog s 1) / 2 = s / 2 by simp [tog, h]; omega]
        simp

variable {p : Par}

/-- Segment `c` of the selected bits of `X` is the selected bit itself. -/
lemma seg_and_sel (hK : 0 < p.K) {c : ℕ} (hc : c < p.n) (X : ℕ) :
    seg p.ρ p.K c (X &&& maskVal p.n (posS p)) = (X.testBit (posS p c)).toNat := by
  have hM : ∀ q, (X &&& maskVal p.n (posS p)).testBit q =
      (X.testBit q && decide (∃ c < p.n, posS p c = q)) := fun q => by
    rw [Nat.testBit_and, testBit_maskVal (posS_mono hK)]
  exact
    Nat.eq_of_testBit_eq fun j => by
      rw [seg, window, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hM]
      by_cases hj : j < p.K
      · have hiff : (∃ c' < p.n, posS p c' = j + (p.ρ + c * p.K)) ↔ j = 0 := by
          constructor
          · rintro ⟨c', _, e⟩
            unfold posS at e
            exact (seg_uniq (K := p.K) (a := c') (c := c) (d := 0) (e := j) hK hj
              (by omega)).2.symm
          · rintro rfl; exact ⟨c, hc, by simp [posS]⟩
        simp only [hj, decide_true, Bool.true_and, hiff]
        cases j with
        | zero =>
          rw [show 0 + (p.ρ + c * p.K) = posS p c by simp [posS]]
          cases X.testBit (posS p c) <;> decide
        | succ j =>
          simp only [Nat.add_one_ne_zero, decide_false, Bool.and_false]
          cases X.testBit (posS p c) <;> simp [Nat.testBit_succ]
      · simp only [hj, decide_false, Bool.false_and]
        exact (Nat.testBit_eq_false_of_lt (lt_of_le_of_lt (Bool.toNat_le _)
          (Nat.one_lt_two_pow (by omega)))).symm

/-- **The ideal toggle is an exclusive or** with the selected bits of `x`. -/
theorem togY_xor (hK : 0 < p.K) (X Y : ℕ) :
    togY p (fun c => par p c X) Y = Y ^^^ (X &&& maskVal p.n (posS p)) := by
  set M := X &&& maskVal p.n (posS p) with hMdef
  have hM : ∀ q, M.testBit q = (X.testBit q && decide (∃ c < p.n, posS p c = q)) := fun q => by
    rw [hMdef, Nat.testBit_and, testBit_maskVal (posS_mono hK)]
  have hlow : M % 2 ^ p.ρ = 0 := Nat.eq_of_testBit_eq fun t => by
    rw [Nat.testBit_mod_two_pow, hM]
    by_cases ht : t < p.ρ
    · have : ¬ ∃ c < p.n, posS p c = t := fun ⟨c, _, e⟩ => by unfold posS at e; omega
      simp [this]
    · simp [ht]
  have htop : M / 2 ^ (p.ρ + p.n * p.K) = 0 := Nat.eq_of_testBit_eq fun t => by
    rw [Nat.testBit_div_two_pow, hM]
    have : ¬ ∃ c < p.n, posS p c = t + (p.ρ + p.n * p.K) := fun ⟨c, hc, e⟩ => by
      have := Nat.mul_le_mul_right p.K (show c + 1 ≤ p.n by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      unfold posS at e; omega
    simp [this]
  have hseg : ∀ c < p.n, seg p.ρ p.K c M = (X.testBit (posS p c)).toNat :=
    fun c hc => seg_and_sel hK hc X
  conv_rhs => rw [eq_asm p.ρ p.K p.n (Y ^^^ M)]
  unfold togY
  rw [xor_mod_two_pow, hlow, Nat.xor_zero, xor_div_two_pow, htop, Nat.xor_zero]
  refine asm_congr fun c hc => ?_
  show tog _ (par p c X) = _
  rw [par_eq hK, tog_toNat, seg, seg, window_xor, ← seg, ← seg, hseg c hc]

/-! ### Masked exclusive or on indices -/

section Index

variable {nf : ℕ} (len : Fin nf → ℕ) (F : Fields nf)

/-- Replace the digit of `y` by `y ⊕ (x ∧ mm)`. -/
def xorIdx (mm i : ℕ) : ℕ := setDigit len F.y (digit len F.y i ^^^ (digit len F.x i &&& mm)) i

variable {len F}

/-- Equal lengths of the digits of `y` and `x`, distinct fields. -/
structure XorFields (len : Fin nf → ℕ) (F : Fields nf) : Prop where
  len_eq : len F.x = len F.y
  ne : F.x ≠ F.y

lemma Fields.Valid.xorFields {p : Par} (hF : F.Valid p len) : XorFields len F :=
  ⟨by rw [hF.lx, hF.ly], fun e => by have := hF.distinct; rw [e] at this; simp at this⟩

lemma digit_xorIdx_y (hX : XorFields len F) (mm i : ℕ) :
    digit len F.y (xorIdx len F mm i) = digit len F.y i ^^^ (digit len F.x i &&& mm) := by
  rw [xorIdx, digit_setDigit_self, Nat.mod_eq_of_lt]
  refine Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (lt_of_le_of_lt Nat.and_le_left ?_)
  rw [← hX.len_eq]
  exact Nat.mod_lt _ (by positivity)

lemma digit_xorIdx_ne {g : Fin nf} (hg : g ≠ F.y) (mm i : ℕ) :
    digit len g (xorIdx len F mm i) = digit len g i := by
  rw [xorIdx, digit_setDigit_ne len _ _ hg]

/-- **Masked exclusive or is an involution.** -/
theorem xorIdx_xorIdx (hX : XorFields len F) (mm i : ℕ) :
    xorIdx len F mm (xorIdx len F mm i) = i := by
  apply eq_of_digit_eq len
  · intro g
    by_cases hg : g = F.y
    · subst hg
      rw [digit_xorIdx_y hX, digit_xorIdx_y hX, digit_xorIdx_ne hX.ne, Nat.xor_assoc,
        Nat.xor_self, Nat.xor_zero]
    · rw [digit_xorIdx_ne hg, digit_xorIdx_ne hg]
  · rw [xorIdx, setDigit_div_total, xorIdx, setDigit_div_total]

lemma xorIdx_lt {q R : ℕ} (hq : fieldOff len F.y + len F.y ≤ q) (mm : ℕ) {i : ℕ}
    (hi : i < R * 2 ^ q) : xorIdx len F mm i < R * 2 ^ q := by
  have hpos : 0 < 2 ^ q := by positivity
  have h1 : i / 2 ^ q < R := (Nat.div_lt_iff_lt_mul hpos).2 hi
  rw [← setDigit_div_of_le len F.y hq _ i] at h1
  exact (Nat.div_lt_iff_lt_mul hpos).1 h1

/-- Masked exclusive or as a permutation of the ranks below `R 2^q`. -/
def xorPerm (hX : XorFields len F) {q R : ℕ} (hq : fieldOff len F.y + len F.y ≤ q) (mm : ℕ) :
    Equiv.Perm (Fin (R * 2 ^ q)) where
  toFun i := ⟨xorIdx len F mm i, xorIdx_lt hq mm i.isLt⟩
  invFun i := ⟨xorIdx len F mm i, xorIdx_lt hq mm i.isLt⟩
  left_inv i := Fin.ext (xorIdx_xorIdx hX mm i)
  right_inv i := Fin.ext (xorIdx_xorIdx hX mm i)

/-- The ideal map is the masked exclusive or with the selected bits. -/
lemma idealIdx_eq_xorIdx {p : Par} (hK : 0 < p.K) (i : ℕ) :
    idealIdx p len F i = xorIdx len F (maskVal p.n (posS p)) i := by
  rw [idealIdx, togY_xor hK]; rfl

lemma window_two_pow_of_lt {o w Q : ℕ} (h : Q < o ∨ o + w ≤ Q) : window o w (2 ^ Q) = 0 := by
  rcases h with h | h
  · rw [window, Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h), Nat.zero_mod]
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [window, Nat.pow_add, Nat.pow_add, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity),
      Nat.mul_mod_right]

/-- With the one-bit mask `2^P`, the masked exclusive or flips bit `fieldOff y + P` of the index
when bit `P` of `x` is set. -/
lemma xorIdx_two_pow {P : ℕ} (hP : P < len F.y) (i : ℕ) :
    xorIdx len F (2 ^ P) i =
      if (digit len F.x i).testBit P then i ^^^ 2 ^ (fieldOff len F.y + P) else i := by
  have hand : digit len F.x i &&& 2 ^ P = if (digit len F.x i).testBit P then 2 ^ P else 0 :=
    Nat.eq_of_testBit_eq fun t => by
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      split_ifs with h
      · rw [Nat.testBit_two_pow]; by_cases ht : P = t <;> simp_all
      · simp only [Nat.zero_testBit]; by_cases ht : P = t <;> simp_all
  split_ifs with hx
  · simp only [xorIdx, hand, hx, ↓reduceIte]
    apply eq_of_digit_eq len
    · intro g
      rw [digit_eq_window len g (i ^^^ _), window_xor, ← digit_eq_window]
      by_cases hg : g = F.y
      · subst hg
        rw [digit_setDigit_self, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow
          (show digit len F.y i < 2 ^ len F.y from Nat.mod_lt _ (by positivity))
          (Nat.pow_lt_pow_right (by norm_num) hP)), window, Nat.pow_add,
          Nat.mul_div_cancel_left _ (by positivity), Nat.mod_eq_of_lt
          (Nat.pow_lt_pow_right (by norm_num) hP)]
      · rw [digit_setDigit_ne len _ _ hg, window_two_pow_of_lt, Nat.xor_zero]
        rcases lt_or_gt_of_ne hg with h | h
        · exact Or.inr ((fieldOff_add_le_of_lt len h).trans (by omega))
        · have := fieldOff_add_le_of_lt len h; exact Or.inl (by omega)
    · rw [setDigit_div_total, xor_div_two_pow, Nat.div_eq_of_lt (a := 2 ^ _)
        (Nat.pow_lt_pow_right (by norm_num)
          (lt_of_lt_of_le (by omega) (fieldOff_add_le_total len F.y))), Nat.xor_zero]
  · simp only [xorIdx, hand, hx, Bool.false_eq_true, ↓reduceIte, Nat.xor_zero, setDigit_digit]

/-- **The ideal map keeps good indices good**: it changes only the selected bits of `y`, which
the guards do not read. -/
theorem good_xorIdx {p : Par} (hF : F.Valid p len) (hK : 0 < p.K) (i : ℕ) :
    GoodIdx p len F (xorIdx len F (maskVal p.n (posS p)) i) ↔ GoodIdx p len F i := by
  have hX := hF.xorFields
  have hd := hF.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  have htY : F.t ≠ F.y := hd.2.1.2.1
  have huY : F.u ≠ F.y := hd.2.2.1.1
  unfold GoodIdx Good view
  simp only [digit_xorIdx_ne htY, digit_xorIdx_ne huY, digit_xorIdx_y hX]
  refine forall₂_congr fun c hc => and_congr_right' (and_congr_right' ?_)
  rw [seg, window_xor, ← seg, ← seg, seg_and_sel hK hc,
    show ∀ a b : ℕ, (a ^^^ b) / 2 = a / 2 ^^^ b / 2 from fun a b => by
      simpa using xor_div_two_pow a b 1]
  cases (digit len F.x i).testBit (posS p c) <;> simp

/-- Two masked exclusive ors are one, with the exclusive or of the masks. -/
theorem xorIdx_comp (hX : XorFields len F) (m₁ m₂ i : ℕ) :
    xorIdx len F m₂ (xorIdx len F m₁ i) = xorIdx len F (m₁ ^^^ m₂) i := by
  apply eq_of_digit_eq len
  · intro g
    by_cases hg : g = F.y
    · subst hg
      rw [digit_xorIdx_y hX, digit_xorIdx_y hX, digit_xorIdx_y hX, digit_xorIdx_ne hX.ne,
        Nat.xor_assoc, Nat.and_xor_distrib_left]
    · rw [digit_xorIdx_ne hg, digit_xorIdx_ne hg, digit_xorIdx_ne hg]
  · rw [xorIdx, setDigit_div_total, xorIdx, setDigit_div_total, xorIdx, setDigit_div_total]

/-- The selected bits of the used segments and the top selected bit are the selected bits of
all `n + 1` columns. -/
lemma maskVal_xor_top {p : Par} (hK : 0 < p.K) :
    maskVal p.n (posS p) ^^^ 2 ^ posS p p.n = maskVal (p.n + 1) (posS p) :=
  Nat.eq_of_testBit_eq fun t => by
    rw [Nat.testBit_xor, testBit_maskVal (posS_mono hK), testBit_maskVal (posS_mono hK),
      Nat.testBit_two_pow]
    by_cases ht : posS p p.n = t
    · have : ¬ ∃ c < p.n, posS p c = t := fun ⟨c, hc, e⟩ =>
        (posS_mono hK).injective (e.trans ht.symm) ▸ hc |>.false
      simp only [this, ht, decide_false, decide_true, Bool.false_xor]
      exact (decide_eq_true ⟨p.n, by omega, ht⟩).symm
    · simp only [ht, decide_false, Bool.xor_false]
      refine decide_eq_decide.2 ⟨fun ⟨c, hc, e⟩ => ⟨c, by omega, e⟩, fun ⟨c, hc, e⟩ => ?_⟩
      refine ⟨c, ?_, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | rfl
      · exact h
      · exact absurd e ht

end Index

end IntegerMultBounds.MathlibTM2.Layer.CompactGadget
