import IntegerMultBounds.Schoenhage.RingBridgeMath
import IntegerMultBounds.NLogN.SynthFFT

/-! The recordwise monomial of the synthetic transforms (§6): multiplication
of a polynomial record by `y^E` modulo `y^r + 1`. With `E = e r + s`,
`0 ≤ s < r`, the coefficient list is split before position `r - s`, the tail
is put before the head and negated, and the common sign `(-1)^e` is applied.
On the record's component words (most significant bit first) this is
`twWords`: the words are rotated and some are negated in two's complement
(`negW`). It is exact on the grid (`gridPoly_twistRec`) and preserves disk
grid records (`DiskGrid.twistRec`). -/

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

/-! ### Two's complement negation -/

/-- Two's complement negation, least significant bit first: copy through the first one, then
invert. -/
def negL : List Bool → List Bool
  | [] => []
  | b :: bs => b :: if b then bs.map (!·) else negL bs

@[simp] theorem length_negL : ∀ t : List Bool, (negL t).length = t.length
  | [] => rfl
  | b :: bs => by cases b <;> simp [negL, length_negL bs]

theorem bval_map_not : ∀ t : List Bool, bval (t.map (!·)) + bval t + 1 = 2 ^ t.length
  | [] => by simp
  | b :: bs => by have := bval_map_not bs; cases b <;> simp [pow_succ] <;> omega

theorem bval_negL : ∀ t : List Bool, bval (negL t) = (2 ^ t.length - bval t) % 2 ^ t.length
  | [] => by simp [negL]
  | b :: bs => by
    have hl := bval_lt bs
    cases b
    · have ih := bval_negL bs
      simp only [negL, Bool.false_eq_true, ↓reduceIte, bval_cons, List.length_cons, pow_succ, ih]
      generalize bval bs = x at *
      generalize 2 ^ bs.length = N at *
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · simp
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · have := bval_map_not bs
      simp only [negL, ↓reduceIte, bval_cons, List.length_cons, pow_succ]
      generalize bval bs = x at *
      generalize bval (bs.map (!·)) = y at *
      generalize 2 ^ bs.length = N at *
      rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem neg_emod_toNat {N : ℕ} (hN : 0 < N) (z : ℤ) :
    ((-z) % (N : ℤ)).toNat = (N - (z % (N : ℤ)).toNat) % N := by
  have h0 : 0 ≤ z % (N : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : z % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
  have e : (-z) % (N : ℤ) = ((N : ℤ) - z % N) % N := by
    rw [Int.sub_emod, Int.emod_self, Int.emod_emod_of_dvd _ (dvd_refl _), zero_sub,
      show -z = 0 - z by ring, Int.sub_emod, Int.zero_emod, zero_sub]
  rw [e]
  have : ((N : ℤ) - z % N) = ((N - (z % (N : ℤ)).toNat : ℕ) : ℤ) := by omega
  rw [this, ← Int.natCast_mod, Int.toNat_natCast]

theorem negL_tw (w : ℕ) (z : ℤ) : negL (tw w z) = tw w (-z) := by
  have hl : (negL (tw w z)).length = w := by simp [tw]
  have hN : 0 < 2 ^ w := by positivity
  have e2 : ((2 : ℤ) ^ w) = ((2 ^ w : ℕ) : ℤ) := by push_cast; rfl
  have hlt : (z % ((2 ^ w : ℕ) : ℤ)).toNat < 2 ^ w := by
    have := Int.emod_lt_of_pos z (show (0 : ℤ) < ((2 ^ w : ℕ) : ℤ) by positivity)
    have := Int.emod_nonneg z (show ((2 ^ w : ℕ) : ℤ) ≠ 0 by positivity)
    omega
  rw [← bits_bval (negL (tw w z)), hl, bval_negL]
  simp only [tw, length_bits, bval_bits, e2]
  rw [neg_emod_toNat hN z, Nat.mod_eq_of_lt hlt]

/-- Two's complement negation of a word written most significant bit first. -/
def negW (x : List Bool) : List Bool := (negL x.reverse).reverse

theorem negW_compWord (w : ℕ) (z : ℤ) : negW (compWord w z) = compWord w (-z) := by
  rw [negW, compWord_reverse, negL_tw, tw_reverse]

/-! ### The monomial on records -/

/-- The sign `(-1)^k` as an integer. -/
def sgnZ (k : ℕ) : ℤ := (-1) ^ k

/-- Multiplication of a record by `y^E` modulo `y^r + 1`. -/
def twistRec {r : ℕ} [NeZero r] (E : ℕ) (f : Rec r) : Rec r :=
  (fun i => sgnZ (((shiftSrc r E i).val + E) / r) * f.1 (shiftSrc r E i),
    fun i => sgnZ (((shiftSrc r E i).val + E) / r) * f.2 (shiftSrc r E i))

theorem gridPoly_twistRec {r : ℕ} [NeZero r] (p E : ℕ) (f : Rec r) :
    gridPoly p (twistRec E f).1 (twistRec E f).2 = shiftNegZ E (gridPoly p f.1 f.2) := by
  funext i
  rw [shiftNegZ_apply]
  simp only [twistRec, gridPoly, sgnZ]
  rcases Nat.even_or_odd (((shiftSrc r E i).val + E) / r) with h | h <;>
    rw [h.neg_one_pow, h.neg_one_pow] <;> apply Complex.ext <;> simp [neg_div]

theorem DiskGrid.twistRec {r p : ℕ} [NeZero r] {f : Rec r} (h : DiskGrid p f.1 f.2) (E : ℕ) :
    DiskGrid p (twistRec E f).1 (twistRec E f).2 := by
  intro i
  have := h (shiftSrc r E i)
  simp only [Schoenhage.twistRec, sgnZ]
  rcases Nat.even_or_odd (((shiftSrc r E i).val + E) / r) with h | h <;>
    rw [h.neg_one_pow] <;> simpa using this

/-! ### The monomial on component words -/

/-- The words after the monomial: split before word `n = 2 (r - s)`, the tail first, negating the
tail when `e` is false and the head when `e` is true. -/
def twWords (n : ℕ) (e : Bool) (ws : List (List Bool)) : List (List Bool) :=
  (ws.drop n).map (fun x => if e then x else negW x) ++ (ws.take n).map (fun x => if e then negW x else x)

theorem flatMap_pair_getElem {α : Type} (f g : α → List Bool) :
    ∀ (l : List α) (m : ℕ) (hm : m < (l.flatMap fun x => [f x, g x]).length),
      (l.flatMap fun x => [f x, g x])[m] =
        if m % 2 = 0 then f (l[m / 2]'(by simp at hm; omega)) else g (l[m / 2]'(by simp at hm; omega))
  | [], m, hm => by simp at hm
  | x :: l, 0, _ => by simp
  | x :: l, 1, _ => by simp
  | x :: l, m + 2, hm => by
    have hm' : m < (l.flatMap fun x => [f x, g x]).length := by simp at hm ⊢; omega
    have ih := flatMap_pair_getElem f g l m hm'
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ]
    rw [ih]
    have e1 : (m + 2) % 2 = m % 2 := by omega
    have e2 : (m + 2) / 2 = m / 2 + 1 := by omega
    simp only [e1, e2, List.getElem_cons_succ]

@[simp] theorem length_recordWords {r : ℕ} (w : ℕ) (re im : Fin r → ℤ) :
    (recordWords w re im).length = 2 * r := by
  simp [recordWords]; ring

theorem recordWords_getElem {r : ℕ} (w : ℕ) (re im : Fin r → ℤ) (m : ℕ) (hm : m < 2 * r) :
    (recordWords w re im)[m]'(by simpa using hm) =
      compWord w (if m % 2 = 0 then re ⟨m / 2, by omega⟩ else im ⟨m / 2, by omega⟩) := by
  unfold recordWords
  rw [flatMap_pair_getElem]
  simp only [List.getElem_finRange]
  split_ifs <;> rfl

theorem sgnZ_mul_compWord (w k : ℕ) (z : ℤ) :
    compWord w (sgnZ k * z) = if k % 2 = 0 then compWord w z else negW (compWord w z) := by
  rw [negW_compWord]
  unfold sgnZ
  split_ifs with h
  · rw [Even.neg_one_pow (Nat.even_iff.mpr h), one_mul]
  · rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega)), neg_one_mul]

/-- On component words, the monomial `y^E` is `twWords` with `s = E mod r`, `e` the parity of
`⌊E / r⌋`. -/
theorem twWords_recordWords {r : ℕ} [NeZero r] (w E : ℕ) (f : Rec r) :
    twWords (2 * (r - E % r)) (E / r % 2 = 1) (recordWords w f.1 f.2) =
      recordWords w (twistRec E f).1 (twistRec E f).2 := by
  have hr := NeZero.pos r
  have hs : E % r < r := Nat.mod_lt _ hr
  unfold twWords
  apply List.ext_getElem
  · simp <;> omega
  intro m h1 h2
  have hm : m < 2 * r := by simpa using h2
  rw [recordWords_getElem w _ _ m hm]
  have hE := Nat.mod_add_div E r
  by_cases hlt : m < 2 * (E % r)
  · have hd : m < (((recordWords w f.1 f.2).drop (2 * (r - E % r))).map
        (fun x => if decide (E / r % 2 = 1) = true then x else negW x)).length := by simp; omega
    rw [List.getElem_append_left hd, List.getElem_map, List.getElem_drop,
      recordWords_getElem w _ _ _ (by omega)]
    have hsrc : (shiftSrc r E ⟨m / 2, by omega⟩).val = (2 * (r - E % r) + m) / 2 := by
      simp only [shiftSrc]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hk : ((shiftSrc r E ⟨m / 2, by omega⟩).val + E) / r = E / r + 1 := by
      rw [hsrc]
      have : (2 * (r - E % r) + m) / 2 + E = (m / 2 + r - E % r) + E % r + r * (E / r) := by omega
      rw [this, show m / 2 + r - E % r + E % r = m / 2 + r by omega, Nat.add_mul_div_left _ _ hr,
        show m / 2 + r = (m / 2) + 1 * r by ring, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt (by omega)]
      ring
    have hpar : (2 * (r - E % r) + m) % 2 = m % 2 := by omega
    simp only [twistRec, hpar]
    have e1 : (⟨(2 * (r - E % r) + m) / 2, by omega⟩ : Fin r) = shiftSrc r E ⟨m / 2, by omega⟩ :=
      Fin.ext hsrc.symm
    split_ifs with hm2 he <;> simp only [e1, hk, sgnZ_mul_compWord, decide_eq_true_eq] <;> split_ifs <;>
      first | rfl | (simp only [decide_eq_true_eq] at *; omega)
  · have hd : (((recordWords w f.1 f.2).drop (2 * (r - E % r))).map
        (fun x => if decide (E / r % 2 = 1) = true then x else negW x)).length ≤ m := by simp; omega
    rw [List.getElem_append_right hd, List.getElem_map, List.getElem_take]
    have hl : (List.map (fun x => if decide (E / r % 2 = 1) = true then x else negW x)
        ((recordWords w f.1 f.2).drop (2 * (r - E % r)))).length = 2 * (E % r) := by simp; omega
    simp only [hl]
    rw [recordWords_getElem w _ _ _ (by omega)]
    have hsrc : (shiftSrc r E ⟨m / 2, by omega⟩).val = (m - 2 * (E % r)) / 2 := by
      simp only [shiftSrc]
      rw [show m / 2 + (r - E % r) = (m / 2 - E % r) + r by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    have hk : ((shiftSrc r E ⟨m / 2, by omega⟩).val + E) / r = E / r := by
      rw [hsrc]
      have : (m - 2 * (E % r)) / 2 + E = ((m - 2 * (E % r)) / 2 + E % r) + r * (E / r) := by omega
      rw [this, Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt (by omega)]
      ring
    have hpar : (m - 2 * (E % r)) % 2 = m % 2 := by omega
    simp only [twistRec, hpar]
    have e1 : (⟨(m - 2 * (E % r)) / 2, by omega⟩ : Fin r) = shiftSrc r E ⟨m / 2, by omega⟩ :=
      Fin.ext hsrc.symm
    split_ifs with hm2 he <;> simp only [e1, hk, sgnZ_mul_compWord, decide_eq_true_eq] <;> split_ifs <;>
      first | rfl | (simp only [decide_eq_true_eq] at *; omega)

end IntegerMultBounds.Schoenhage
