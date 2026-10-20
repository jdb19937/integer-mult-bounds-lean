module

public import IntegerMultBounds.MathlibTM2.Host.GatherSpread
public import IntegerMultBounds.MathlibTM2.Host.Index

/-!
# Masks at strictly increasing positions

For strictly increasing positions `pos c`, `c < n`, `maskVal n pos = ∑ 2^(pos c)` has its set bits
exactly at the positions (`testBit_maskVal`), and `placeVal n pos b = ∑ b c 2^(pos c)` places
the bits `b c` there (`testBit_placeVal`). Gathering at the mask reads the bits at the positions
in order (`gatherL_mask`); spreading writes them back (`spreadL_mask`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactMasks

open IntegerMultBounds.MathlibTM2.Host Finset

/-- The mask with set bits at `pos c`, `c < n`. -/
def maskVal (n : ℕ) (pos : ℕ → ℕ) : ℕ := ∑ c ∈ range n, 2 ^ pos c

/-- The bits `b c` placed at `pos c`, `c < n`. -/
def placeVal (n : ℕ) (pos : ℕ → ℕ) (b : ℕ → Bool) : ℕ := ∑ c ∈ range n, (b c).toNat * 2 ^ pos c

lemma maskVal_eq_placeVal (n : ℕ) (pos : ℕ → ℕ) : maskVal n pos = placeVal n pos fun _ => true := by
  simp [maskVal, placeVal]

variable {pos : ℕ → ℕ}

/-- A placed value below the next position. -/
lemma placeVal_lt (hpos : StrictMono pos) (b : ℕ → Bool) :
    ∀ n, placeVal n pos b < 2 ^ pos n := by
  intro n
  induction n with
  | zero => simp [placeVal]
  | succ n ih =>
    rw [placeVal, sum_range_succ, ← placeVal]
    have h1 : 2 ^ pos n ≤ 2 ^ pos (n + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num), ← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (hpos (Nat.lt_succ_self n))
    have h2 : (b n).toNat * 2 ^ pos n ≤ 2 ^ pos n := by
      cases b n <;> simp
    have h3 : 2 ^ pos (n + 1) / 2 * 2 ≤ 2 ^ pos (n + 1) := Nat.div_mul_le_self _ _
    omega

/-- The bits of a placed value. -/
theorem testBit_placeVal (hpos : StrictMono pos) (b : ℕ → Bool) (n q : ℕ) :
    (placeVal n pos b).testBit q = decide (∃ c < n, pos c = q ∧ b c = true) := by
  induction n with
  | zero => simp [placeVal]
  | succ n ih =>
    rw [placeVal, sum_range_succ, ← placeVal]
    have hlt := placeVal_lt hpos b n
    have hle : ∀ c < n + 1, pos c ≤ pos n := fun c hc => hpos.monotone (by omega)
    cases hb : b n with
    | false =>
      simp only [Bool.toNat_false, zero_mul, Nat.add_zero, ih]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨c, hc, h1, h2⟩; exact ⟨c, by omega, h1, h2⟩
      · rintro ⟨c, hc, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
        · exact ⟨c, hc, h1, h2⟩
        · rw [hb] at h2; exact absurd h2 (by simp)
    | true =>
      simp only [Bool.toNat_true, one_mul]
      rw [Nat.add_comm]
      rcases lt_trichotomy q (pos n) with hq | hq | hq
      · rw [Nat.testBit_two_pow_add_gt hq, ih]
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨c, hc, h1, h2⟩; exact ⟨c, by omega, h1, h2⟩
        · rintro ⟨c, hc, h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
          · exact ⟨c, hc, h1, h2⟩
          · omega
      · subst hq
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hlt]
        simp only [Bool.not_false, true_eq_decide_iff]
        exact ⟨n, Nat.lt_succ_self n, rfl, hb⟩
      · rw [Nat.testBit_eq_false_of_lt]
        · symm
          simp only [decide_eq_false_iff_not, not_exists, not_and]
          intro c hc h1
          have := hle c hc
          omega
        · calc 2 ^ pos n + placeVal n pos b < 2 ^ pos n + 2 ^ pos n := by omega
            _ = 2 ^ (pos n + 1) := by ring
            _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq

theorem testBit_maskVal (hpos : StrictMono pos) (n q : ℕ) :
    (maskVal n pos).testBit q = decide (∃ c < n, pos c = q) := by
  rw [maskVal_eq_placeVal, testBit_placeVal hpos]
  simp

/-! ### Gathering at a mask -/

lemma gatherL_ofFn : ∀ (L : ℕ) (f m : Fin L → Bool),
    gatherL (List.ofFn f) (List.ofFn m) = ((List.finRange L).filter fun q => m q).map f
  | 0, _, _ => rfl
  | L + 1, f, m => by
    have ih := gatherL_ofFn L (fun i => f i.succ) (fun i => m i.succ)
    rw [List.ofFn_succ, List.ofFn_succ, List.finRange_succ]
    cases hm : m 0 <;> simp [gatherL, hm, ih, List.filter_map, List.map_map, Function.comp_def]

/-- Gathering at a mask reads the bits at its positions, in order. -/
theorem gatherL_mask (hpos : StrictMono pos) {n L : ℕ} (hL : ∀ c < n, pos c < L) (s : ℕ) :
    gatherL (binBits L s) (binBits L (maskVal n pos)) =
      List.ofFn fun c : Fin n => s.testBit (pos c) := by
  rw [binBits, binBits, gatherL_ofFn]
  have hsort : ((List.finRange L).filter fun q : Fin L =>
      (maskVal n pos).testBit q).map Fin.val = (List.range n).map pos := by
    apply List.SortedLT.eq_of_mem_iff
    · exact (((List.pairwise_lt_finRange L).filter _).map Fin.val (fun _ _ h => h)).sortedLT
    · exact ((List.pairwise_lt_range).map _ (fun _ _ h => hpos h)).sortedLT
    · intro q
      simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, List.mem_range,
        testBit_maskVal hpos, decide_eq_true_eq]
      constructor
      · rintro ⟨q, ⟨c, hc, hcq⟩, rfl⟩; exact ⟨c, hc, hcq⟩
      · rintro ⟨c, hc, rfl⟩; exact ⟨⟨pos c, hL c hc⟩, ⟨c, hc, rfl⟩, rfl⟩
  have : ((List.finRange L).filter fun q : Fin L => (maskVal n pos).testBit q).map
      (fun q : Fin L => s.testBit q) = (((List.finRange L).filter fun q : Fin L =>
      (maskVal n pos).testBit q).map Fin.val).map s.testBit := by
    rw [List.map_map]; rfl
  rw [this, hsort, List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-! ### Spreading at a mask -/

lemma length_gatherL_le : ∀ (ss ms : List Bool), (gatherL ss ms).length ≤ ss.length
  | [], _ => by simp [gatherL]
  | _ :: _, [] => by simp [gatherL]
  | s :: ss, m :: ms => by
    have := length_gatherL_le ss ms
    cases m <;> simp [gatherL] <;> omega

lemma spreadL_getElem_false : ∀ (ss ms : List Bool) (q : ℕ) (hq : q < ms.length),
    ms[q] = false → (spreadL ss ms)[q]'(by rw [length_spreadL]; exact hq) = false
  | _, [], _, hq, _ => by simp at hq
  | ss, true :: ms, 0, _, h => by simp at h
  | ss, false :: ms, 0, _, _ => by simp [spreadL]
  | ss, true :: ms, q + 1, hq, h => by
    simp only [spreadL, List.getElem_cons_succ]
    exact spreadL_getElem_false ss.tail ms q (by simpa using hq) (by simpa using h)
  | ss, false :: ms, q + 1, hq, h => by
    simp only [spreadL, List.getElem_cons_succ]
    exact spreadL_getElem_false ss ms q (by simpa using hq) (by simpa using h)

lemma gatherL_spreadL : ∀ (ss ms : List Bool), ms.count true = ss.length →
    gatherL (spreadL ss ms) ms = ss
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | ss, false :: ms, h => by
    simp only [List.count_cons, Bool.false_eq_true, beq_iff_eq, ite_false, Nat.add_zero] at h
    simp [spreadL, gatherL, gatherL_spreadL ss ms (by simpa using h)]
  | [], true :: ms, h => by simp at h
  | s :: ss, true :: ms, h => by
    simp only [List.count_cons, ite_true, beq_self_eq_true, List.length_cons,
      Nat.add_right_cancel_iff] at h
    simp [spreadL, gatherL, gatherL_spreadL ss ms (by simpa using h)]

/-- Two lists that vanish off a mask and agree on it are equal. -/
lemma eq_of_gatherL (ms : List Bool) : ∀ (l₁ l₂ : List Bool) (h1 : l₁.length = ms.length)
    (h2 : l₂.length = ms.length),
    (∀ q (hq : q < ms.length), ms[q] = false →
      l₁[q]'(by omega) = false ∧ l₂[q]'(by omega) = false) →
    gatherL l₁ ms = gatherL l₂ ms → l₁ = l₂ := by
  induction ms with
  | nil =>
    intro l₁ l₂ h1 h2 _ _
    rw [List.eq_nil_of_length_eq_zero h1, List.eq_nil_of_length_eq_zero h2]
  | cons m ms ih =>
    intro l₁ l₂ h1 h2 hz hg
    rcases l₁ with _ | ⟨a, l₁⟩
    · simp at h1
    rcases l₂ with _ | ⟨b, l₂⟩
    · simp at h2
    have h1' : l₁.length = ms.length := by simpa using h1
    have h2' : l₂.length = ms.length := by simpa using h2
    have hz' : ∀ q (hq : q < ms.length), ms[q] = false →
        l₁[q]'(by omega) = false ∧ l₂[q]'(by omega) = false := fun q hq h =>
      hz (q + 1) (by simpa using hq) (by simpa using h)
    cases m with
    | false =>
      have h0 := hz 0 (by simp) rfl
      simp only [List.getElem_cons_zero] at h0
      simp only [gatherL, Bool.false_eq_true, ite_false] at hg
      rw [h0.1, h0.2, ih l₁ l₂ h1' h2' hz' hg]
    | true =>
      simp only [gatherL, ite_true, List.cons.injEq] at hg
      rw [hg.1, ih l₁ l₂ h1' h2' hz' hg.2]

/-- A mask has one set bit per position. -/
theorem count_maskVal (hpos : StrictMono pos) {n L : ℕ} (hL : ∀ c < n, pos c < L) :
    (binBits L (maskVal n pos)).count true = n := by
  have h := length_gatherL (binBits L 0) (binBits L (maskVal n pos)) (by simp)
  rw [gatherL_mask hpos hL] at h
  simpa using h.symm

/-- Spreading at a mask places the bits at its positions. -/
theorem spreadL_mask (hpos : StrictMono pos) {n L : ℕ} (hL : ∀ c < n, pos c < L)
    (b : ℕ → Bool) :
    spreadL (List.ofFn fun c : Fin n => b c) (binBits L (maskVal n pos)) =
      binBits L (placeVal n pos b) := by
  have hcount : (binBits L (maskVal n pos)).count true = n := by
    have h := length_gatherL (binBits L 0) (binBits L (maskVal n pos)) (by simp)
    rw [gatherL_mask hpos hL] at h
    simpa using h.symm
  have h1 : (spreadL (List.ofFn fun c : Fin n => b c) (binBits L (maskVal n pos))).length =
      (binBits L (maskVal n pos)).length := length_spreadL _ _
  have h2 : (binBits L (placeVal n pos b)).length = (binBits L (maskVal n pos)).length := by simp
  refine eq_of_gatherL (binBits L (maskVal n pos)) _ _ h1 h2 ?_ ?_
  · intro q hq hm
    refine ⟨spreadL_getElem_false _ _ q hq hm, ?_⟩
    simp only [binBits, List.getElem_ofFn] at hm ⊢
    rw [testBit_placeVal hpos]
    rw [testBit_maskVal hpos] at hm
    simp only [decide_eq_false_iff_not, not_exists, not_and] at hm ⊢
    exact fun c hc h _ => hm c hc h
  · rw [gatherL_spreadL _ _ (by simpa using hcount), gatherL_mask hpos hL]
    apply List.ext_getElem (by simp)
    intro i h1 _
    simp only [List.getElem_ofFn]
    rw [testBit_placeVal hpos]
    simp only [List.length_ofFn] at h1
    cases hb : b i
    · rw [eq_comm, decide_eq_false_iff_not]
      rintro ⟨c, hc, h, hbc⟩
      rw [hpos.injective h, hb] at hbc
      simp at hbc
    · rw [eq_comm, decide_eq_true_eq]
      exact ⟨i, h1, rfl, hb⟩

end IntegerMultBounds.MathlibTM2.Layer.CompactMasks
