module

public import IntegerMultBounds.MathlibTM2.Layer.CompactKey

/-!
# The number of bad indices

Among the indices below `R 2^q`, at most `R 2^(q - w)` have a given window of `w` bits below
`q` all ones (`card_window_ones`). An index is bad when, for a used segment `c`, the digit `c`
of `t` or of `u` (`G` bits) or the guard window of `y` (`K - 1 - G` bits) is all ones
(`cdig_good_iff`, `seg_good_iff`), so `card_bad_le`: at most
`n R (2 · 2^(q - G) + 2^(q - (K - 1 - G)))` indices are bad.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactGadget

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Host Finset

/-- **Windows of ones.** -/
theorem card_window_ones (a w R q : ℕ) (h : a + w ≤ q) :
    ((range (R * 2 ^ q)).filter fun i => ∀ j < w, i.testBit (a + j) = true).card ≤
      R * 2 ^ (q - w) := by
  let f : ℕ × ℕ → ℕ := fun x => x.1 + 2 ^ a * ((2 ^ w - 1) + 2 ^ w * x.2)
  have hsub : ((range (R * 2 ^ q)).filter fun i => ∀ j < w, i.testBit (a + j) = true) ⊆
      (range (2 ^ a) ×ˢ range (R * 2 ^ (q - a - w))).image f := by
    intro i hi
    simp only [mem_filter, mem_range] at hi
    obtain ⟨hiq, hones⟩ := hi
    have hwin : i / 2 ^ a % 2 ^ w = 2 ^ w - 1 := by
      have hlt : i / 2 ^ a % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
      by_contra hne
      have h1 : i / 2 ^ a % 2 ^ w + 1 < 2 ^ w := by omega
      refine (lt_all_ones hlt).1 h1 fun g hg => ?_
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm g]
      simp [hg, hones g hg]
    refine mem_image.2 ⟨(i % 2 ^ a, i / 2 ^ (a + w)), ?_, ?_⟩
    · refine mem_product.2 ⟨mem_range.2 (Nat.mod_lt _ (by positivity)), mem_range.2 ?_⟩
      rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.mul_assoc, ← Nat.pow_add,
        show q - a - w + (a + w) = q by omega]
      exact hiq
    · show i % 2 ^ a + 2 ^ a * ((2 ^ w - 1) + 2 ^ w * (i / 2 ^ (a + w))) = i
      rw [← hwin, Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mod_add_div,
        Nat.mod_add_div]
  calc _ ≤ ((range (2 ^ a) ×ˢ range (R * 2 ^ (q - a - w))).image f).card := card_le_card hsub
    _ ≤ (range (2 ^ a) ×ˢ range (R * 2 ^ (q - a - w))).card := card_image_le
    _ = R * 2 ^ (q - w) := by
      rw [card_product, card_range, card_range, show q - w = a + (q - a - w) by omega,
        Nat.pow_add]
      ring

variable {p : Par} {nf : ℕ} {len : Fin nf → ℕ} {F : Fields nf}

/-- A bad index has, for some used segment, an all-ones window in `t`, `u` or the guard of `y`. -/
lemma bad_windows_of_lengths (htlen : len F.t = p.wc)
    (hulen : len F.u = p.wc) (hylen : len F.y = p.wy) (hGK : p.G + 1 < p.K) {i : ℕ}
    (hi : ¬ GoodIdx p len F i) : ∃ c < p.n,
      (∀ j < p.G, i.testBit (fieldOff len F.t + c * p.G + j) = true) ∨
      (∀ j < p.G, i.testBit (fieldOff len F.u + c * p.G + j) = true) ∨
      (∀ j < p.K - 1 - p.G, i.testBit (fieldOff len F.y + (posS p c + 1 + p.G) + j) = true) := by
  have hbit : ∀ (g : Fin nf) (j : ℕ), j < len g →
      (digit len g i).testBit j = i.testBit (fieldOff len g + j) := fun g j hj => by
    rw [digit, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm j]
    simp [hj]
  unfold GoodIdx Good at hi
  push Not at hi
  obtain ⟨c, hc, hgood⟩ := hi
  have hcG : c * p.G + p.G ≤ p.wc := by
    have := Nat.mul_le_mul_right p.G (show c + 1 ≤ p.n by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; unfold Par.wc; omega
  refine ⟨c, hc, ?_⟩
  by_cases ht : cdig p.G c (view len F i).t + 1 < 2 ^ p.G
  · by_cases hu : cdig p.G c (view len F i).u + 1 < 2 ^ p.G
    · have hy : ¬ (seg p.ρ p.K c (view len F i).y / 2 + 2 ^ p.G < 2 ^ (p.K - 1)) :=
        not_lt.2 (hgood ht hu)
      rw [seg_good_iff hGK] at hy
      push Not at hy
      refine Or.inr (Or.inr fun j hj => ?_)
      have hj' : posS p c + 1 + p.G + j < len F.y := by
        rw [hylen]
        have := Nat.mul_le_mul_right p.K (show c + 1 ≤ p.n by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        unfold posS Par.wy; omega
      rw [show fieldOff len F.y + (posS p c + 1 + p.G) + j =
        fieldOff len F.y + (posS p c + 1 + p.G + j) by omega, ← hbit F.y _ hj']
      exact hy j hj
    · rw [cdig_good_iff] at hu
      push Not at hu
      refine Or.inr (Or.inl fun j hj => ?_)
      rw [Nat.add_assoc, ← hbit F.u _ (by rw [hulen]; omega)]
      exact hu j hj
  · rw [cdig_good_iff] at ht
    push Not at ht
    refine Or.inl fun j hj => ?_
    rw [Nat.add_assoc, ← hbit F.t _ (by rw [htlen]; omega)]
    exact ht j hj

open Classical in
/-- **The number of bad indices** below `R 2^q`. -/
theorem card_bad_le_of_lengths (htlen : len F.t = p.wc)
    (hulen : len F.u = p.wc) (hylen : len F.y = p.wy) (hGK : p.G + 1 < p.K) {q R : ℕ}
    (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q) :
    ((range (R * 2 ^ q)).filter fun i => ¬ GoodIdx p len F i).card ≤
      p.n * (2 * (R * 2 ^ (q - p.G)) + R * 2 ^ (q - (p.K - 1 - p.G))) := by
  classical
  set M := R * 2 ^ q
  let W : ℕ → ℕ → Finset ℕ := fun a w => (range M).filter fun i => ∀ j < w, i.testBit (a + j) = true
  have hsub : ((range M).filter fun i => ¬ GoodIdx p len F i) ⊆ (range p.n).biUnion fun c =>
      W (fieldOff len F.t + c * p.G) p.G ∪ W (fieldOff len F.u + c * p.G) p.G ∪
        W (fieldOff len F.y + (posS p c + 1 + p.G)) (p.K - 1 - p.G) := by
    intro i hi
    simp only [mem_filter, mem_range] at hi
    obtain ⟨c, hc, h⟩ := bad_windows_of_lengths htlen hulen hylen hGK hi.2
    simp only [mem_biUnion, mem_range, mem_union, W, mem_filter, mem_range]
    exact ⟨c, hc, by tauto⟩
  have hT := hq F.t (Or.inr (Or.inl rfl))
  have hU := hq F.u (Or.inr (Or.inr (Or.inl rfl)))
  have hY := hq F.y (Or.inr (Or.inr (Or.inr rfl)))
  have hcard : ∀ c ∈ range p.n, (W (fieldOff len F.t + c * p.G) p.G ∪
      W (fieldOff len F.u + c * p.G) p.G ∪
      W (fieldOff len F.y + (posS p c + 1 + p.G)) (p.K - 1 - p.G)).card ≤
      2 * (R * 2 ^ (q - p.G)) + R * 2 ^ (q - (p.K - 1 - p.G)) := by
    intro c hc
    rw [mem_range] at hc
    have hcG : c * p.G + p.G ≤ p.wc := by
      have := Nat.mul_le_mul_right p.G (show c + 1 ≤ p.n by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; unfold Par.wc; omega
    have hcK : posS p c + p.K ≤ p.wy := by
      have := Nat.mul_le_mul_right p.K (show c + 1 ≤ p.n by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; unfold posS Par.wy; omega
    have h1 : (W (fieldOff len F.t + c * p.G) p.G).card ≤ R * 2 ^ (q - p.G) :=
      card_window_ones _ _ R q (by rw [htlen] at hT; omega)
    have h2 : (W (fieldOff len F.u + c * p.G) p.G).card ≤ R * 2 ^ (q - p.G) :=
      card_window_ones _ _ R q (by rw [hulen] at hU; omega)
    have h3 : (W (fieldOff len F.y + (posS p c + 1 + p.G)) (p.K - 1 - p.G)).card ≤
        R * 2 ^ (q - (p.K - 1 - p.G)) :=
      card_window_ones _ _ R q (by rw [hylen] at hY; omega)
    calc _ ≤ (W (fieldOff len F.t + c * p.G) p.G ∪ W (fieldOff len F.u + c * p.G) p.G).card +
          (W (fieldOff len F.y + (posS p c + 1 + p.G)) (p.K - 1 - p.G)).card := card_union_le _ _
      _ ≤ _ := by
        have := card_union_le (W (fieldOff len F.t + c * p.G) p.G)
          (W (fieldOff len F.u + c * p.G) p.G)
        omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ c ∈ range p.n, (W (fieldOff len F.t + c * p.G) p.G ∪
          W (fieldOff len F.u + c * p.G) p.G ∪
          W (fieldOff len F.y + (posS p c + 1 + p.G)) (p.K - 1 - p.G)).card := card_biUnion_le
    _ ≤ ∑ _c ∈ range p.n, (2 * (R * 2 ^ (q - p.G)) + R * 2 ^ (q - (p.K - 1 - p.G))) :=
        sum_le_sum hcard
    _ = _ := by rw [sum_const, card_range, smul_eq_mul]

open Classical in
/-- Compatibility with callers that supply the complete gadget field contract. -/
theorem card_bad_le (hF : F.Valid p len) (hGK : p.G + 1 < p.K) {q R : ℕ}
    (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q) :
    ((range (R * 2 ^ q)).filter fun i => ¬ GoodIdx p len F i).card ≤
      p.n * (2 * (R * 2 ^ (q - p.G)) + R * 2 ^ (q - (p.K - 1 - p.G))) :=
  card_bad_le_of_lengths hF.lt hF.lu hF.ly hGK hq

/-- The length of a filtered `finRange` is the card of the filtered `range`. -/
lemma length_filter_finRange (M : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((List.finRange M).filter fun i : Fin M => decide (P i)).length =
      ((range M).filter P).card := by
  have hnd : (((List.finRange M).filter fun i : Fin M => decide (P i)).map Fin.val).Nodup :=
    ((List.nodup_finRange M).filter _).map Fin.val_injective
  rw [← List.length_map (f := Fin.val), ← List.toFinset_card_of_nodup hnd]
  congr 1
  ext n
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, mem_filter, mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i.isLt, hi⟩
  · rintro ⟨hn, hp⟩; exact ⟨⟨n, hn⟩, hp, rfl⟩

end IntegerMultBounds.MathlibTM2.Layer.CompactGadget
