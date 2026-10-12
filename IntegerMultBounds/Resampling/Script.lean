module

public import IntegerMultBounds.Resampling.ScriptSem
public import IntegerMultBounds.Resampling.AxisDriver

/-! Scripts for the tensor driver. A swap record with headers built from the
values `P, 1, B, h, d` interchanges two adjacent address fields of sizes
`2^h` and `2^d` (`swapRec_spec`); records concatenate (`result_append`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.Script
noncomputable section

open Machine Schoenhage AxisDriver ScriptSem

variable {E : ℕ}

/-- The canonical binary word of `n`. -/
def bin (n : ℕ) : List Bool := GrowingCounterData.advance n []

theorem value_bin (n : ℕ) : Counter.value (bin n) = n := by
  simp [bin, GrowingCounterData.advance_value, Counter.value]

theorem canonical_bin (n : ℕ) : GrowingCounterData.Canonical (bin n) :=
  GrowingCounterData.advance_canonical n [] (Or.inl rfl)

/-- The headers of one interchange: prefix `P`, gap `1`, block `B`, field widths `h` and `d`. -/
def swapHdrs (P h d B : ℕ) : List (List Bool) := [bin P, bin 1, bin B, bin h, bin d]

theorem swapRec_spec (P h d B : ℕ) (A : List Bool) (hP : 0 < P) (hB : 0 < B) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hl : A.length = P * 2 ^ h * 2 ^ d * B) :
    SwapPrim.Pre (swIn (swapHdrs P h d B) A) ∧
      swapF (swapHdrs P h d B) A = SwapPrim.swapList P (2 ^ h) 1 (2 ^ d) B A := by
  have hw : ∀ i : Fin 6, SwapPrim.words (swIn (swapHdrs P h d B) A) i =
      if i.val < 5 then (swapHdrs P h d B).getD i.val [] else A := by
    intro i
    simp only [SwapPrim.words, swIn, SwapPrim.slot_val]
    have := i.isLt
    by_cases h5 : i.val < 5
    · simp [h5, reg]
    · have : i.val = 5 := by omega
      simp [this, reg]
  have hv : ∀ i : Fin 5, SwapPrim.vals (swIn (swapHdrs P h d B) A) i = ![P, 1, B, h, d] i := by
    intro i
    simp only [SwapPrim.vals, SwapPrim.hdr, SwapPrim.focus, hw, Fin.val_castSucc, i.isLt, ite_true]
    fin_cases i <;> simp [swapHdrs, value_bin]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [swIn]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · intro i
    rw [hw i]; simp only [swIn, SwapPrim.slot_val]
    have := i.isLt
    by_cases h5 : i.val < 5
    · simp [h5, reg]
    · have : i.val = 5 := by omega
      simp [this, reg]
  · intro i
    simp only [SwapPrim.hdr, SwapPrim.focus, hw, Fin.val_castSucc, i.isLt, ite_true]
    fin_cases i <;> simp [swapHdrs, canonical_bin]
  · rw [hv 0]; simpa using hP
  · rw [hv 1]; simp
  · rw [hv 2]; simpa using hB
  · rw [hv 3, hv 4]; simpa using hhd
  · rw [hv 3, hv 4]; simpa using hdh
  · rw [hw 5, hv 0, hv 1, hv 2, hv 3, hv 4]
    simp [BinaryAdjacentWidthInterchange.volume, hl]
  · simp only [swapF, SwapPrim.swapped, hv, hw]
    simp

theorem result_append (S : AxisSpec E) : ∀ (r₁ r₂ : List Rec) (A : List Bool),
    result S (r₁ ++ r₂) A = result S r₂ (result S r₁ A)
  | [], _, _ => rfl
  | .axis _ :: r₁, r₂, _ => result_append S r₁ r₂ _
  | .swap _ :: r₁, r₂, _ => result_append S r₁ r₂ _

theorem valid_append (S : AxisSpec E) : ∀ (r₁ r₂ : List Rec) (A : List Bool),
    Valid S r₁ A → Valid S r₂ (result S r₁ A) → Valid S (r₁ ++ r₂) A
  | [], _, _, _, h => h
  | .axis _ :: r₁, r₂, _, ⟨h1, h2, h3⟩, h => ⟨h1, h2, valid_append S r₁ r₂ _ h3 h⟩
  | .swap _ :: r₁, r₂, _, ⟨h1, h2, h3⟩, h => ⟨h1, h2, valid_append S r₁ r₂ _ h3 h⟩

theorem driveCost_append (S : AxisSpec E) : ∀ (r₁ r₂ : List Rec) (A : List Bool),
    driveCost S (r₁ ++ r₂) A = driveCost S r₁ A + driveCost S r₂ (result S r₁ A)
  | [], _, _ => by simp [driveCost, result]
  | .axis _ :: r₁, r₂, A => by simp only [List.cons_append, driveCost, result, driveCost_append S r₁ r₂]; ring
  | .swap _ :: r₁, r₂, A => by simp only [List.cons_append, driveCost, result, driveCost_append S r₁ r₂]; ring

/-- Move the field of width `2^h` inward past fields of widths `2^lᵢ` (outer to inner). -/
def insRecs (h : ℕ) : ℕ → List ℕ → ℕ → List Rec
  | _, [], _ => []
  | Q, l :: ls, B => .swap (swapHdrs Q h l (B * (ls.map (2 ^ ·)).prod)) :: insRecs h (Q * 2 ^ l) ls B

/-- Move the innermost field of width `2^h` outward past fields of widths `2^lᵢ` (inner to outer). -/
def outRecs (h : ℕ) : ℕ → List ℕ → ℕ → List Rec
  | _, [], _ => []
  | Q, l :: ls, B => .swap (swapHdrs (Q * (ls.map (2 ^ ·)).prod) l h B) :: outRecs h Q ls (2 ^ l * B)

theorem insRecs_spec (S : AxisSpec E) (h : ℕ) : ∀ (Q : ℕ) (ls : List ℕ) (B : ℕ) (A : List Bool),
    0 < Q → 0 < B → (∀ l ∈ ls, l ≤ h + 1 ∧ h ≤ l + 1) →
    A.length = Q * 2 ^ h * (ls.map (2 ^ ·)).prod * B →
    Valid S (insRecs h Q ls B) A ∧ result S (insRecs h Q ls B) A = rotIn (2 ^ h) Q (ls.map (2 ^ ·)) B A
  | Q, [], B, A, _, _, _, _ => ⟨trivial, rfl⟩
  | Q, l :: ls, B, A, hQ, hB, hls, hl => by
    have hR : 0 < (ls.map (2 ^ ·)).prod := List.prod_pos (by simp)
    obtain ⟨hpre, hf⟩ := swapRec_spec Q h l (B * (ls.map (2 ^ ·)).prod) A hQ (by positivity)
      (hls l (by simp)).2 (hls l (by simp)).1 (by rw [hl]; simp only [List.map_cons, List.prod_cons]; ring)
    have hlen : (SwapPrim.swapList Q (2 ^ h) 1 (2 ^ l) (B * (ls.map (2 ^ ·)).prod) A).length =
        Q * 2 ^ l * 2 ^ h * (ls.map (2 ^ ·)).prod * B := by rw [length_swapList']; ring
    obtain ⟨hv, hr⟩ := insRecs_spec S h (Q * 2 ^ l) ls B _ (by positivity) hB
      (fun l' hl' => hls l' (by simp [hl'])) (hlen.trans (by ring))
    refine ⟨⟨by simp [swapHdrs], hpre, by rw [hf]; exact hv⟩, ?_⟩
    simp only [insRecs, result, hf, hr, rotIn, List.map_cons]

theorem outRecs_spec (S : AxisSpec E) (h : ℕ) : ∀ (Q : ℕ) (ls : List ℕ) (B : ℕ) (A : List Bool),
    0 < Q → 0 < B → (∀ l ∈ ls, l ≤ h + 1 ∧ h ≤ l + 1) →
    A.length = Q * (ls.map (2 ^ ·)).prod * 2 ^ h * B →
    Valid S (outRecs h Q ls B) A ∧ result S (outRecs h Q ls B) A = rotOut (2 ^ h) Q (ls.map (2 ^ ·)) B A
  | Q, [], B, A, _, _, _, _ => ⟨trivial, rfl⟩
  | Q, l :: ls, B, A, hQ, hB, hls, hl => by
    have hR : 0 < (ls.map (2 ^ ·)).prod := List.prod_pos (by simp)
    obtain ⟨hpre, hf⟩ := swapRec_spec (Q * (ls.map (2 ^ ·)).prod) l h B A (by positivity) hB
      (hls l (by simp)).1 (hls l (by simp)).2 (by rw [hl]; simp only [List.map_cons, List.prod_cons]; ring)
    have hlen : (SwapPrim.swapList (Q * (ls.map (2 ^ ·)).prod) (2 ^ l) 1 (2 ^ h) B A).length =
        Q * (ls.map (2 ^ ·)).prod * 2 ^ h * (2 ^ l * B) := by rw [length_swapList']; ring
    obtain ⟨hv, hr⟩ := outRecs_spec S h Q ls (2 ^ l * B) _ hQ (by positivity)
      (fun l' hl' => hls l' (by simp [hl'])) hlen
    refine ⟨⟨by simp [swapHdrs], hpre, by rw [hf]; exact hv⟩, ?_⟩
    simp only [outRecs, result, hf, hr, rotOut, List.map_cons]

end
end IntegerMultBounds.Resampling.Script
