module

public import IntegerMultBounds.Resampling.ScriptSem
public import IntegerMultBounds.Resampling.AxisDriver

/-! Scripts for the tensor driver. A swap record with headers built from the
values `P, G, B, h, d` interchanges two address fields of sizes `2^h` and
`2^d` across a gap of `G` (`swapRecG_spec`); records concatenate
(`result_append`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.Script
noncomputable section

open Machine Schoenhage AxisDriver ScriptSem FlatTensor

variable {E : ℕ}

/-- The canonical binary word of `n`. -/
def bin (n : ℕ) : List Bool := GrowingCounterData.advance n []

theorem value_bin (n : ℕ) : Counter.value (bin n) = n := by
  simp [bin, GrowingCounterData.advance_value, Counter.value]

theorem canonical_bin (n : ℕ) : GrowingCounterData.Canonical (bin n) :=
  GrowingCounterData.advance_canonical n [] (Or.inl rfl)

/-- The headers of one interchange: prefix `P`, gap `G`, block `B`, field widths `h` and `d`. -/
def swapHdrsG (P G h d B : ℕ) : List (List Bool) := [bin P, bin G, bin B, bin h, bin d]

theorem swapRecG_spec (P G h d B : ℕ) (A : List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hl : A.length = P * 2 ^ h * G * 2 ^ d * B) :
    SwapPrim.Pre (swIn (swapHdrsG P G h d B) A) ∧
      swapF (swapHdrsG P G h d B) A = SwapPrim.swapList P (2 ^ h) G (2 ^ d) B A := by
  have hw : ∀ i : Fin 6, SwapPrim.words (swIn (swapHdrsG P G h d B) A) i =
      if i.val < 5 then (swapHdrsG P G h d B).getD i.val [] else A := by
    intro i
    simp only [SwapPrim.words, swIn, SwapPrim.slot_val]
    have := i.isLt
    by_cases h5 : i.val < 5
    · simp [h5, reg]
    · have : i.val = 5 := by omega
      simp [this, reg]
  have hv : ∀ i : Fin 5, SwapPrim.vals (swIn (swapHdrsG P G h d B) A) i = ![P, G, B, h, d] i := by
    intro i
    simp only [SwapPrim.vals, SwapPrim.hdr, SwapPrim.focus, hw, Fin.val_castSucc, i.isLt, ite_true]
    fin_cases i <;> simp [swapHdrsG, value_bin]
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
    fin_cases i <;> simp [swapHdrsG, canonical_bin]
  · rw [hv 0]; simpa using hP
  · rw [hv 1]; simpa using hG
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


end
end IntegerMultBounds.Resampling.Script
