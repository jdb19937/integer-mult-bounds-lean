module

public import IntegerMultBounds.Schoenhage.DifHadamard

/-! The paper's layout puts every chunk-group round in the form of one
simultaneous-layer call. With `b = (ℓ - 1) mod K` and `q = ⌊(ℓ - 1)/K⌋`,
the slot `h = b + cK + ρ` (`c < q`, `ρ < K`) of axis `i` sits at physical bit
`cDK + (D - 1 - i)K + ρ` (`paperPerm_σ_chunk`), so the round's bits are the
selected bits `selList (cDK) K ρ D` of the layer on `[P] × [2^K]^D × [S]` with
`S = 2^(cDK)` (`paper_slotBits_chunk`), and the round is the layer operator
`ℋ` followed by one twist (`paper_slotRound_chunk`). The remaining slots,
`h < b` and the top slot `ℓ - 1` of the long axes, are the prefix slots
(`slot_cases`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

variable {r : ℕ}

theorem selList_eq_map (s K ρ : ℕ) : ∀ D : ℕ,
    selList s K ρ D = (List.range D).map fun i => s + (D - 1 - i) * K + ρ
  | 0 => rfl
  | D + 1 => by
    rw [selList, selList_eq_map (s + K) K ρ D, List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      have : D + 1 - 1 - i = (D - 1 - i) + 1 := by omega
      rw [this]; ring
    · simp

/-- Every slot below `ℓ` is a bottom prefix slot, a chunk-group slot, or the top slot. -/
theorem slot_cases {ℓ K h : ℕ} (hK : 1 ≤ K) (hh : h < ℓ) :
    h < (ℓ - 1) % K ∨
      (∃ c ρ, c < (ℓ - 1) / K ∧ ρ < K ∧ h = (ℓ - 1) % K + c * K + ρ) ∨ h = ℓ - 1 := by
  by_cases h1 : h < (ℓ - 1) % K
  · exact Or.inl h1
  · by_cases h2 : h = ℓ - 1
    · exact Or.inr (Or.inr h2)
    · refine Or.inr (Or.inl ⟨(h - (ℓ - 1) % K) / K, (h - (ℓ - 1) % K) % K, ?_, Nat.mod_lt _ (by omega), ?_⟩)
      · have hq := Nat.mod_add_div (ℓ - 1) K
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        have : (ℓ - 1) / K * K = ℓ - 1 - (ℓ - 1) % K := by rw [Nat.mul_comm]; omega
        omega
      · have := Nat.div_add_mod (h - (ℓ - 1) % K) K
        rw [Nat.mul_comm] at this
        omega

/-- In the paper's layout, slot `b + cK + ρ` of axis `i` sits at physical bit `cDK + (D-1-i)K + ρ`. -/
theorem paperPerm_σ_chunk {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {c ρ i : ℕ}
    (hc : c < (ℓ - 1) / K) (hρ : ρ < K) (hi : i < ts.length) :
    (paperPerm hL).σ (axOff ts i + ((ℓ - 1) % K + c * K + ρ)) =
      c * ts.length * K + (ts.length - 1 - i) * K + ρ := by
  set D := ts.length
  set Q := c * D * K + (D - 1 - i) * K + ρ with hQdef
  have hD : 0 < D := by omega
  have hK : 0 < K := by omega
  have hQK : Q / K = c * D + (D - 1 - i) := by
    rw [hQdef, show c * D * K + (D - 1 - i) * K + ρ = ρ + K * (c * D + (D - 1 - i)) by ring,
      Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hρ, zero_add]
  have hQmod : Q % K = ρ := by
    rw [hQdef, show c * D * K + (D - 1 - i) * K + ρ = ρ + K * (c * D + (D - 1 - i)) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]
  have hdivD : (c * D + (D - 1 - i)) / D = c := by
    rw [show c * D + (D - 1 - i) = (D - 1 - i) + D * c by ring, Nat.add_mul_div_left _ _ hD,
      Nat.div_eq_of_lt (by omega), zero_add]
  have hmodD : (c * D + (D - 1 - i)) % D = D - 1 - i := by
    rw [show c * D + (D - 1 - i) = (D - 1 - i) + D * c by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have hQlt : Q < D * ((ℓ - 1) / K) * K := by
    have : (c + 1) * D * K ≤ D * ((ℓ - 1) / K) * K := by
      have := Nat.mul_le_mul_right (D * K) (show c + 1 ≤ (ℓ - 1) / K by omega)
      nlinarith
    have : (D - 1 - i) * K + ρ < D * K := by
      have : (D - 1 - i) * K + K ≤ D * K := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    nlinarith
  have hslot : paperSlot ts ℓ K Q = (i, (ℓ - 1) % K + c * K + ρ) := by
    unfold paperSlot
    rw [ite_eq_left hQlt, hQK, hQmod, hmodD, hdivD]
    simp only [Prod.mk.injEq]
    exact ⟨by omega, by simp⟩
  have htau : paperTau ts ℓ K Q = axOff ts i + ((ℓ - 1) % K + c * K + ρ) := by
    unfold paperTau; rw [hslot]
  have hn : Q < Nat.log 2 ts.prod := by
    calc Q < D * ((ℓ - 1) / K) * K := hQlt
      _ ≤ Nat.log 2 ts.prod := by
        rw [log_prod_layout hL]; exact Nat.le_add_right_of_le (Nat.le_add_right _ _)
  rw [← htau]
  exact BitPerm.ofTau_σ hn

/-- Every axis takes part in a round below the top slot. -/
theorem slotAxes_below_top {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {h : ℕ} (hh : h < ℓ - 1) :
    slotAxes ts h = List.range ts.length := by
  unfold slotAxes
  rw [List.filter_eq_self]
  intro i hi
  have := hL.2.1 i (List.mem_range.mp hi)
  simp only [decide_eq_true_eq]
  omega

/-- The bits of a chunk-group round are the layer's selected bits `selList (cDK) K ρ D`. -/
theorem paper_slotBits_chunk {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {c ρ : ℕ}
    (hc : c < (ℓ - 1) / K) (hρ : ρ < K) :
    slotBits (paperPerm hL) ts (slotAxes ts ((ℓ - 1) % K + c * K + ρ)) ((ℓ - 1) % K + c * K + ρ) =
      selList (c * ts.length * K) K ρ ts.length := by
  have hh : (ℓ - 1) % K + c * K + ρ < ℓ - 1 := by
    have hq := Nat.mod_add_div (ℓ - 1) K
    have : (c + 1) * K ≤ (ℓ - 1) / K * K := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_comm] at hq
    nlinarith
  rw [slotAxes_below_top hL hh, selList_eq_map]
  unfold slotBits
  apply List.map_congr_left
  intro i hi
  exact paperPerm_σ_chunk hL hc hρ (List.mem_range.mp hi)

/-- `paper_slotRound_chunk`: in the paper's layout a chunk-group round is the simultaneous layer's
operator `ℋ` on `[P] × [2^K]^D × [2^(cDK)]` with offset `ρ`, followed by one twist. -/
theorem paper_slotRound_chunk [NeZero r] {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {c ρ : ℕ}
    (hc : c < (ℓ - 1) / K) (hρ : ρ < K) (w : ℕ → Fin r → ℂ) :
    slotRound (paperPerm hL) ts ((ℓ - 1) % K + c * K + ρ) w =
      twist (slotExp (paperPerm hL) r ts (slotAxes ts ((ℓ - 1) % K + c * K + ρ)) ((ℓ - 1) % K + c * K + ρ))
        (hadamard ts.length K ρ (2 ^ (c * ts.length * K)) w) := by
  unfold slotRound
  rw [paper_slotBits_chunk hL hc hρ, hadamard_eq_bflys hρ]

end IntegerMultBounds.Schoenhage
