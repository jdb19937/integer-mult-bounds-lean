module

public import IntegerMultBounds.MathlibTM2.Node.CompactSlotRun
public import IntegerMultBounds.MathlibTM2.Layer.CompactCount

/-!
# The cost of the compact slot XOR

With `M = R 2^n` records, index length `L = n + rb` and record length `B`, every setup stage
costs `O(M (L + B))` steps (`setupStep_le`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer (m)
open IntegerMultBounds.Compact (badRanks)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- The density of bad indices of the late repair: `2 n / 2^G + 8 n 2^G / 2^K`. -/
noncomputable def cxDensity (K G n : ℕ) : ℝ := 2 * n / (2 : ℝ) ^ G + 8 * n * (2 : ℝ) ^ G / (2 : ℝ) ^ K

lemma cxDensity_nonneg (K G n : ℕ) : 0 ≤ cxDensity K G n := by unfold cxDensity; positivity

lemma keyRecCost_le' (yF : Fin 10) (len : Fin 10 → ℕ) (B : ℕ) :
    keyRecCost yF len B ≤ 13 * (∑ f, len f) + 4 * B + 130 := by
  have h : ((List.finRange 10).map (keyCost yF len)).sum ≤ 9 * (∑ f, len f) + 80 := by
    rw [← Fin.sum_univ_def]
    calc ∑ j, keyCost yF len j ≤ ∑ j : Fin 10, (9 * len j + 8) :=
          Finset.sum_le_sum fun j _ => keyCost_le yF len j
      _ = 9 * (∑ f, len f) + 80 := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
  unfold keyRecCost
  omega

namespace CxData

variable {d : CxData}

/-- The slots fit below the address width. -/
lemma OK.slots_le (hd : d.OK) : m * (d.k * d.K) ≤ d.n := by
  have := hd.slots; have := hd.front; unfold wy at *; omega

lemma OK.lens_sum (hd : d.OK) :
    d.lens 0 + d.lens 1 + d.lens 2 + d.lens 3 + d.lens 4 + d.lens 5 + d.lens 6 + d.lens 7 +
      d.lens 8 + d.lens 9 = d.n + d.rb := by
  have h := hd.offs.2.2.2.2.2
  simp only [fieldsLen, Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  simpa [Nat.add_assoc] using h

/-- **Each setup stage** costs `O(M (L + B))`. -/
theorem setupStep_le (hd : d.OK) {o hB act cr cw : ℕ} (hsT : d.sT = hB + act * d.K)
    (hBo : d.B = cr * cw * 2 ^ o) :
    d.setupStep o hB act cr cw ≤ 2000 * (d.R * 2 ^ d.n * (d.n + d.rb + d.B)) := by
  have hk := hd.k1
  have hK : 0 < d.K := by have := hd.ρK; omega
  have hGK := hd.GK
  have hρ := hd.ρK
  have hfr := hd.front
  have hlow := hd.low
  have hsl := hd.slots
  have hR := hd.R0
  have hB1 := hd.B1
  have hm : 1 ≤ m := by decide
  have hkK : d.k * d.K ≤ d.n := le_trans (Nat.le_mul_of_pos_left _ hm) hd.slots_le
  have hKk : d.K ≤ d.k * d.K := Nat.le_mul_of_pos_left _ hk
  have hwc : d.wc = (d.k - 1) * d.G := rfl
  have hwcn : d.wc ≤ d.n := by omega
  -- the products of the stage costs
  have hdiv : d.k * d.K * (10 * d.K + 17) ≤ 27 * (d.n * d.n) := by
    have := Nat.mul_le_mul hkK (show 10 * d.K + 17 ≤ 27 * d.n by omega)
    nlinarith
  have hk1 : (d.k - 1) * (4 * d.G + 7) ≤ 11 * d.n := by
    have : d.k - 1 ≤ d.k * d.K := le_trans (Nat.sub_le _ _) (Nat.le_mul_of_pos_right _ hK)
    rw [Nat.mul_add, Nat.mul_comm 4, ← Nat.mul_assoc, ← hwc]; omega
  have hact : act * (4 * d.K + 7) ≤ 11 * d.n := by
    have h1 : act * d.K ≤ d.n := by omega
    have h2 : act ≤ act * d.K := Nat.le_mul_of_pos_right _ hK
    rw [Nat.mul_add, Nat.mul_comm 4, ← Nat.mul_assoc]; omega
  have h2o : 1 ≤ 2 ^ o := Nat.one_le_two_pow
  have hrw : cr * cw ≤ d.B := by rw [hBo]; exact Nat.le_mul_of_pos_right _ h2o
  have hcw : 1 ≤ cw := by
    rcases Nat.eq_zero_or_pos cw with h | h
    · rw [hBo, h] at hB1; simp at hB1
    · exact h
  have hcr : cr ≤ cr * cw := Nat.le_mul_of_pos_right _ hcw
  have hcrw : cr * (4 * cw + 7) ≤ 11 * d.B := by
    rw [Nat.mul_add, Nat.mul_comm 4, ← Nat.mul_assoc]; omega
  have hB2 : 2 ^ o * (cr * cw) = d.B := by rw [hBo]; ring
  have hcr1 : 1 ≤ cr := by
    rcases Nat.eq_zero_or_pos cr with h | h
    · rw [hBo, h] at hB1; simp at hB1
    · exact h
  have ho : o ≤ d.B := by
    have h1 : 2 ^ o ≤ 2 ^ o * (cr * cw) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hcr1 hcw)
    have h2 := (Nat.lt_two_pow_self (n := o)).le
    omega
  have hhi : (d.hi + 1) * (d.k * d.K) ≤ d.n :=
    le_trans (Nat.mul_le_mul_right _ (show d.hi + 1 ≤ m from hd.hi_lt)) hd.slots_le
  have hmk1 : (d.k - 1) * (4 * d.K + 40 + 3) ≤ 47 * d.n := by
    have := Nat.mul_le_mul_right (4 * d.K + 40 + 3) (show d.k - 1 ≤ d.k from Nat.sub_le _ _)
    have h2 : d.k * (4 * d.K + 40 + 3) ≤ 47 * (d.k * d.K) := by nlinarith
    omega
  have hk1n : d.k - 1 ≤ d.n := le_trans (le_trans (Nat.sub_le _ _)
    (Nat.le_mul_of_pos_right _ hK)) hkK
  have hactn : act ≤ d.n := by
    have h2 : act ≤ act * d.K := Nat.le_mul_of_pos_right _ hK
    omega
  have hs1 := length_sxBits_le d.R
  have hs2 := length_sxBits_le (3 * (d.n + d.rb + d.B))
  have hs3 := length_sxBits_le d.wc
  have hsum := hd.lens_sum
  -- the size `W = M (L + B)` dominates everything
  set M := d.R * 2 ^ d.n with hM
  have hRM : d.R ≤ M := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have hnM : d.n ≤ M := le_trans (Nat.lt_two_pow_self).le (Nat.le_mul_of_pos_left _ hR)
  have hrbR : d.rb ≤ d.R := length_sxBits_le d.R
  have hM1 : 1 ≤ M := by omega
  have hW1 : d.n + d.rb + d.B ≤ M * (d.n + d.rb + d.B) := Nat.le_mul_of_pos_left _ hM1
  have hW2 : M ≤ M * (d.n + d.rb + d.B) := Nat.le_mul_of_pos_right _ (by omega)
  have hW3 : d.n * d.n ≤ M * (d.n + d.rb + d.B) := Nat.mul_le_mul hnM (by omega)
  have hc : 2 ^ d.n * d.R = M := Nat.mul_comm _ _
  unfold setupStep maskCost synMulRCost synDivModCost
  rw [hc]
  omega

open Classical in
/-- The bad indices of the repair are at most a density share of the records. -/
lemma OK.bad_le (hd : d.OK) :
    ((badRanks (Equiv.refl (Fin (d.R * 2 ^ d.n)))
      fun i => ¬ GoodIdx d.par d.lens d.fields i).length : ℝ) ≤
      (d.R * 2 ^ d.n : ℕ) * cxDensity d.K d.G (d.k - 1) := by
  have hlen : (badRanks (Equiv.refl (Fin (d.R * 2 ^ d.n)))
      fun i => ¬ GoodIdx d.par d.lens d.fields i).length =
      ((Finset.range (d.R * 2 ^ d.n)).filter fun i => ¬ GoodIdx d.par d.lens d.fields i).card := by
    unfold badRanks
    exact length_filter_finRange (d.R * 2 ^ d.n) (fun i => ¬ GoodIdx d.par d.lens d.fields i)
  have hc := card_bad_le (R := d.R) hd.valid (by unfold CxData.par; exact hd.GK) hd.touched_le
  rw [hlen]
  refine le_trans (Nat.cast_le.2 hc) ?_
  have hpn : d.par.n = d.k - 1 := rfl
  have hpG : d.par.G = d.G := rfl
  have hpK : d.par.K = d.K := rfl
  rw [hpn, hpG, hpK]
  rcases Nat.eq_zero_or_pos (d.k - 1) with h0 | hpos
  · rw [h0]; simp only [Nat.zero_mul, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (cxDensity_nonneg _ _ _)
  have hGK := hd.GK
  have hwc : d.G ≤ d.wc := by
    unfold CxData.wc; exact Nat.le_mul_of_pos_left _ hpos
  have hGn : d.G ≤ d.n := by have := hd.front; omega
  have hKn : d.K ≤ d.n := le_trans (Nat.le_mul_of_pos_left _ hd.k1)
    (le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < m)) hd.slots_le)
  have e1 : (2:ℝ) ^ (d.n - d.G) * 2 ^ d.G = 2 ^ d.n := by rw [← pow_add]; congr 1; omega
  have e2 : (2:ℝ) ^ (d.n - (d.K - 1 - d.G)) * 2 ^ (d.K - 1 - d.G) = 2 ^ d.n := by
    rw [← pow_add]; congr 1; omega
  have e3 : (2:ℝ) ^ d.K = 2 ^ (d.K - 1 - d.G) * (2 * 2 ^ d.G) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  obtain ⟨a, ha⟩ : ∃ a : ℝ, (2:ℝ) ^ (d.n - d.G) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (2:ℝ) ^ (d.n - (d.K - 1 - d.G)) = b := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, (2:ℝ) ^ d.G = g := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ, (2:ℝ) ^ (d.K - 1 - d.G) = h := ⟨_, rfl⟩
  have hg0 : 0 < g := hg ▸ by positivity
  have hh0 : 0 < h := hh ▸ by positivity
  have ha0 : 0 < a := ha ▸ by positivity
  have hab : a * g = b * h := by rw [← ha, ← hb, ← hg, ← hh, e1, e2]
  unfold cxDensity
  push_cast
  rw [e3, ← e1, ha, hb, hg, hh]
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℝ, ((d.k - 1 : ℕ) : ℝ) = k₁ := ⟨_, rfl⟩
  have hk0 : 0 ≤ k₁ := hk₁ ▸ Nat.cast_nonneg _
  rw [hk₁]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (d.R : ℝ) = r := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hr ▸ Nat.cast_nonneg _
  rw [hr]
  have hb' : b = a * g / h := by rw [eq_div_iff hh0.ne']; linarith [hab]
  rw [hb']
  have e4 : 8 * k₁ * g / (h * (2 * g)) = 4 * k₁ / h := by field_simp; ring
  rw [e4]
  have e5 : r * (a * g) * (2 * k₁ / g + 4 * k₁ / h) = 2 * (r * a * k₁) + 4 * (r * a * g * k₁ / h) := by
    field_simp <;> ring
  have e6 : k₁ * (2 * (r * a) + r * (a * g / h)) = 2 * (r * a * k₁) + r * a * g * k₁ / h := by
    field_simp <;> ring
  rw [e5, e6]
  have : 0 ≤ r * a * g * k₁ / h := by positivity
  linarith

/-- The constant of the compact slot XOR. -/
noncomputable def cxSlotConst (T D : ℕ) : ℝ :=
  3 * 10 ^ 6 + 72 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) + 31 * D + 48 * T + 144 * swapT 6

lemma cxSlotConst_nonneg (T D : ℕ) : 0 ≤ cxSlotConst T D := by
  have := swapConst_pos; unfold cxSlotConst; positivity

/-- A pass of one gadget instruction. -/
lemma OK.opCost_le (hd : d.OK) {T : ℕ} {bankLen : Fin 2 → ℕ} {W S : ℕ}
    (hW : W = d.R * 2 ^ d.n * (d.n + d.rb + d.B)) (hbl : ∀ c, bankLen c ≤ 5 * S)
    (hS : S ≤ 2000 * W) (op : Op) :
    opCost d.par d.lens T d.R d.n (fieldsLen d.lens + d.B) bankLen op ≤
      3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) * W * ((max 1 d.wc : ℕ) : ℝ) ^ Parameters.tau +
        (((61000 + 600) * W + 2 * T + 6 * swapT 6 + 23 : ℕ) : ℝ) := by
  have hL : fieldsLen d.lens = d.n + d.rb := hd.offs.2.2.2.2.2
  have hWL : d.R * 2 ^ d.n * (fieldsLen d.lens + d.B) = W := by rw [hL, hW]
  have hE : (0:ℝ) ≤ ((max 1 d.wc : ℕ) : ℝ) ^ Parameters.tau := by positivity
  have hsc := swapConst_pos
  have hM1 : 1 ≤ d.R * 2 ^ d.n := Nat.mul_pos hd.R0 (Nat.two_pow_pos _)
  have hB1 := hd.B1
  have hW1 : d.R * 2 ^ d.n ≤ W := by rw [hW]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hLW : d.n + d.rb + d.B ≤ W := by rw [hW]; exact Nat.le_mul_of_pos_left _ hM1
  have hwy : d.par.wy = d.wy := hd.wy_eq
  have hkK : d.k * d.K ≤ d.n := le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < m)) hd.slots_le
  have hwcn : d.wc ≤ d.n := by have := hd.front; omega
  have hsum : (∑ f, d.lens f) = d.n + d.rb := hL
  cases op with
  | rotY neg o | rotB neg o =>
    simp only [opCost]
    generalize swapT 6 = st
    have hc : classMoveCost (nd := 2) (cRot d.par) (cRot d.par) (d.R * 2 ^ d.n)
        (fieldsLen d.lens + d.B) d.lens ≤ 600 * W := by
      unfold classMoveCost idxStepCost cRot
      rw [hsum, par_wc, hwy, hL]
      have h1 : d.R * 2 ^ d.n * (20 * d.wc + 34 * d.wy + 40 + 4 * (d.n + d.rb + d.B) +
          4 * (d.n + d.rb) + 4 * 10 + 8 + 1) ≤ d.R * 2 ^ d.n * (150 * (d.n + d.rb + d.B)) :=
        Nat.mul_le_mul_left _ (by unfold CxData.wy; omega)
      have h2 : d.R * 2 ^ d.n * (20 * d.wc + 34 * d.wy + 40 + 4 * (d.n + d.rb + d.B) +
          4 * (d.n + d.rb) + 4 * 10 + 8 + 3) ≤ d.R * 2 ^ d.n * (150 * (d.n + d.rb + d.B)) :=
        Nat.mul_le_mul_left _ (by unfold CxData.wy; omega)
      have h3 : d.R * 2 ^ d.n * (150 * (d.n + d.rb + d.B)) = 150 * W := by rw [hW]; ring
      have h4 : d.R * 2 ^ d.n * (d.n + d.rb + d.B) = W := hW.symm
      omega
    have hc' : ((classMoveCost (nd := 2) (cRot d.par) (cRot d.par) (d.R * 2 ^ d.n)
        (fieldsLen d.lens + d.B) d.lens : ℕ) : ℝ) ≤
        (((61000 + 600) * W + 2 * T + 6 * st + 23 : ℕ) : ℝ) := by
      exact_mod_cast (by omega)
    have : (0:ℝ) ≤ 3 * swapConst * (T + 12 * st + 5 : ℕ) * W *
        ((max 1 d.wc : ℕ) : ℝ) ^ Parameters.tau := by positivity
    linarith
  | swapT | swapU =>
    simp only [opCost]
    generalize swapT 6 = st
    rw [hWL, par_wc]
    have hb := hbl 0
    have hb' := hbl 1
    gcongr
    omega

/-- The natural parts of the cost of the core. -/
lemma OK.coreNat_le (hd : d.OK) {W : ℕ} (hW : W = d.R * 2 ^ d.n * (d.n + d.rb + d.B)) :
    (1 + (d.R * 2 ^ d.n * (keyRecCost d.fields.y d.lens d.B + 1) + 1) +
      (2 * (d.R * 2 ^ d.n * ((∑ j, d.lens j) + d.B)) + 2) + (4 * (∑ f, d.lens f) + 4 * 10 + 1) ≤
      1000 * W) ∧
    (d.R * 2 ^ d.n * (2 * idxStepCost (26 * d.par.wy + 24) (fieldsLen d.lens + d.B) d.lens +
      6 * (fieldsLen d.lens + d.B) + 15) + 10 * fieldsLen d.lens + 8 * (∑ f, d.lens f) + 8 * 10 +
        18 ≤ 1000 * W) ∧
    (d.R * 2 ^ d.n * (2 * idxStepCost (6 * d.par.wy + 4) d.B d.lens + 10 * d.B + 4) +
      8 * (∑ f, d.lens f) + 8 * 10 + 18 ≤ 1000 * W) := by
  have hL : fieldsLen d.lens = d.n + d.rb := hd.offs.2.2.2.2.2
  have hsum : (∑ f, d.lens f) = d.n + d.rb := hL
  have hM1 : 1 ≤ d.R * 2 ^ d.n := Nat.mul_pos hd.R0 (Nat.two_pow_pos _)
  have hB1 := hd.B1
  have hW1 : d.R * 2 ^ d.n ≤ W := by rw [hW]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hLW : d.n + d.rb + d.B ≤ W := by rw [hW]; exact Nat.le_mul_of_pos_left _ hM1
  have hwy : d.par.wy = d.wy := hd.wy_eq
  have hkK : d.k * d.K ≤ d.n := le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < m)) hd.slots_le
  have hmul : ∀ c, d.R * 2 ^ d.n * (c * (d.n + d.rb + d.B)) = c * W := fun c => by rw [hW]; ring
  have hkey := keyRecCost_le' d.fields.y d.lens d.B
  rw [hsum] at hkey
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Nat.mul_le_mul_left (d.R * 2 ^ d.n)
      (show keyRecCost d.fields.y d.lens d.B + 1 ≤ 140 * (d.n + d.rb + d.B) by omega)
    have h2 := Nat.mul_le_mul_left (d.R * 2 ^ d.n)
      (show (∑ j, d.lens j) + d.B ≤ 1 * (d.n + d.rb + d.B) by omega)
    rw [hmul] at h1 h2
    rw [hsum]
    omega
  · unfold idxStepCost
    rw [hsum, hL, hwy]
    have h1 := Nat.mul_le_mul_left (d.R * 2 ^ d.n)
      (show 2 * (26 * d.wy + 24 + 4 * (d.n + d.rb + d.B) + 4 * (d.n + d.rb) + 4 * 10 + 8) +
        6 * (d.n + d.rb + d.B) + 15 ≤ 200 * (d.n + d.rb + d.B) by unfold CxData.wy; omega)
    rw [hmul] at h1
    omega
  · unfold idxStepCost
    rw [hsum, hwy]
    have h1 := Nat.mul_le_mul_left (d.R * 2 ^ d.n)
      (show 2 * (6 * d.wy + 4 + 4 * d.B + 4 * (d.n + d.rb) + 4 * 10 + 8) + 10 * d.B + 4 ≤
        200 * (d.n + d.rb + d.B) by unfold CxData.wy; omega)
    rw [hmul] at h1
    omega

/-- The repair of the bad records. -/
lemma OK.badCost_le (hd : d.OK) {W D b : ℕ} (hW : W = d.R * 2 ^ d.n * (d.n + d.rb + d.B))
    (hdens : cxDensity d.K d.G (d.k - 1) * ((d.n + d.rb + 1 : ℕ) : ℝ) ≤ D)
    (hbad : (b : ℝ) ≤ (d.R * 2 ^ d.n : ℕ) * cxDensity d.K d.G (d.k - 1)) :
    ((fieldsLen d.lens * (b * (12 * fieldsLen d.lens + 6 * d.B + 13)) : ℕ) : ℝ) ≤ 31 * D * W := by
  have hL : fieldsLen d.lens = d.n + d.rb := hd.offs.2.2.2.2.2
  have hB1 := hd.B1
  have hden0 := cxDensity_nonneg d.K d.G (d.k - 1)
  obtain ⟨δ, hδ⟩ : ∃ δ, cxDensity d.K d.G (d.k - 1) = δ := ⟨_, rfl⟩
  rw [hδ] at hdens hbad hden0
  obtain ⟨M, hM⟩ : ∃ M, d.R * 2 ^ d.n = M := ⟨_, rfl⟩
  obtain ⟨L, hL'⟩ : ∃ L, d.n + d.rb = L := ⟨_, rfl⟩
  rw [hM] at hbad hW
  rw [hL, hL']
  rw [show d.n + d.rb + d.B = L + d.B by omega] at hW
  rw [show d.n + d.rb + 1 = L + 1 by omega] at hdens
  have hc : 12 * L + 6 * d.B + 13 ≤ 31 * (L + d.B) := by omega
  have hcR : ((12 * L + 6 * d.B + 13 : ℕ) : ℝ) ≤ 31 * ((L + d.B : ℕ) : ℝ) := by exact_mod_cast hc
  have hLd : (L : ℝ) * δ ≤ D := by
    refine le_trans ?_ hdens
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : L ≤ L + 1)) hden0
  have hWR : (W : ℝ) = (M : ℝ) * ((L + d.B : ℕ) : ℝ) := by rw [hW]; push_cast; ring
  have hL0 : (0:ℝ) ≤ L := Nat.cast_nonneg _
  have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg _
  have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
  have hLB0 : (0:ℝ) ≤ ((L + d.B : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : (b : ℝ) * ((12 * L + 6 * d.B + 13 : ℕ) : ℝ) ≤ (M * δ) * (31 * ((L + d.B : ℕ) : ℝ)) :=
    mul_le_mul hbad hcR (Nat.cast_nonneg _) (by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 hL0
  have h3 : (L : ℝ) * ((M * δ) * (31 * ((L + d.B : ℕ) : ℝ))) =
      ((L : ℝ) * δ) * (31 * ((M : ℝ) * ((L + d.B : ℕ) : ℝ))) := by ring
  have h4 := mul_le_mul_of_nonneg_right hLd (show (0:ℝ) ≤ 31 * ((M : ℝ) * ((L + d.B : ℕ) : ℝ)) by
    positivity)
  rw [hWR]
  push_cast at h2 h3 h4 ⊢
  nlinarith [h2, h3, h4]

/-- The gadget passes. -/
lemma OK.progCost_le (hd : d.OK) {T : ℕ} {bankLen : Fin 2 → ℕ} {W S : ℕ}
    (hW : W = d.R * 2 ^ d.n * (d.n + d.rb + d.B)) (hbl : ∀ c, bankLen c ≤ 5 * S)
    (hS : S ≤ 2000 * W) :
    ((prog.map (opCost d.par d.lens T d.R d.n (fieldsLen d.lens + d.B) bankLen)).sum) ≤
      24 * (3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) * W *
        ((max 1 d.wc : ℕ) : ℝ) ^ Parameters.tau +
        (((61000 + 600) * W + 2 * T + 6 * swapT 6 + 23 : ℕ) : ℝ)) := by
  have := List.sum_le_card_nsmul
    (prog.map (opCost d.par d.lens T d.R d.n (fieldsLen d.lens + d.B) bankLen)) _ fun x hx => by
      obtain ⟨op, -, rfl⟩ := List.mem_map.1 hx
      exact hd.opCost_le (T := T) hW hbl hS op
  simpa only [List.length_map, show prog.length = 24 from rfl, nsmul_eq_mul, Nat.cast_ofNat]
    using this

open Classical in
/-- The core. -/
lemma OK.coreCost_le (hd : d.OK) {T D : ℕ} {bankLen : Fin 2 → ℕ} {W S : ℕ}
    (hW : W = d.R * 2 ^ d.n * (d.n + d.rb + d.B)) (hbl : ∀ c, bankLen c ≤ 5 * S)
    (hS : S ≤ 2000 * W)
    (hdens : cxDensity d.K d.G (d.k - 1) * ((d.n + d.rb + 1 : ℕ) : ℝ) ≤ D) :
    cxCoreCost d.par d.lens d.fields T d.R d.n d.B bankLen ≤
      ((1000 * W : ℕ) : ℝ) + (24 * (3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) * W *
        ((max 1 d.wc : ℕ) : ℝ) ^ Parameters.tau +
        (((61000 + 600) * W + 2 * T + 6 * swapT 6 + 23 : ℕ) : ℝ)) + 1) +
        (((1000 * W : ℕ) : ℝ) + 31 * D * W) + ((1000 * W : ℕ) : ℝ) := by
  obtain ⟨hA1, hA3, hA4⟩ := hd.coreNat_le hW
  have hops := hd.progCost_le (T := T) hW hbl hS
  obtain ⟨b, hb⟩ : ∃ b, (badRanks (Equiv.refl (Fin (d.R * 2 ^ d.n)))
      fun i => ¬ GoodIdx d.par d.lens d.fields i).length = b := ⟨_, rfl⟩
  have hbad := hd.bad_le
  rw [hb] at hbad
  have hbR := hd.badCost_le hW hdens hbad
  unfold cxCoreCost
  rw [hb]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · exact_mod_cast hA1
  · linarith
  · have h3 := (Nat.cast_le (α := ℝ)).2 hA3
    push_cast at h3 hbR ⊢
    linarith
  · exact_mod_cast hA4

/-- **The cost of the compact slot XOR**: `O(M (L + B) max(1, w_c)^τ)`. -/
theorem OK.slotRun_cost_le (hd : d.OK) {o hB act cr cw : ℕ} (hsT : d.sT = hB + act * d.K)
    (hBo : d.B = cr * cw * 2 ^ o) (T D : ℕ) (bankLen : Fin 2 → ℕ)
    (hbl : ∀ c, bankLen c ≤ 5 * d.setupStep o hB act cr cw)
    (hdens : cxDensity d.K d.G (d.k - 1) * ((d.n + d.rb + 1 : ℕ) : ℝ) ≤ D) :
    ((41 * d.setupStep o hB act cr cw + 1 : ℕ) : ℝ) +
        cxCoreCost d.par d.lens d.fields T d.R d.n d.B bankLen +
        ((41 * (2 * d.setupStep o hB act cr cw + 2) + 1 : ℕ) : ℝ) ≤
      cxSlotConst T D * (d.R * 2 ^ d.n * (d.n + d.rb + d.B) : ℕ) *
        ((max 1 d.wc : ℕ) : ℝ) ^ Parameters.tau := by
  obtain ⟨W, hW⟩ : ∃ W, W = d.R * 2 ^ d.n * (d.n + d.rb + d.B) := ⟨_, rfl⟩
  have hS := setupStep_le hd hsT hBo
  rw [← hW] at hS
  have hcore := hd.coreCost_le (T := T) hW hbl hS hdens
  rw [← hW]
  have hM1 : 1 ≤ d.R * 2 ^ d.n := Nat.mul_pos hd.R0 (Nat.two_pow_pos _)
  have hW1 : 1 ≤ W := by rw [hW]; exact Nat.mul_pos hM1 (by have := hd.B1; omega)
  generalize d.setupStep o hB act cr cw = S at hS hcore ⊢
  unfold cxSlotConst
  generalize swapT 6 = st at hcore ⊢
  have hE1 : (1:ℝ) ≤ ((max 1 d.wc : ℕ) : ℝ) ^ Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 d.wc) (by norm_num [Parameters.tau])
  generalize ((max 1 d.wc : ℕ) : ℝ) ^ Parameters.tau = E at hE1 hcore ⊢
  have hSR : (S : ℝ) ≤ 2000 * W := by exact_mod_cast hS
  have hW1R : (1:ℝ) ≤ W := by exact_mod_cast hW1
  have hsc := swapConst_pos
  have hT0 : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hD0 : (0:ℝ) ≤ D := Nat.cast_nonneg _
  have hst0 : (0:ℝ) ≤ st := Nat.cast_nonneg _
  have hWE : (W : ℝ) ≤ W * E := le_mul_of_one_le_right (by linarith) hE1
  have h1E : (1 : ℝ) ≤ W * E := by nlinarith
  push_cast at hcore ⊢
  have hk : (0:ℝ) ≤ swapConst * ((T : ℝ) + 12 * st + 5) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hWE hD0, mul_le_mul_of_nonneg_left h1E hT0,
    mul_le_mul_of_nonneg_left h1E hst0, mul_le_mul_of_nonneg_left hWE hk]

end CxData

end IntegerMultBounds.MathlibTM2.Node
