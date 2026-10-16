module

public import IntegerMultBounds.MathlibTM2.Fast.BandLineSpec
public import IntegerMultBounds.NLogN.SchurSizes
public import IntegerMultBounds.NLogN.PhaseCellPerturb

/-!
# Record widths of the banded `B̃₀`

The factorization and the line solve of the folded Gaussian window matrix only meet
numerators of small grid values: stage entries at most `3`, pivots in `[β, 3]`, Newton
iterates at most `2/β`, multipliers at most `6/β`. With `(6/β + 1) 2^P < 2^(w-1)` every
record fits the width `w` (`band_facFits`). The stage invariant of the window matrix is
the hypothesis; for the Gaussian window it is `perturb_stageInv`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.BandList
open IntegerMultBounds.MathlibTM2.Mult.Sizes
open Finset

/-- A numerator whose grid value is at most `C` fits when `C 2^P < 2^(w-1)`. -/
theorem fits_of_gv {w P : ℕ} {z : ℤ} {C : ℝ} (hz : |gv P z| ≤ C) (hC : C * 2 ^ P < 2 ^ (w - 1)) :
    Fits w (⟨z, 0⟩ : GaussianInt) := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have e : |(z : ℝ)| = |gv P z| * 2 ^ P := by
    rw [gv, abs_div, abs_of_pos hP]; field_simp
  refine ⟨?_, by simp⟩
  have : |(z : ℝ)| < 2 ^ (w - 1) := by
    rw [e]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hz hP.le) hC
  exact_mod_cast this

section Stages

variable (P K wd s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ)

/-- The folded matrix has the stage invariant of the window matrix. -/
theorem foldZ_stageInv {μ m : ℝ}
    (hinv : StageInv (windowMatrix s wd fun j k => gv P (aZ j k)) univ μ m) :
    StageInv (gvM P (foldZ s wd aZ)) (Ico 0 s) μ m := by
  have h := stageInv_map (foldPos s) (foldPos_injective s) _ (gvM P (foldZ s wd aZ)) (fun a c => by
    simp only [gvM, foldZ, foldPos_lt, and_self, ite_true, foldAt_foldPos]
    exact wmZ_gv P s wd aZ a c) univ μ m hinv
  rwa [image_foldPos] at h

variable {P K wd s aZ}

/-- **Sizes of the stage matrices.** Under the stage invariant of the window matrix with
margin `1/(16p)` and mass `9/4`, and the precision conditions of the machine solve, every
pivot of the integer stage matrices has grid value in `[β, 3]` and every active entry at
most `3`. -/
theorem band_stgZ_sizes (p : ℕ) (hp : 2 ≤ p) (hP : 2 ≤ P)
    (hinv : StageInv (windowMatrix s wd fun j k => gv P (aZ j k)) univ (1 / (8 * (2 * (p : ℝ))))
      (9 / 4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1 / (8 * (2 * (p : ℝ))) / 2)
    (hηβ : 5 * (1 / 2 ^ P : ℝ) ≤ 2 * (β / 4) / 9)
    (hK : (1 - β / 4 / 2) ^ (2 ^ K) ≤ 3 * (5 * (1 / 2 ^ P : ℝ)) / (β / 4))
    (hsmall : 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (s : ℝ) ^ 2 * ((1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (m : ℕ) (hm : m < s) :
    (β ≤ gv P (stgZ P K (foldZ s wd aZ) m m m) ∧ gv P (stgZ P K (foldZ s wd aZ) m m m) ≤ 3) ∧
      ∀ i l, m ≤ i → m ≤ l → |gv P (stgZ P K (foldZ s wd aZ) m i l)| ≤ 3 := by
  set η : ℝ := 1 / 2 ^ P
  have hη : 0 ≤ η := by positivity
  set η' := η * (1 + 60 * 3 / β ^ 2) with hη'
  have hle : η ≤ η' := by
    have : 0 ≤ η * (60 * 3 / β ^ 2) := by positivity
    nlinarith
  have hrd' : ∀ x, |rdP P x - x| ≤ η' := fun x => (rdP_err P x).trans (by simpa [η] using hle)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (2 : ℝ) ≤ 2 * (p : ℝ) := by linarith
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hμ : (0 : ℝ) < 1 / (8 * (2 * (p : ℝ))) := by positivity
  obtain ⟨-, hmu', -, -, -⟩ := bandM_arith (2 * (p : ℝ)) (s : ℝ) η' hqR hs1 (by positivity) hsmall
  have hm'' : 9 / 4 + (s : ℝ) * (η' * (s + 3)) ≤ 3 := by
    have hη0 : 0 ≤ η' := by positivity
    have hss : (s : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
    have h1 : (s : ℝ) * (η' * (s + 3)) ≤ 4 * ((s : ℝ) ^ 2 * η') := by
      have e : (s : ℝ) * (η' * (s + 3)) = (s : ℝ) ^ 2 * η' + 3 * ((s : ℝ) * η') := by ring
      have := mul_le_mul_of_nonneg_right hss hη0
      rw [e]; linarith
    have hq4 : (1 : ℝ) ≤ (2 * (p : ℝ)) ^ 2 := by nlinarith
    have h3 : 2 ^ 16 * ((s : ℝ) ^ 2 * η') ≤ 1 := by
      calc 2 ^ 16 * ((s : ℝ) ^ 2 * η') = 1 * (2 ^ 16 * ((s : ℝ) ^ 2 * η')) := (one_mul _).symm
        _ ≤ (2 * (p : ℝ)) ^ 2 * (2 ^ 16 * ((s : ℝ) ^ 2 * η')) :=
          mul_le_mul_of_nonneg_right hq4 (by positivity)
        _ = 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (s : ℝ) ^ 2 * η' := by ring
        _ ≤ 1 := hsmall
    linarith
  have hmul : ∀ a c, |a| ≤ 3 → 1 / (8 * (2 * (p : ℝ))) / 2 ≤ c → c ≤ 3 →
      |PhaseCellMatrix.machMul (rdP P) K a c - a / c| ≤ η' := by
    intro a c ha hc hc3
    have e : PhaseCellMatrix.machMul (rdP P) K a c = NewtonRecip.recipMul (rdP P) 3 β K a c := by
      simp only [PhaseCellMatrix.machMul, NewtonRecip.recipMul, hβp.trans hc, hc3, ha, and_self,
        ite_true]
    rw [e]
    exact NewtonRecip.recipMul_err (rdP P) η (rdP_err P) 3 β (by norm_num) hβ hηβ K hK a c
  have hA := foldZ_stageInv P wd s aZ hinv
  have hcard : ((s : ℕ) : ℝ) ≤ (s : ℝ) := le_rfl
  obtain ⟨hpiv, hent⟩ := stg_sizes (rdP P) (mRule P K) η' hrd' _ 3 s hμ (by norm_num) hmul
    (gvM P (foldZ s wd aZ)) 0 s (9 / 4) hcard (by simpa using hA)
    (by have := hm''; nlinarith) (by linarith) m hm
  have hmap : ∀ i l, gv P (stgZ P K (foldZ s wd aZ) m i l) =
      stg (rdP P) (mRule P K) (gvM P (foldZ s wd aZ)) 0 m i l := fun i l => by
    rw [← stgZ_map P K hP]; rfl
  simp only [zero_add] at hpiv hent
  refine ⟨⟨?_, ?_⟩, fun i l hi hl => ?_⟩
  · rw [hmap]; linarith [hpiv.1]
  · rw [hmap]; exact hpiv.2
  · by_cases his : i < s ∧ l < s
    · rw [hmap]; exact hent i l hi his.1 hl his.2
    · rw [stgZ_out P K s _ (fun i j h => by unfold foldZ; rw [if_neg (by omega)]) m i l
        (by omega), gv_zero]
      norm_num

/-- **The factorization fits.** Every window state of the factorization of the folded
Gaussian window matrix satisfies `FacFits` when `(6/β + 1) 2^P < 2^(w-1)`. -/
theorem band_facFits (p : ℕ) (hp : 2 ≤ p) (hP : 2 ≤ P)
    (hinv : StageInv (windowMatrix s wd fun j k => gv P (aZ j k)) univ (1 / (8 * (2 * (p : ℝ))))
      (9 / 4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1 / (8 * (2 * (p : ℝ))) / 2)
    (hηβ : 5 * (1 / 2 ^ P : ℝ) ≤ 2 * (β / 4) / 9)
    (hK : (1 - β / 4 / 2) ^ (2 ^ K) ≤ 3 * (5 * (1 / 2 ^ P : ℝ)) / (β / 4))
    (hsmall : 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (s : ℝ) ^ 2 * ((1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (w : ℕ) (hw : (6 / β + 1) * 2 ^ P < (2 : ℝ) ^ (w - 1)) (m : ℕ) (hm : m < s) :
    FacFits w P K (facState P K (bandRows wd s aZ) (bandInputs wd s aZ) m) := by
  obtain ⟨hpiv, hent⟩ := band_stgZ_sizes p hp hP hinv β hβ hβp hηβ hK hsmall m hm
  set Z := stgZ P K (foldZ s wd aZ) m with hZ
  set C : ℝ := 6 / β + 1
  have hβ1 : β ≤ 1 := hβp.trans (by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    rw [div_div, div_le_one (by positivity)]; nlinarith)
  have h3C : (3 : ℝ) ≤ C := by
    have : 6 ≤ 6 / β := by rw [le_div_iff₀ hβ]; linarith
    simp only [C]; linarith
  have h2C : 2 / β ≤ C := by
    have : 0 ≤ 4 / β := by positivity
    have e : 6 / β = 2 / β + 4 / β := by ring
    simp only [C]; linarith
  have hη1 : (1 / 2 ^ P : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  set c := Z m m
  have hc0 : 0 < gv P c := lt_of_lt_of_le hβ hpiv.1
  have hnew : ∀ n, 0 ≤ gv P c * gv P (newtonZ P c n) ∧ gv P c * gv P (newtonZ P c n) ≤ 2 ∧
      |gv P (newtonZ P c n)| ≤ 2 / β := by
    intro n
    have h := NewtonRecip.newtonR_range (rdP P) _ (rdP_err P) β (gv P c) hβ hpiv.1 hpiv.2 hηβ n
    rw [newtonZ_eq P hP c n] at h
    have hr0 : 0 ≤ gv P (newtonZ P c n) := by
      by_contra hneg; have := not_le.mp hneg; nlinarith
    have hβr : β * gv P (newtonZ P c n) ≤ 2 :=
      le_trans (mul_le_mul_of_nonneg_right hpiv.1 hr0) h.2
    refine ⟨h.1, h.2, ?_⟩
    rw [abs_of_nonneg hr0, le_div_iff₀ hβ]; linarith
  have hrd : ∀ a r : ℤ, |gv P ((a * r).tdiv (2 ^ P))| ≤ |gv P a * gv P r| + 1 := by
    intro a r
    have e := rdP_mul_grid P a r
    have h := rdP_err P (gv P a * gv P r)
    simp only [gv] at e h ⊢
    rw [← e]
    have := abs_sub_abs_le_abs_sub (rdP P ((a : ℝ) / 2 ^ P * ((r : ℝ) / 2 ^ P)))
      ((a : ℝ) / 2 ^ P * ((r : ℝ) / 2 ^ P))
    linarith
  have hfit : ∀ z : ℤ, |gv P z| ≤ C → Fits w (⟨z, 0⟩ : GaussianInt) := fun z hz => fits_of_gv hz hw
  rw [bandRows, bandInputs, facState_window P K (2 * wd + 1) hP (foldZ s wd aZ)
    (foldZ_band P s wd aZ) s m hm.le, List.range'_succ, List.map_cons]
  simp only [winRowZ, ← hZ]
  rw [List.range'_succ, List.map_cons]
  refine ⟨hfit _ ((hent m m le_rfl le_rfl).trans h3C), fun n _ => ⟨hfit _ ((hnew n).2.2.trans h2C),
    hfit _ ?_⟩, hfit _ ((hnew K).2.2.trans h2C), fun a ha => ?_, fun row hrow => ?_⟩
  · refine (hrd _ _).trans ?_
    rw [abs_of_nonneg (hnew n).1]; linarith [(hnew n).2.1]
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    exact hfit _ ((hent m l le_rfl (by have := List.mem_range'_1.mp hl; omega)).trans h3C)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    have hi' := List.mem_range'_1.mp hi
    have hh : (winRowZ (2 * wd + 1) Z m i).headD 0 = Z i m := by
      rw [winRowZ, List.range'_succ, List.map_cons, List.headD_cons]
    simp only [facMul, hh]
    refine ⟨hfit _ ((hent i m (by omega) le_rfl).trans h3C), hfit _ ?_⟩
    refine (hrd _ _).trans ?_
    rw [abs_mul]
    have h1 := hent i m (by omega) le_rfl
    have h2 := (hnew K).2.2
    have : |gv P (Z i m)| * |gv P (newtonZ P c K)| ≤ 3 * (2 / β) :=
      mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    have e6 : 3 * (2 / β) = 6 / β := by ring
    change |gv P (Z i m)| * |gv P (newtonZ P (Z m m) K)| ≤ 3 * (2 / β) at this
    simp only [C]; linarith

end Stages

end IntegerMultBounds.MathlibTM2.Fast
