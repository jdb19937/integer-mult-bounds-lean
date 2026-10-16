module

public import IntegerMultBounds.MathlibTM2.Fast.BandLineSpec
public import IntegerMultBounds.MathlibTM2.Fast.BandAxis
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
    · rw [stgZ_out P K s _ (fun i j h => by unfold foldZ; split_ifs <;> omega) m i l
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

/-- The arithmetic of the line bounds under `2^16 (2p)² s² η ≤ 1`. -/
theorem band_line_arith (p s η : ℝ) (hp : 2 ≤ p) (hs : 1 ≤ s) (hη : 0 ≤ η)
    (hsmall : 2 ^ 16 * (2 * p) ^ 2 * s ^ 2 * η ≤ 1) :
    9 / 4 + s * (η * (s + 3)) ≤ 3 ∧ (s + 3 + 2 * (3 * η) * 3) * η ≤ 1 / 2 ∧
      2 * (3 * η) * 3 * (8 * p + 1) ≤ 1 / 2 := by
  have hq : (16 : ℝ) ≤ (2 * p) ^ 2 := by nlinarith
  have h0 : 0 ≤ s ^ 2 * η := by positivity
  have hs2 : s ^ 2 * η * 2 ^ 20 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ s ^ 2 * η * 2 ^ 16)
    nlinarith
  have hs1' : (1 : ℝ) ≤ s ^ 2 := by nlinarith
  have hp2 : p ^ 2 * η * 2 ^ 18 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hs1' (by positivity : (0 : ℝ) ≤ p ^ 2 * η * 2 ^ 18)
    nlinarith
  have hpη : p * η ≤ p ^ 2 * η := mul_le_mul_of_nonneg_right (by nlinarith) hη
  have hsη : s * η ≤ s ^ 2 * η := mul_le_mul_of_nonneg_right (by nlinarith) hη
  have hηs : η ≤ s ^ 2 * η := le_mul_of_one_le_left hη hs1'
  have hηη : η * η ≤ η := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

section Line

/-- The forward values of the numerator line solve are the forward substitution of the
machine-rule band solve in natural order. -/
theorem lineFwd_eq (P K B s : ℕ) (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ) (hA : BandFrom B (gvM P AZ) 0)
    (hout : ∀ i j, (s ≤ i ∨ s ≤ j) → AZ i j = 0) (bZ : List ℤ) (hlen : bZ.length = s) :
    (fwdZ P ((factorRowsZ P K (windowZ B AZ) (inputsZ B AZ s)).map Prod.fst)
      (bZ ++ List.replicate B 0)).map (gv P) =
      (List.range' 0 s).map (fwdM (rdP P) (luLr (rdP P) (mRule P K) (gvM P AZ) (Ico 0 s)
        (List.range' 0 s)) (fun i => gv P (bZ.getD i 0)) ∅ (fun _ => 0) (List.range' 0 s)) := by
  set ks := List.range' 0 s with hks
  have hnd : ks.Nodup := List.nodup_range'
  have hfac := factorRowsZ_run P K B hP AZ hA s
  have hLc : (factorRowsZ P K (windowZ B AZ) (inputsZ B AZ s)).map Prod.fst =
      (cols (LzN P K s AZ) ks).map (padCol B) := by
    rw [hfac, List.map_map, lcols_eq P K B s AZ hout]; rfl
  have hlenk : bZ.length = ks.length := by rw [hlen, hks, List.length_range']
  rw [hLc, fwdZ_pad P B (LzN P K s AZ) ks (banded_LzN P K B s hP AZ hA hout) bZ hlenk]
  have hbZ : bZ = ks.map fun i => bZ.getD i 0 := by rw [hks, ← hlen, range'_getD]
  have h1 := fwdZ_eq P (luLr (rdP P) (mRule P K) (gvM P AZ) (Ico 0 s) ks) (LzN P K s AZ)
    (fun i k => luLr_natural P K s hP AZ i k) ks hnd (fun _ => 0) (fun i => bZ.getD i 0)
  rw [← hbZ] at h1
  have h2 := colFwd_eq (rdP P) (luLr (rdP P) (mRule P K) (gvM P AZ) (Ico 0 s) ks)
    (fun i => gv P (bZ.getD i 0)) ks hnd ∅ (fun _ => 0) (fun i => ((bZ.getD i 0 : ℤ) : ℝ) / 2 ^ P)
    (fun k _ => Finset.notMem_empty k) (fun k _ => by simp [gv])
  exact h1.trans (by rw [h2])

variable {P K wd s : ℕ} [NeZero s] {aZ : ZMod s → ℤ → ℤ}

/-- **Sizes of the line solve.** For a right-hand side of grid values at most `1/2`, the
computed solution is at most `8p + 1` and every forward value at most `3(8p + 1) + 1`. -/
theorem band_line_sizes (p : ℕ) (hp : 2 ≤ p) (hP : 2 ≤ P)
    (hinv : StageInv (windowMatrix s wd fun j k => gv P (aZ j k)) univ (1 / (8 * (2 * (p : ℝ))))
      (9 / 4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1 / (8 * (2 * (p : ℝ))) / 2)
    (hηβ : 5 * (1 / 2 ^ P : ℝ) ≤ 2 * (β / 4) / 9)
    (hK : (1 - β / 4 / 2) ^ (2 ^ K) ≤ 3 * (5 * (1 / 2 ^ P : ℝ)) / (β / 4))
    (hsmall : 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (s : ℝ) ^ 2 * ((1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (hE : 62000 * (2 * (p : ℝ)) ^ 3 * (s : ℝ) ^ 2 * ((1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (bZ : List ℤ) (hlen : bZ.length = s) (hb : ∀ i < s, |gv P (bZ.getD i 0)| ≤ 1 / 2) :
    (∀ i < s, |gv P ((lineSolveZ P K (2 * wd + 1) s (foldZ s wd aZ) bZ).getD i 0)| ≤ 8 * p + 1) ∧
      ∀ i < s, |gv P ((fwdZ P (bandLc P K wd s aZ) (bZ ++ List.replicate (2 * wd + 1) 0)).getD i 0)|
        ≤ 3 * (8 * p + 1) + 1 := by
  set η : ℝ := 1 / 2 ^ P
  have hη : 0 ≤ η := by positivity
  set η' := η * (1 + 60 * 3 / β ^ 2) with hη'
  have hle : η ≤ η' := by
    have : 0 ≤ η * (60 * 3 / β ^ 2) := by positivity
    nlinarith
  have hη'0 : 0 ≤ η' := by positivity
  have hrd' : ∀ x, |rdP P x - x| ≤ η' := fun x => (rdP_err P x).trans (by simpa [η] using hle)
  have hrd0 := rdP_zero P
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (2 : ℝ) ≤ 2 * (p : ℝ) := by linarith
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hμ : (0 : ℝ) < 1 / (8 * (2 * (p : ℝ))) := by positivity
  set At := windowMatrix s wd fun j k => gv P (aZ j k)
  set b : ZMod s → ℝ := fun a => gv P (bZ.getD (foldPos s a) 0)
  obtain ⟨R, hR⟩ := exists_solver At univ _ hμ hinv.1
  set xt := R b
  have hxt := hR b
  have hcard : ((univ : Finset (ZMod s)).card : ℝ) ≤ s := by simp [ZMod.card]
  have hlenO := foldOrder_length s
  have hX : ∀ i ∈ (univ : Finset (ZMod s)), |xt i| ≤ 4 * (2 * (p : ℝ)) := by
    intro i hi
    have h := solves_bound _ _ _ hμ hinv.1 xt b hxt (1 / 2)
      (fun i _ => hb _ (foldPos_lt s i)) i hi
    rw [div_div_eq_mul_div, div_one] at h
    linarith
  obtain ⟨hm', hmu', hMη, hsm', hfin⟩ :=
    bandM_arith (2 * (p : ℝ)) (s : ℝ) η' hqR hs1 hη'0 hsmall
  obtain ⟨hA0, hA1, hA2⟩ := band_line_arith (p : ℝ) (s : ℝ) η' hpR hs1 hη'0 hsmall
  have hm'' : 9 / 4 + (foldOrder s).length * (η' * (s + 3)) ≤ 3 := by rw [hlenO]; exact hA0
  have hmul := NewtonRecip.recipMul_err (rdP P) η (rdP_err P) 3 β (by norm_num) hβ hηβ K hK
  have hagree : ∀ a c, |a| ≤ 3 → 1 / (8 * (2 * (p : ℝ))) / 2 ≤ c → c ≤ 3 →
      PhaseCellMatrix.machMul (rdP P) K a c = NewtonRecip.recipMul (rdP P) 3 β K a c :=
    fun a c ha hc hc3 => by
      simp only [machMul, NewtonRecip.recipMul, hβp.trans hc, hc3, ha, and_self, ite_true]
  have hrecA : ∀ c, 1 / (8 * (2 * (p : ℝ))) / 2 ≤ c → c ≤ 3 →
      NewtonRecip.newtonR (rdP P) c K = NewtonRecip.recipNewton (rdP P) β K c := fun c hc hc3 => by
    simp only [NewtonRecip.recipNewton, hβp.trans hc, hc3, and_self, ite_true]
  have hrec : ∀ c, 1 / (8 * (2 * (p : ℝ))) / 2 ≤ c → c ≤ 3 →
      |c * NewtonRecip.recipNewton (rdP P) β K c - 1| ≤ 3 * η' := fun c hc hc3 => by
    have h := NewtonRecip.recipNewton_residual (rdP P) η (rdP_err P) β hβ hηβ K hK c (hβp.trans hc) hc3
    have e : 3 * (η * (1 + 60 * 3 / β ^ 2)) = 3 * η + 3 * (180 * η / β ^ 2) := by ring
    have h0 : 0 ≤ 180 * η / β ^ 2 := by positivity
    rw [hη', e]; linarith
  obtain ⟨hsol, hfwd, -⟩ := bandSolveG_sizes (rdP P) (NewtonRecip.recipMul (rdP P) 3 β K)
    (NewtonRecip.recipNewton (rdP P) β K) η' (3 * η') hrd' hrd0 hmul
    (NewtonRecip.recipMul_zero (rdP P) hrd0 3 β K) (foldPos s) (foldPos_injective s) At univ _ (9 / 4)
    3 s hμ (by norm_num) (by norm_num) hinv hcard (foldOrder s) (foldOrder_toFinset s)
    (foldOrder_sorted s) hm'' (by rw [hlenO]; exact hmu') hrec hMη xt b hxt _ (by positivity) hX
    (by rw [hlenO]; exact hsm') (8 * p + 1) (by rw [hlenO]; linarith [hfin, hE])
  -- machine rules agree with the analysed ones
  have hcongr := bandSolveG_congr (rdP P) (NewtonRecip.recipMul (rdP P) 3 β K) η' hrd' hmul
    (machMul (rdP P) K) (NewtonRecip.recipNewton (rdP P) β K) (fun c => NewtonRecip.newtonR (rdP P) c K)
    At univ _ (9 / 4) 3 s hμ (by norm_num) (by norm_num) hinv hcard (foldOrder s)
    (foldOrder_toFinset s) hm'' (by rw [hlenO]; exact hmu') hagree hrecA b
  have hL := lur_congr (rdP P) (NewtonRecip.recipMul (rdP P) 3 β K) η' hrd' hmul (machMul (rdP P) K)
    _ 3 s hμ (by norm_num) (by linarith) hagree (foldOrder s) At At univ _ (9 / 4) hinv
    (fun _ _ _ => rfl) hcard (by norm_num) hm'' (by rw [hlenO]; linarith)
  have hgetD : ∀ (l : List ℤ) (i : ℕ), gv P (l.getD i 0) = (l.map (gv P)).getD i 0 := by
    intro l i
    by_cases h : i < l.length
    · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using h), gv_zero]
  have hrange : ∀ (F : ℕ → ℝ) (i : ℕ), i < s → ((List.range' 0 s).map F).getD i 0 = F i :=
    fun F i hi => by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range']
      simp
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hgetD, lineSolveFold_eq P K s hP wd aZ bZ hlen, hrange _ i hi]
    have e : Mult.FastB0.machSolveT K (rdP P) At (fun a => gv P (bZ.getD (foldPos s a) 0)) (foldAt s i) =
        bandSolveG (rdP P) (NewtonRecip.recipMul (rdP P) 3 β K) (NewtonRecip.recipNewton (rdP P) β K)
          At univ (foldOrder s) b (foldAt s i) := by
      rw [← hcongr]; rfl
    rw [e]; exact hsol _ (mem_univ _)
  · have hband := foldZ_band P s wd aZ
    have hout : ∀ i j, (s ≤ i ∨ s ≤ j) → foldZ s wd aZ i j = 0 := fun i j h => by
      unfold foldZ; split_ifs <;> omega
    rw [hgetD, show bandLc P K wd s aZ = (factorRowsZ P K (windowZ (2 * wd + 1) (foldZ s wd aZ))
      (inputsZ (2 * wd + 1) (foldZ s wd aZ) s)).map Prod.fst from rfl,
      lineFwd_eq P K (2 * wd + 1) s hP (foldZ s wd aZ) hband hout bZ hlen, hrange _ i hi]
    have hlu := lur_map (rdP P) (mRule P K) (foldPos s) (foldPos_injective s) (foldOrder s) At
      (gvM P (foldZ s wd aZ)) univ (fun a c => by
        simp only [gvM, foldZ, foldPos_lt, and_self, ite_true, foldAt_foldPos]
        exact wmZ_gv P s wd aZ a c)
    have hmap := fwdM_map (rdP P) (foldPos s) (foldPos_injective s)
      (luLr (rdP P) (mRule P K) At univ (foldOrder s))
      (luLr (rdP P) (mRule P K) (gvM P (foldZ s wd aZ)) (univ.image (foldPos s))
        ((foldOrder s).map (foldPos s))) (fun a c => (hlu a c).1) b
      (fun i => gv P (bZ.getD i 0)) (fun _ => rfl) (foldOrder s) ∅ (fun _ => 0) (fun _ => 0)
      (fun _ => rfl) (foldAt s i)
    rw [image_foldPos, foldOrder_map_foldPos, image_empty, foldPos_foldAt s i hi] at hmap
    rw [hmap]
    have hLe : luLr (rdP P) (mRule P K) At univ (foldOrder s) =
        luLr (rdP P) (NewtonRecip.recipMul (rdP P) 3 β K) At univ (foldOrder s) := by
      funext a c; exact (hL a (mem_univ a) c).1
    rw [hLe]
    have h := hfwd _ (mem_univ (foldAt s i))
    linarith

end Line

section LineOk

theorem bandOut_rev_getD (P : ℕ) (cs : List (List ℤ)) (pend : List GaussianInt) :
    ∀ n j, j < n → (bandOut P cs pend n).reverse.getD j 0 = (bandPend P cs pend j).headD 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, h => by
    rw [bandOut, List.reverse_cons]
    by_cases hj : j < n
    · rw [List.getD_append _ _ _ _ (by rw [List.length_reverse, length_bandOut]; exact hj)]
      exact bandOut_rev_getD P cs pend n j hj
    · have e : j = n := by omega
      subst e
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_reverse, length_bandOut]),
        List.length_reverse, length_bandOut, Nat.sub_self]
      rfl

theorem bandOutB_rev_getD (P : ℕ) (cs : List (List ℤ)) (rs : List ℤ) (pend : List GaussianInt) :
    ∀ n j, j < n → (bandOutB P cs rs pend n).reverse.getD j 0 =
      tdivN P ((bandPendB P cs rs pend j).headD 0 * ⟨rs.getD j 0, 0⟩)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, h => by
    rw [bandOutB, List.reverse_cons]
    by_cases hj : j < n
    · rw [List.getD_append _ _ _ _ (by rw [List.length_reverse, length_bandOutB]; exact hj)]
      exact bandOutB_rev_getD P cs rs pend n j hj
    · have e : j = n := by omega
      subst e
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_reverse, length_bandOutB]),
        List.length_reverse, length_bandOutB, Nat.sub_self]
      rfl

theorem re_getD (l : List GaussianInt) (i : ℕ) : (l.getD i 0).re = (l.map (·.re)).getD i 0 := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using h)]; rfl

theorem im_getD (l : List GaussianInt) (i : ℕ) : (l.getD i 0).im = (l.map (·.im)).getD i 0 := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using h)]; rfl

theorem abs_gv_tdiv (P : ℕ) (x : ℤ) (Q : ℕ) :
    |gv P (x.tdiv (2 ^ Q))| ≤ |gv P x| / 2 ^ Q := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hQ : (0 : ℝ) < 2 ^ Q := by positivity
  have h := NLogN.abs_rho0_le ((x : ℝ) / 2 ^ Q)
  rw [abs_div, abs_of_pos hQ] at h
  rw [tdiv_rho0, gv, gv, abs_div, abs_div, abs_of_pos hP, div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right h hP.le

/-- A complex numerator whose grid parts are at most `C` fits when `C 2^P < 2^(w-1)`. -/
theorem fitsC_of_gv {w P : ℕ} {z : GaussianInt} {C : ℝ} (hre : |gv P z.re| ≤ C)
    (him : |gv P z.im| ≤ C) (hC : C * 2 ^ P < 2 ^ (w - 1)) : Fits w z :=
  ⟨(fits_of_gv hre hC).1, (fits_of_gv him hC).1⟩

theorem mem_of_mem_unfoldList {α : Type*} {a : α} (l : List α) (h : a ∈ unfoldList l) : a ∈ l := by
  rcases List.mem_append.mp h with h | h
  · exact mem_of_mem_evens l h
  · exact mem_of_mem_odds l (List.mem_reverse.mp h)

theorem getD_mem_or (l : List GaussianInt) (k : ℕ) : l.getD k 0 ∈ l ∨ l.getD k 0 = 0 := by
  by_cases h : k < l.length
  · exact Or.inl (by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
  · exact Or.inr (List.getD_eq_default _ _ (by omega))

/-- The scaled input of a line of grid values at most `1` has grid parts at most `1/2`. -/
theorem bandInVec_bound (P p s t : ℕ) [NeZero s] (hpP : p + 1 ≤ P) (L : List GaussianInt)
    (hLb : ∀ x ∈ L, |x.re| ≤ 2 ^ p ∧ |x.im| ≤ 2 ^ p) :
    ∀ a ∈ bandInVec P s t (2 ^ (2 * P - p - 1)) (rsbVec (t := t) L),
      |gv P a.re| ≤ 1 / 2 ∧ |gv P a.im| ≤ 1 / 2 := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  have hx' := mem_of_mem_foldList x _ hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx'
  have hb : |(rsbVec (t := t) L (rowIndex s t (i : ZMod s))).re| ≤ 2 ^ p ∧
      |(rsbVec (t := t) L (rowIndex s t (i : ZMod s))).im| ≤ 2 ^ p := by
    simp only [rsbVec]
    rcases getD_mem_or L ((rowIndex s t (i : ZMod s)).val) with h | h
    · exact hLb _ h
    · rw [h]; simp
  set x := rsbVec (t := t) L (rowIndex s t (i : ZMod s))
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have e : (2 : ℝ) ^ p * 2 ^ (2 * P - p - 1) * 2 = 2 ^ P * 2 ^ P := by
    rw [← pow_add, ← pow_succ, ← pow_add]; congr 1; omega
  have key : ∀ y : ℤ, |y| ≤ 2 ^ p → |gv P ((y * 2 ^ (2 * P - p - 1)).tdiv (2 ^ P))| ≤ 1 / 2 := by
    intro y hy
    refine (abs_gv_tdiv P _ P).trans ?_
    have hyR : |(y : ℝ)| ≤ 2 ^ p := by exact_mod_cast hy
    rw [gv, abs_div, abs_of_pos hP, div_div, div_le_iff₀ (by positivity)]
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (2 * P - p - 1))]
    nlinarith [mul_le_mul_of_nonneg_right hyR (by positivity : (0 : ℝ) ≤ 2 ^ (2 * P - p - 1))]
  refine ⟨?_, ?_⟩
  · rw [tdivN_re, mul_real_re]; exact key _ hb.1
  · rw [tdivN_im, mul_real_im]; exact key _ hb.2

variable {P K wd s : ℕ} [NeZero s] {aZ : ZMod s → ℤ → ℤ}

/-- The stored reciprocals of the pivots are at least `1/4`. -/
theorem band_rcs_lb (p : ℕ) (hp : 2 ≤ p) (hP : 2 ≤ P)
    (hinv : StageInv (windowMatrix s wd fun j k => gv P (aZ j k)) univ (1 / (8 * (2 * (p : ℝ))))
      (9 / 4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1 / (8 * (2 * (p : ℝ))) / 2)
    (hηβ : 5 * (1 / 2 ^ P : ℝ) ≤ 2 * (β / 4) / 9)
    (hK : (1 - β / 4 / 2) ^ (2 ^ K) ≤ 3 * (5 * (1 / 2 ^ P : ℝ)) / (β / 4))
    (hsmall : 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (s : ℝ) ^ 2 * ((1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (j : ℕ) (hj : j < s) : 1 / 4 ≤ gv P ((bandRcs P K wd s aZ).getD j 0) := by
  have hfac := factorRowsZ_run P K (2 * wd + 1) hP (foldZ s wd aZ) (foldZ_band P s wd aZ) s
  have hm : s - 1 - j < s := by omega
  obtain ⟨hpiv, -⟩ := band_stgZ_sizes p hp hP hinv β hβ hβp hηβ hK hsmall (s - 1 - j) hm
  set c := stgZ P K (foldZ s wd aZ) (s - 1 - j) (s - 1 - j) (s - 1 - j)
  have e : (bandRcs P K wd s aZ).getD j 0 = newtonZ P c K := by
    rw [bandRcs, bandFac, hfac, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_reverse]
    simp [winRowZ, List.range'_succ, c]
  rw [e, ← newtonZ_eq P hP c K]
  have h := NewtonRecip.newtonR_recip (rdP P) _ (rdP_err P) β (gv P c) hβ hpiv.1 hpiv.2 hηβ K hK
  have hc0 : 0 < gv P c := lt_of_lt_of_le hβ hpiv.1
  have h13 : 1 / 3 ≤ 1 / gv P c := one_div_le_one_div_of_le hc0 hpiv.2
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hsmall' : 60 * (1 / 2 ^ P : ℝ) / β ^ 2 ≤ 1 / 12 := by
    have hη : (0 : ℝ) ≤ 1 / 2 ^ P := by positivity
    have h1 : 60 * (1 / 2 ^ P : ℝ) / β ^ 2 ≤ (1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2) := by
      have : 0 ≤ (1 / 2 ^ P : ℝ) * (60 * 2 / β ^ 2) := by positivity
      have e2 : (1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2) =
          (1 / 2 ^ P : ℝ) + 60 * (1 / 2 ^ P : ℝ) / β ^ 2 + (1 / 2 ^ P : ℝ) * (60 * 2 / β ^ 2) := by
        ring
      linarith
    have h2 : (12 : ℝ) ≤ 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (s : ℝ) ^ 2 := by
      have h4 : (1 : ℝ) ≤ (2 * (p : ℝ)) ^ 2 := by nlinarith
      have h5 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
      have : (1 : ℝ) ≤ (2 * (p : ℝ)) ^ 2 * (s : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le h4 h5
      nlinarith
    have h3 : 0 ≤ (1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_right h2 h3
    linarith
  have := (abs_le.mp h).1
  linarith

theorem proj_getD (π : GaussianInt → ℤ) (hπ0 : π 0 = 0) (l : List GaussianInt) (i : ℕ) :
    π (l.getD i 0) = (l.map π).getD i 0 := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using h), hπ0]

theorem length_bandLc (hP : 2 ≤ P) : (bandLc P K wd s aZ).length = s := by
  rw [bandLc, bandFac, factorRowsZ_run P K (2 * wd + 1) hP (foldZ s wd aZ) (foldZ_band P s wd aZ) s]
  simp

theorem length_bandUc : (bandUc P K wd s aZ).length = s := by simp [bandUc]

theorem length_bandRcs (hP : 2 ≤ P) : (bandRcs P K wd s aZ).length = s := by
  rw [bandRcs, bandFac, factorRowsZ_run P K (2 * wd + 1) hP (foldZ s wd aZ) (foldZ_band P s wd aZ) s]
  simp

/-- **The values of one part of a line.** For a projection `π` (real or imaginary part) and an
input whose parts are at most `1/2`, the forward heads, the back heads, the solution and the
scaled outputs of the tape line have grid values within `4(8p + 2)`. -/
theorem band_line_part (π : GaussianInt → ℤ) (hπ0 : π 0 = 0)
    (hfwd : ∀ cs pend, (fwdZC P cs pend).map π = fwdZ P cs (pend.map π))
    (hsolv : ∀ b, (bandSolveVec P (2 * wd + 1) (bandLc P K wd s aZ) (bandUc P K wd s aZ)
      (bandRcs P K wd s aZ) b).map π = lineSolveZ P K (2 * wd + 1) s (foldZ s wd aZ) (b.map π))
    (htd : ∀ z, π (tdivN P z) = (π z).tdiv (2 ^ P)) (hmulr : ∀ z c, π (z * ⟨c, 0⟩) = π z * c)
    (p : ℕ) (hp : 2 ≤ p) (hP : 2 ≤ P)
    (hinv : StageInv (windowMatrix s wd fun j k => gv P (aZ j k)) univ (1 / (8 * (2 * (p : ℝ))))
      (9 / 4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1 / (8 * (2 * (p : ℝ))) / 2)
    (hηβ : 5 * (1 / 2 ^ P : ℝ) ≤ 2 * (β / 4) / 9)
    (hK : (1 - β / 4 / 2) ^ (2 ^ K) ≤ 3 * (5 * (1 / 2 ^ P : ℝ)) / (β / 4))
    (hsmall : 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (s : ℝ) ^ 2 * ((1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (hE : 62000 * (2 * (p : ℝ)) ^ 3 * (s : ℝ) ^ 2 * ((1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (bin : List GaussianInt) (hlen : bin.length = s) (hbin : ∀ a ∈ bin, |gv P (π a)| ≤ 1 / 2)
    (Q : ℕ) (hQ : Q ≤ P) :
    (∀ j < s, |gv P (π ((bandPend P (bandLc P K wd s aZ) (bin ++ List.replicate (2 * wd + 1) 0)
      j).headD 0))| ≤ 3 * (8 * p + 1) + 1) ∧
    (∀ j < s, |gv P (π ((bandPendB P (bandUc P K wd s aZ) (bandRcs P K wd s aZ)
      ((fwdZC P (bandLc P K wd s aZ) (bin ++ List.replicate (2 * wd + 1) 0)).reverse ++
        List.replicate (2 * wd + 1) 0) j).headD 0))| ≤ 4 * (8 * p + 2)) ∧
    (∀ j < s, |gv P (π (tdivN P ((bandPendB P (bandUc P K wd s aZ) (bandRcs P K wd s aZ)
      ((fwdZC P (bandLc P K wd s aZ) (bin ++ List.replicate (2 * wd + 1) 0)).reverse ++
        List.replicate (2 * wd + 1) 0) j).headD 0 * ⟨(bandRcs P K wd s aZ).getD j 0, 0⟩)))| ≤
          8 * p + 1) ∧
    (∀ a ∈ unfoldList (bandSolveVec P (2 * wd + 1) (bandLc P K wd s aZ) (bandUc P K wd s aZ)
      (bandRcs P K wd s aZ) bin), |gv P (π a)| ≤ 8 * p + 1 ∧
        |gv P (π (tdivN P (a * ⟨2 ^ Q, 0⟩)))| ≤ 8 * p + 1) := by
  set B := 2 * wd + 1
  set Lc := bandLc P K wd s aZ
  set Uc := bandUc P K wd s aZ
  set rcs := bandRcs P K wd s aZ
  set bZ := bin.map π
  have hbZlen : bZ.length = s := by simp [bZ, hlen]
  have hb : ∀ i < s, |gv P (bZ.getD i 0)| ≤ 1 / 2 := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by rw [hbZlen]; exact hi), List.getElem_map]
    exact hbin _ (List.getElem_mem _)
  obtain ⟨hsolB, hfwdB⟩ := band_line_sizes p hp hP hinv β hβ hβp hηβ hK hsmall hE bZ hbZlen hb
  have hLc : Lc.length = s := length_bandLc hP
  have hUc : Uc.length = s := length_bandUc
  have hrcs : rcs.length = s := length_bandRcs hP
  set pend := bin ++ List.replicate B 0
  have hpend : pend.map π = bZ ++ List.replicate B 0 := by simp [pend, bZ, hπ0]
  have hplen : pend.length = s + B := by simp [pend, hlen]
  have hfwdC := fwdZC_eq_bandOut P Lc pend (by rw [hLc, hplen]; omega)
  have hfwdlen : (fwdZC P Lc pend).length = s := by rw [hfwdC]; simp [length_bandOut, hLc]
  set pend' := (fwdZC P Lc pend).reverse ++ List.replicate B 0
  have hp'len : pend'.length = s + B := by simp [pend', hfwdlen]
  have hbwdC := bwdZC_eq_bandOutB P Uc rcs pend' (by rw [hUc, hp'len]; omega) (by rw [hUc, hrcs])
  have hsolvlen : (bandSolveVec P B Lc Uc rcs bin).length = s :=
    length_bandSolveVec P K wd s hP aZ bin hlen
  have hsolrev : bwdZC P Uc rcs pend' =
      (bandSolveVec P B Lc Uc rcs bin).reverse := by
    simp only [bandSolveVec, List.reverse_reverse]; rfl
  have hsolπ : (bandSolveVec P B Lc Uc rcs bin).map π = lineSolveZ P K B s (foldZ s wd aZ) bZ :=
    hsolv bin
  have hlslen : (lineSolveZ P K B s (foldZ s wd aZ) bZ).length = s := by
    rw [← hsolπ, List.length_map, hsolvlen]
  -- the solution entries
  have hsolE : ∀ a ∈ bandSolveVec P B Lc Uc rcs bin, |gv P (π a)| ≤ 8 * p + 1 := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have h := hsolB i (by rw [hsolvlen] at hi; exact hi)
    rw [← hsolπ, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map] at h
    exact h
  -- the outputs of the back pass
  have hout : ∀ j < s, tdivN P ((bandPendB P Uc rcs pend' j).headD 0 * ⟨rcs.getD j 0, 0⟩) =
      (bwdZC P Uc rcs pend').getD j 0 := fun j hj => by
    rw [hbwdC, bandOutB_rev_getD P Uc rcs pend' _ j (by rw [hUc]; exact hj)]
  have houtB : ∀ j < s, |gv P (π (tdivN P ((bandPendB P Uc rcs pend' j).headD 0 *
      ⟨rcs.getD j 0, 0⟩)))| ≤ 8 * p + 1 := fun j hj => by
    rw [hout j hj, hsolrev, List.getD_eq_getElem _ _ (by simpa [hsolvlen] using hj)]
    exact hsolE _ (List.mem_reverse.mp (List.getElem_mem _))
  refine ⟨fun j hj => ?_, fun j hj => ?_, houtB, fun a ha => ?_⟩
  · rw [← bandOut_rev_getD P Lc pend s j hj, ← hLc, ← hfwdC, proj_getD π hπ0, hfwd, hpend]
    exact hfwdB j hj
  · have h := houtB j hj
    rw [htd, hmulr] at h
    set q := π ((bandPendB P Uc rcs pend' j).headD 0)
    have hr := band_rcs_lb (aZ := aZ) (K := K) p hp hP hinv β hβ hβp hηβ hK hsmall j hj
    have e := rdP_mul_grid P q (rcs.getD j 0)
    have herr := rdP_err P (gv P q * gv P (rcs.getD j 0))
    simp only [gv] at h hr herr e ⊢
    rw [← e] at h
    have hη1 : (1 : ℝ) / 2 ^ P ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have h1 : |(q : ℝ) / 2 ^ P * ((rcs.getD j 0 : ℤ) / 2 ^ P)| ≤ 8 * p + 2 := by
      have := abs_sub_abs_le_abs_sub ((q : ℝ) / 2 ^ P * ((rcs.getD j 0 : ℤ) / 2 ^ P))
        (rdP P ((q : ℝ) / 2 ^ P * ((rcs.getD j 0 : ℤ) / 2 ^ P)))
      rw [abs_sub_comm] at this
      linarith
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < (rcs.getD j 0 : ℤ) / 2 ^ P)] at h1
    have h0 : 0 ≤ |(q : ℝ) / 2 ^ P| := abs_nonneg _
    nlinarith
  · have ha' := mem_of_mem_unfoldList _ ha
    have h1 := hsolE a ha'
    refine ⟨h1, ?_⟩
    rw [htd, hmulr]
    refine (abs_gv_tdiv P _ P).trans ?_
    have hQP : (2 : ℝ) ^ Q ≤ 2 ^ P := pow_le_pow_right₀ (by norm_num) hQ
    have e : gv P (π a * 2 ^ Q) = gv P (π a) * 2 ^ Q := by simp [gv]; ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ Q), div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ |gv P (π a)| := abs_nonneg _
    exact mul_le_mul h1 hQP (by positivity) (by positivity)

/-- **Every line of grid values at most `1` meets the record widths of the band line.** -/
theorem band_lineOk (p j t : ℕ) (hp : 2 ≤ p) (hpP : p + 1 ≤ P) (hjp : j ≤ p)
    (hinv : StageInv (windowMatrix s wd fun j k => gv P (aZ j k)) univ (1 / (8 * (2 * (p : ℝ))))
      (9 / 4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1 / (8 * (2 * (p : ℝ))) / 2)
    (hηβ : 5 * (1 / 2 ^ P : ℝ) ≤ 2 * (β / 4) / 9)
    (hK : (1 - β / 4 / 2) ^ (2 ^ K) ≤ 3 * (5 * (1 / 2 ^ P : ℝ)) / (β / 4))
    (hsmall : 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (s : ℝ) ^ 2 * ((1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (hE : 62000 * (2 * (p : ℝ)) ^ 3 * (s : ℝ) ^ 2 * ((1 / 2 ^ P : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (w : ℕ) (hw : (6 / β + 1) * 2 ^ P < (2 : ℝ) ^ (w - 1))
    (L : List GaussianInt) (hL : L.length = t) (hLb : ∀ x ∈ L, |x.re| ≤ 2 ^ p ∧ |x.im| ≤ 2 ^ p) :
    BandLineOk w P s t (2 * wd + 1) (bandLc P K wd s aZ) (bandUc P K wd s aZ) (bandRcs P K wd s aZ)
      (2 ^ (2 * P - p - 1)) (2 ^ (p - j)) L := by
  have hP : 2 ≤ P := by omega
  set C : ℝ := 6 / β + 1
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h32 : 32 * (p : ℝ) ≤ 1 / β := by
    rw [le_div_iff₀ hβ]
    have := mul_le_mul_of_nonneg_right hβp (by positivity : (0 : ℝ) ≤ 32 * p)
    have e : 1 / (8 * (2 * (p : ℝ))) / 2 * (32 * p) = 1 := by field_simp; ring
    linarith
  have hC : 4 * (8 * (p : ℝ) + 2) ≤ C := by
    have e : 6 / β = 6 * (1 / β) := by ring
    simp only [C]; rw [e]; nlinarith
  have hC1 : 3 * (8 * (p : ℝ) + 1) + 1 ≤ C := by linarith
  have hC2 : 8 * (p : ℝ) + 1 ≤ C := by linarith
  have hin := bandInVec_bound P p s t hpP L hLb
  have hlen : (bandInVec P s t (2 ^ (2 * P - p - 1)) (rsbVec (t := t) L)).length = s := by
    simp [bandInVec, length_foldList, length_rsbArr]
  have hQ : p - j ≤ P := by omega
  obtain ⟨r1, r2, r3, r4⟩ := band_line_part (·.re) rfl (fun cs pend => fwdZC_re P cs pend)
    (bandSolveVec_re_eq P K wd s aZ) (fun z => rfl) (fun z c => mul_real_re z c) p hp hP hinv β hβ
    hβp hηβ hK hsmall hE _ hlen (fun a ha => (hin a ha).1) (p - j) hQ
  obtain ⟨i1, i2, i3, i4⟩ := band_line_part (·.im) rfl (fun cs pend => fwdZC_im P cs pend)
    (bandSolveVec_im_eq P K wd s aZ) (fun z => rfl) (fun z c => mul_real_im z c) p hp hP hinv β hβ
    hβp hηβ hK hsmall hE _ hlen (fun a ha => (hin a ha).2) (p - j) hQ
  have hpow : ((2 : ℤ) ^ (p - j) : ℤ) = 2 ^ (p - j) := rfl
  refine ⟨hL, fun x hx => ?_, fun k hk => fitsC_of_gv ((r1 k hk).trans hC1) ((i1 k hk).trans hC1) hw,
    fun k hk => fitsC_of_gv ((r2 k hk).trans hC) ((i2 k hk).trans hC) hw,
    fun k hk => fitsC_of_gv ((r3 k hk).trans hC2) ((i3 k hk).trans hC2) hw,
    fun a ha => fitsC_of_gv ((r4 a ha).1.trans hC2) ((i4 a ha).1.trans hC2) hw,
    fun a ha => fitsC_of_gv ((r4 a ha).2.trans hC2) ((i4 a ha).2.trans hC2) hw⟩
  have hbound : ∀ y : ℤ, |y| ≤ 2 ^ p → |gv P y| ≤ C := by
    intro y hy
    have hyR : |(y : ℝ)| ≤ 2 ^ p := by exact_mod_cast hy
    have hpP' : (2 : ℝ) ^ p ≤ 2 ^ P := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [gv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ P), div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ C := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 ^ P)]
  exact fitsC_of_gv (hbound _ (hLb x hx).1) (hbound _ (hLb x hx).2) hw

end LineOk

end IntegerMultBounds.MathlibTM2.Fast
