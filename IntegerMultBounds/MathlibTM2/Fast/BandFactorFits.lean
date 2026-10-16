module

public import IntegerMultBounds.MathlibTM2.Fast.BandFactor

/-!
# Record widths of the window factorization

Every number the window factorization stores is the numerator of a value of size
at most `V = 12/β + 4`: stage entries are bounded by the row mass `3`, the pivot
lies in `[β, 3]`, Newton iterates satisfy `0 ≤ c r ≤ 2`, and multipliers are
entries times reciprocals. With `V 2^P < 2^(w-1)` the width conditions
`FacFits` hold at every step.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
open IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandFactor

/-- A numerator whose grid value is at most `V` fits `w` symbols when `V 2^P < 2^(w-1)`. -/
theorem fits_of_gv (P w : ℕ) (x : ℤ) (V : ℝ) (h : |gv P x|≤V) (hV : V*2^P<2^(w-1)) :
    Fits w (⟨x, 0⟩ : GaussianInt) := by
  have hP : (0 : ℝ)<2^P := by positivity
  have hx : |(x : ℝ)|≤V*2^P := by
    have e : (x : ℝ)=gv P x*2^P := by simp [gv]
    rw [e, abs_mul, abs_of_pos hP]
    exact mul_le_mul_of_nonneg_right h hP.le
  refine ⟨?_, ?_⟩
  · have : |(x : ℝ)|<2^(w-1) := lt_of_le_of_lt hx hV
    exact_mod_cast this
  · simp only [abs_zero]; positivity

/-- **Width conditions of the window factorization.** For a banded numerator matrix
vanishing outside `s × s`, whose grid values satisfy the stage invariant budgets for the
guarded Newton rule, every window state of the factorization satisfies `FacFits`. -/
theorem facFits_all (P K B s w : ℕ) (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ)
    (hA : BandFrom B (gvM P AZ) 0) (hout : ∀ i j, (s ≤ i ∨ s ≤ j) → AZ i j=0)
    (β μ n μ₀ m₀ : ℝ) (hβ : 0<β) (hβμ : β≤μ/2) (hμ : 0<μ) (hn : (s : ℝ)≤n)
    (hηβ : 5*(1/2^P : ℝ)≤2*(β/4)/9) (hK : (1-β/4/2)^(2^K)≤3*(5*(1/2^P : ℝ))/(β/4))
    (hinv : StageInv (gvM P AZ) (Finset.Ico 0 s) μ₀ m₀)
    (hm : m₀+s*((1/2^P : ℝ)*(1+60*3/β^2)*(n+3))≤3)
    (hmu : μ/2+2*s*((1/2^P : ℝ)*(1+60*3/β^2)*(n+3))≤μ₀)
    (hW : (12/β+4)*2^P<(2 : ℝ)^(w-1)) :
    ∀ m < s, FacFits w P K (facState P K (windowZ B AZ) (inputsZ B AZ s) m) := by
  intro m hms
  set ηr : ℝ := 1/2^P with hηr
  set η' : ℝ := ηr*(1+60*3/β^2) with hη'
  have hηr0 : 0≤ηr := by positivity
  have hrd : ∀ x, |rdP P x-x|≤ηr := fun x => rdP_err P x
  have hext : 0≤ηr*(60*3/β^2) := by positivity
  have hle : ηr≤η' := by nlinarith
  have hrd' : ∀ x, |rdP P x-x|≤η' := fun x => (hrd x).trans hle
  set R := NewtonRecip.recipMul (rdP P) 3 β K
  have hmulR : ∀ a b, |R a b-a/b|≤η' :=
    NewtonRecip.recipMul_err (rdP P) ηr hrd 3 β (by norm_num) hβ hηβ K hK
  have hR0 : ∀ c, R 0 c=0 := NewtonRecip.recipMul_zero (rdP P) (rdP_zero P) 3 β K
  have hM0 : ∀ c, mRule P K 0 c=0 := machMul_zero P K
  have hagree : ∀ a c, |a|≤3 → μ/2≤c → c≤3 → mRule P K a c=R a c := fun a c ha hc hc3 => by
    simp only [mRule, PhaseCellMatrix.machMul, R, NewtonRecip.recipMul, hβμ.trans hc, hc3, ha,
      and_self, ite_true]
  have houtR : ∀ i j, (s ≤ i ∨ s ≤ j) → gvM P AZ i j=0 := fun i j h => by
    simp [gvM, hout i j h, gv]
  have hn0 : 0≤n := le_trans (Nat.cast_nonneg _) hn
  -- stage values
  have hval : ∀ i j, m ≤ i → m ≤ j →
      gv P (stgZ P K AZ m i j)=stg (rdP P) R (gvM P AZ) 0 m i j := by
    intro i j hi hj
    have h1 := congrFun (congrFun (stgZ_map P K hP AZ m) i) j
    simp only [gvM] at h1
    rw [h1]
    exact stg_congr (rdP P) R η' hrd' hmulR (rdP_zero P) (mRule P K) hR0 hM0 μ 3 n (by norm_num) s hn
      (gvM P AZ) houtR μ₀ m₀ hinv hm hmu hμ hagree m hms.le i j hi hj
  have hst := stg_inv (rdP P) R η' hrd' hmulR μ 3 n (by norm_num) s hn (gvM P AZ) μ₀ m₀ hinv hm hmu hμ m
    hms.le
  have hQ : 0≤η'*(n+3) := by positivity
  have hmR : (m : ℝ)<s := by exact_mod_cast hms
  have hbound : ∀ i j, m ≤ i → m ≤ j → |stg (rdP P) R (gvM P AZ) 0 m i j|≤3 := by
    intro i j hi hj
    by_cases hij : i<s ∧ j<s
    · have hiS : i ∈ Finset.Ico m s := Finset.mem_Ico.mpr ⟨hi, hij.1⟩
      have hjS : j ∈ Finset.Ico m s := Finset.mem_Ico.mpr ⟨hj, hij.2⟩
      have h1 := Finset.single_le_sum (f := fun j => |stg (rdP P) R (gvM P AZ) 0 m i j|)
        (fun _ _ => abs_nonneg _) hjS
      have h2 := hst.2 i hiS
      have h3 : m₀+(m : ℝ)*(η'*(n+3))≤3 := by
        have : (m : ℝ)*(η'*(n+3))≤s*(η'*(n+3)) := mul_le_mul_of_nonneg_right hmR.le hQ
        linarith
      linarith
    · rw [stg_out (rdP P) R (rdP_zero P) hR0 s (gvM P AZ) houtR m i j (by omega)]; simp
  have hmem : m ∈ Finset.Ico m s := Finset.mem_Ico.mpr ⟨le_rfl, hms⟩
  have hpivlo : μ/2≤stg (rdP P) R (gvM P AZ) 0 m m m := by
    have h1 := hst.1 m hmem
    have h0 : 0≤∑ j∈(Finset.Ico m s).erase m, |stg (rdP P) R (gvM P AZ) 0 m m j| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have : 2*(m : ℝ)*(η'*(n+3))≤2*s*(η'*(n+3)) := by nlinarith
    linarith
  have hpivhi : stg (rdP P) R (gvM P AZ) 0 m m m≤3 := (le_abs_self _).trans (hbound m m le_rfl le_rfl)
  have hV3 : (3 : ℝ)≤12/β+4 := by
    have : 0≤12/β := by positivity
    linarith
  -- unfold the window
  rw [facState_window P K B hP AZ hA s m hms.le, List.range'_succ, List.map_cons, winRowZ,
    List.range'_succ, List.map_cons]
  set c := stgZ P K AZ m m m with hc
  have hgc : gv P c=stg (rdP P) R (gvM P AZ) 0 m m m := hval m m le_rfl le_rfl
  have hb : β≤gv P c := by rw [hgc]; linarith
  have hb3 : gv P c≤3 := by rw [hgc]; exact hpivhi
  have hbpos : 0<gv P c := lt_of_lt_of_le hβ hb
  have hnewt : ∀ k, |gv P (newtonZ P c k)|≤2/β := by
    intro k
    rw [← newtonZ_eq P hP c k]
    obtain ⟨h1, h2⟩ := NewtonRecip.newtonR_range (rdP P) ηr hrd β (gv P c) hβ hb hb3 hηβ k
    have hr0 : 0≤NewtonRecip.newtonR (rdP P) (gv P c) k := by
      by_contra hneg; push_neg at hneg; nlinarith
    rw [abs_of_nonneg hr0]
    calc NewtonRecip.newtonR (rdP P) (gv P c) k≤2/gv P c := by
          rw [le_div_iff₀ hbpos]; linarith
      _≤2/β := div_le_div_of_nonneg_left (by norm_num) hβ hb
  have h2β : 2/β≤12/β+4 := by
    have : 2/β≤12/β := div_le_div_of_nonneg_right (by norm_num) hβ.le
    linarith
  refine ⟨fits_of_gv P w c _ (by rw [hgc]; exact (hbound m m le_rfl le_rfl).trans hV3) hW,
    fun k _ => ⟨fits_of_gv P w _ _ ((hnewt k).trans h2β) hW, ?_⟩,
    fits_of_gv P w _ _ ((hnewt K).trans h2β) hW, ?_, ?_⟩
  · -- `t = c r`
    refine fits_of_gv P w _ (12/β+4) ?_ hW
    have h := Mult.BandList.rdP_mul_grid P c (newtonZ P c k)
    simp only [gv] at h ⊢
    rw [← h]
    have hr := hnewt k
    rw [← newtonZ_eq P hP c k] at hr
    obtain ⟨h1, h2⟩ := NewtonRecip.newtonR_range (rdP P) ηr hrd β (gv P c) hβ hb hb3 hηβ k
    have hcr := rdP_err P (gv P c*NewtonRecip.newtonR (rdP P) (gv P c) k)
    have hηr1 : (1 : ℝ)/2^P≤1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    rw [newtonZ_eq P hP c k] at hcr h1 h2
    simp only [gv] at hcr h1 h2
    have := abs_le.mp hcr
    rw [abs_le]; constructor <;> nlinarith
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have hj' := List.mem_range'_1.mp hj
    exact fits_of_gv P w _ _ (by rw [hval m j le_rfl (by omega)]; exact (hbound m j le_rfl (by omega)).trans hV3) hW
  · intro row hrow
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    have hi' := List.mem_range'_1.mp hi
    have hhead : (winRowZ B (stgZ P K AZ m) m i).headD 0=stgZ P K AZ m i m := by
      simp [winRowZ, List.range'_succ]
    rw [hhead]
    have hgh : |gv P (stgZ P K AZ m i m)|≤3 := by
      rw [hval i m (by omega) le_rfl]; exact hbound i m (by omega) le_rfl
    refine ⟨fits_of_gv P w _ _ (hgh.trans hV3) hW, fits_of_gv P w _ (12/β+4) ?_ hW⟩
    simp only [facMul, hhead]
    have h := Mult.BandList.rdP_mul_grid P (stgZ P K AZ m i m) (newtonZ P c K)
    simp only [gv] at h ⊢
    rw [← h]
    have hcr := rdP_err P ((stgZ P K AZ m i m : ℝ)/2^P*((newtonZ P c K : ℝ)/2^P))
    have hr := hnewt K
    simp only [gv] at hr hgh
    have hprod : |(stgZ P K AZ m i m : ℝ)/2^P*((newtonZ P c K : ℝ)/2^P)|≤3*(2/β) := by
      rw [abs_mul]; exact mul_le_mul hgh hr (abs_nonneg _) (by norm_num)
    have hηr1 : (1 : ℝ)/2^P≤1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have e : 3*(2/β)=6/β := by ring
    have h6 : 6/β≤12/β := div_le_div_of_nonneg_right (by norm_num) hβ.le
    have := abs_sub_abs_le_abs_sub (rdP P ((stgZ P K AZ m i m : ℝ)/2^P*((newtonZ P c K : ℝ)/2^P)))
      ((stgZ P K AZ m i m : ℝ)/2^P*((newtonZ P c K : ℝ)/2^P))
    linarith

end IntegerMultBounds.MathlibTM2.Fast
