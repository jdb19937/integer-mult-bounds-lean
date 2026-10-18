module

public import IntegerMultBounds.MathlibTM2.Fast.ParamProg
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
import IntegerMultBounds.MathlibTM2.Mult.CompactDyadicRootRoom

/-! Charged overwrite of the chunk entry of the clean parameter table: the root
`⌊d^(7/8)⌋` of the seventh power of the dimension, then the uniform balanced width above it
(`compactWidthC`). The legacy parameter program and table contracts retain their original
meanings. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Mult
open IntegerMultBounds.MathlibTM2.Mult.Sizes
noncomputable section
variable {A W w : ℕ}

/-- Same parameter table, with only the chunk entry replaced. -/
def compactPmVals (n : ℕ) : Fin pmNV → ℕ := Function.update (pmVals n) 4 (CompactSizes.K n)

/-- Preserve `x` in `0` and place `x^7` in `1`: `x, x^2, x^3, x^6, x^7`. -/
def compactSeventhC : TblCode 2 := tblBlock 2 [.copy 0 1,.mul 1 0 1,.mul 1 0 1,.mul 1 1 1] (.mul 1 0 1)

theorem compactSeventhC_do (st : TblSt 2 A) {x : ℕ} (hx : st.val 0=x) (hW : x^7<2^W) :
    TblDo A W w compactSeventhC st (fun s => s.val 0=x ∧ s.val 1=x^7 ∧ s.acc=st.acc) 5 := by
  have hp (k : ℕ) (hk : 1≤k) (hk7 : k≤7) : x^k<2^W := by
    by_cases hx0 : x=0
    · simp [hx0,Nat.ne_of_gt hk]
    · exact (Nat.pow_le_pow_right (by omega : 1≤x) hk7).trans_lt hW
  have h1 := hp 1 le_rfl (by omega)
  have h2 := hp 2 (by omega) (by omega)
  have h3 := hp 3 (by omega) (by omega)
  have h6 := hp 6 (by omega) (by omega)
  have e2 : x*x=x^2 := by ring
  have e3 : x^2*x=x^3 := by ring
  have e6 : x^3*x^3=x^6 := by ring
  have e7 : x^6*x=x^7 := by ring
  rw [pow_one] at h1
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hx,e2,e3,e6,e7,h2,h3,h6,hW]
  · simp [tblExactList,TblIns.exact,hx,e2,e3,e6,e7]

/-- The seventh power of the dimension and its successor square fit the parameter word. -/
theorem pm_seventh_sq_lt {n : ℕ} (hW : 4*b n+32≤W) : (d n^7+1)*(d n^7+1)<2^W := by
  have h7 : d n^7≤b n^7 := Nat.pow_le_pow_left (d_le_b n) 7
  have h4 : b n^7+1≤(b n+1)^7 := by
    simpa only [one_pow] using
      (pow_add_pow_le (Nat.zero_le (b n)) (by decide : (0:ℕ)≤1) (by decide : 7≠0))
  have h8 : (d n^7+1)*(d n^7+1)≤(b n+1)^18 := by
    calc (d n^7+1)*(d n^7+1)≤(b n+1)^7*(b n+1)^7 := Nat.mul_le_mul (by omega) (by omega)
      _ = (b n+1)^14 := by ring
      _ ≤ (b n+1)^18 := Nat.pow_le_pow_right (by omega) (by norm_num)
  exact (h8.trans_lt (Mult.CompactDyadicRootRoom.eighteenth_power_lt (b n))).trans_le
    (pm_W_pow hW le_rfl)

def compactPmPowerReg : Fin 2 → Fin pmNV := ![3,35]

def compactPmRootReg : Fin 6 → Fin pmNV := ![35,4,31,32,33,34]

def compactPmRootClear : TblCode pmNV :=
  tblBlock pmNV [.zero 31,.zero 32,.zero 33,.zero 34] (.zero 35)

/-- The uniform chunk width above the root: `n` in `0`, `d` in `1`, the root in `2` (the
result), scratch in `3`, `4`. `q := n / K₀`, `w := n / q`, `K := max K₀ w`, `K := min d K`,
scratch cleared. -/
def compactWidthC : TblCode 5 :=
  tblBlock 5 [.div 0 2 3] (.div 0 3 4) ;;
  .ite 2 4 (.ins (.copy 4 2)) (.ins (.zero 3)) ;;
  .ite 1 2 (.ins (.copy 1 2)) (.ins (.zero 3)) ;;
  tblBlock 5 [.zero 3] (.zero 4)

theorem compactWidthC_do (st : TblSt 5 A) {n D K₀ : ℕ} (h0 : st.val 0=n) (h1 : st.val 1=D)
    (h2 : st.val 2=K₀) :
    TblDo A W w compactWidthC st (fun s => s.val 0=n ∧ s.val 1=D ∧
      s.val 2=min D (Balanced.unifWidth n K₀) ∧ s.val 3=0 ∧ s.val 4=0 ∧ s.acc=st.acc) 8 := by
  refine (TblDo.block (P := fun s => s.val 0=n ∧ s.val 1=D ∧ s.val 2=K₀ ∧ s.val 4=n/(n/K₀) ∧
      s.acc=st.acc) _ _ (by simp [tblFitsList,TblIns.fits])
      (by simp [tblExactList,TblIns.exact,h0,h1,h2])).seq (K₂ := 6)
    (fun s₁ ⟨a0,a1,a2,a4,aa⟩ => ?_)
  have hmax : TblDo A W w (.ite 2 4 (.ins (.copy 4 2)) (.ins (.zero 3))) s₁
      (fun s => s.val 0=n ∧ s.val 1=D ∧ s.val 2=Balanced.unifWidth n K₀ ∧ s.acc=st.acc) 2 := by
    by_cases hlt : K₀<n/(n/K₀)
    · refine TblDo.iteT (by rw [a2,a4]; exact hlt) (TblDo.ins _ ?_)
      simp [TblIns.run,a0,a1,a4,aa,Balanced.unifWidth,max_eq_right hlt.le]
    · refine TblDo.iteF (by rw [a2,a4]; exact hlt) (TblDo.ins _ ?_)
      simp [TblIns.run,a0,a1,a2,aa,Balanced.unifWidth,max_eq_left (not_lt.1 hlt)]
  refine hmax.seq (K₂ := 4) (fun s₂ ⟨b0,b1,b2,ba⟩ => ?_)
  have hmin : TblDo A W w (.ite 1 2 (.ins (.copy 1 2)) (.ins (.zero 3))) s₂
      (fun s => s.val 0=n ∧ s.val 1=D ∧ s.val 2=min D (Balanced.unifWidth n K₀) ∧
        s.acc=st.acc) 2 := by
    by_cases hlt : D<Balanced.unifWidth n K₀
    · refine TblDo.iteT (by rw [b1,b2]; exact hlt) (TblDo.ins _ ?_)
      simp [TblIns.run,b0,b1,ba,min_eq_left hlt.le]
    · refine TblDo.iteF (by rw [b1,b2]; exact hlt) (TblDo.ins _ ?_)
      simp [TblIns.run,b0,b1,b2,ba,min_eq_right (not_lt.1 hlt)]
  refine hmin.seq (K₂ := 2) (fun s₃ ⟨c0,c1,c2,ca⟩ => ?_)
  refine TblDo.block _ _ (by simp [tblFitsList,TblIns.fits]) ?_
  simp [tblExactList,TblIns.exact,c0,c1,c2,ca]

def compactPmWidthReg : Fin 5 → Fin pmNV := ![9,3,4,31,32]

def compactPmOverwrite : TblCode pmNV :=
  compactSeventhC.rename compactPmPowerReg ;; ((pmIrootC 3).rename compactPmRootReg ;;
    (compactPmRootClear ;; compactWidthC.rename compactPmWidthReg))

def compactPmOverwriteAtoms (n : ℕ) : ℕ := 50+26*CompactSizes.Kroot n

/-- The table with the chunk root in the chunk entry. -/
def compactPmRootVals (n : ℕ) : Fin pmNV → ℕ := Function.update (pmVals n) 4 (CompactSizes.Kroot n)

private theorem compactPm_width (n : ℕ) (s : TblSt pmNV A) (hs : s.val=compactPmRootVals n) :
    TblDo A W w (compactWidthC.rename compactPmWidthReg) s
      (fun s' => s'.val=compactPmVals n ∧ s'.acc=s.acc) 8 := by
  have h0 : (s.restrict compactPmWidthReg).val 0=ℓ n-1 := by
    simp [TblSt.restrict,compactPmWidthReg,hs,compactPmRootVals,pmVals,pmVal,pmNV]
  have h1 : (s.restrict compactPmWidthReg).val 1=d n := by
    simp [TblSt.restrict,compactPmWidthReg,hs,compactPmRootVals,pmVals,pmVal,pmNV]
  have h2 : (s.restrict compactPmWidthReg).val 2=CompactSizes.Kroot n := by
    simp [TblSt.restrict,compactPmWidthReg,hs,compactPmRootVals,pmNV]
  refine (TblDo.rename (f:=compactPmWidthReg) (by decide : Function.Injective compactPmWidthReg)
    (compactWidthC_do (W:=W) (w:=w) (s.restrict compactPmWidthReg) h0 h1 h2)).mono ?_ le_rfl
  rintro s' ⟨⟨e0,e1,e2,e3,e4,ea⟩,hrest⟩
  refine ⟨funext fun i => ?_,by simpa using ea⟩
  have hK : CompactSizes.K n=min (d n) (Balanced.unifWidth (ℓ n-1) (CompactSizes.Kroot n)) := rfl
  by_cases hex : ∃ y, compactPmWidthReg y=i
  · obtain ⟨y,rfl⟩ := hex
    fin_cases y
    · simpa [compactPmWidthReg,compactPmVals,pmVals,pmVal,pmNV] using e0
    · simpa [compactPmWidthReg,compactPmVals,pmVals,pmVal,pmNV] using e1
    · simpa [compactPmWidthReg,compactPmVals,hK,pmNV] using e2
    · simpa [compactPmWidthReg,compactPmVals,pmVals,pmVal,pmNV] using e3
    · simpa [compactPmWidthReg,compactPmVals,pmVals,pmVal,pmNV] using e4
  · push Not at hex
    have h4 : i≠4 := fun h => hex 2 (by rw [h]; rfl)
    rw [hrest i hex, hs]
    simp [compactPmRootVals,compactPmVals,h4]

private theorem compactPm_clear (n : ℕ) (s : TblSt pmNV A) (acc : List (Fin (A+4)))
    (ha : s.acc=acc) (h4 : s.val 4=CompactSizes.Kroot n)
    (hoff : ∀ i, (∀ j,compactPmRootReg j≠i) → s.val i=pmVals n i) :
    TblDo A W w compactPmRootClear s
      (fun s' => s'.val=compactPmRootVals n ∧ s'.acc=acc) 5 := by
  refine TblDo.block _ _ (by simp [tblFitsList,TblIns.fits]) ⟨funext fun i => ?_,?_⟩
  · have hsrc : ∀ i : Fin pmNV,i≠4 → i≠31 → i≠32 → i≠33 → i≠34 → i≠35 →
        s.val i=pmVals n i := by
      intro i h4 h31 h32 h33 h34 h35
      apply hoff i
      intro j
      fin_cases j <;> simp_all [compactPmRootReg,ne_comm]
    fin_cases i <;> simp [compactPmRootVals,tblExactList,TblIns.exact,
      pmVals,pmVal,h4,hsrc,pmNV]
  · simp [tblExactList,TblIns.exact,ha]

/-- Recompute slot 4 as the eighth root of the seventh power of slot 3, through scratch slot 35,
then as the uniform balanced width of slot 9 above it, restoring all scratch cells to zero. Every
other parameter and the accumulator are preserved exactly. -/
theorem compactPmOverwrite_do (n : ℕ) (hW : 4*b n+32≤W) (s : TblSt pmNV A)
    (hs : s.val=pmVals n) :
    TblDo A W w compactPmOverwrite s
      (fun s' => s'.val=compactPmVals n ∧ s'.acc=s.acc) (compactPmOverwriteAtoms n) := by
  have hsq := pm_seventh_sq_lt (n:=n) hW
  have hpowW : d n^7<2^W := lt_of_le_of_lt ((Nat.le_succ _).trans (Nat.le_mul_self _)) hsq
  have hd : (s.restrict compactPmPowerReg).val 0=d n := by
    simp [TblSt.restrict,compactPmPowerReg,hs,pmVals,pmVal,pmNV]
  have hpow := TblDo.rename (f:=compactPmPowerReg) (by decide : Function.Injective compactPmPowerReg)
    (compactSeventhC_do (w:=w) (s.restrict compactPmPowerReg) hd hpowW)
  refine (hpow.seq (K₂ := (32+26*CompactSizes.Kroot n)+(5+8)) (fun s₁ h₁ => ?_)).mono (fun _ h => h) ?_
  · have hx : (s₁.restrict compactPmRootReg).val 0=d n^7 := by
      simpa [TblSt.restrict,compactPmRootReg,compactPmPowerReg] using h₁.1.2.1
    have hroot := TblDo.rename (f:=compactPmRootReg) (by decide : Function.Injective compactPmRootReg)
      (pmIrootC_do (w:=w) 3 (s₁.restrict compactPmRootReg) hx hsq (pm_const_lt hW (by norm_num)))
    refine (hroot.seq (fun s₂ h₂ => (compactPm_clear n s₂ s.acc ?_ ?_ ?_).seq
      (fun s₃ h₃ => (compactPm_width n s₃ h₃.1).mono (fun _ h => ⟨h.1,h.2.trans h₃.2⟩) le_rfl))).mono
      (fun _ h => h) ?_
    · simpa [TblSt.restrict] using h₂.1.2.2.trans h₁.1.2.2
    · simpa [TblSt.restrict,compactPmRootReg,CompactSizes.Kroot,CompactSizes.cExp] using h₂.1.2.1
    · intro i hi
      rw [h₂.2 i hi]
      by_cases h3 : i=3
      · subst h3
        have h₁₀ := h₁.1.1
        simp only [TblSt.restrict,compactPmPowerReg] at h₁₀
        simpa [pmVals,pmVal,pmNV] using h₁₀
      · rw [h₁.2 i ?_, hs]
        intro y
        fin_cases y
        · simpa [compactPmPowerReg] using Ne.symm h3
        · simpa [compactPmRootReg,compactPmPowerReg] using hi 0
    · simp only [CompactSizes.Kroot,CompactSizes.cExp,CompactSizes.d]
      omega
  · unfold compactPmOverwriteAtoms
    omega

lemma compactPmVals_chunk (n : ℕ) : compactPmVals n 4=CompactSizes.K n := by
  simp [compactPmVals]

lemma compactPmVals_other (n : ℕ) (i : Fin pmNV) (hi : i≠4) : compactPmVals n i=pmVals n i := by
  simp [compactPmVals,hi]

end
end IntegerMultBounds.MathlibTM2.Fast.TableVM
