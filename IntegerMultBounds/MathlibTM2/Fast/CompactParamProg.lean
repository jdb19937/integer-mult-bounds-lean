module

public import IntegerMultBounds.MathlibTM2.Fast.ParamProg
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Charged overwrite of the chunk entry of the clean parameter table: the root
`⌈d/2⌉ = (d + 1)/2` of the dimension, then the uniform balanced width above it
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

/-- Place the chunk root `(d + 1)/2` of slot 3 in slot 4, through scratch slot 35. -/
def compactPmRootC : TblCode pmNV :=
  tblBlock pmNV [.copy 3 4,.inc 4,.zero 35,.inc 35,.inc 35,.div 4 35 4] (.zero 35)

def compactPmOverwrite : TblCode pmNV :=
  compactPmRootC ;; compactWidthC.rename compactPmWidthReg

def compactPmOverwriteAtoms (_n : ℕ) : ℕ := 7+8

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

private theorem compactPm_root (n : ℕ) (hW : 4*b n+32≤W) (s : TblSt pmNV A)
    (hs : s.val=pmVals n) :
    TblDo A W w compactPmRootC s
      (fun s' => s'.val=compactPmRootVals n ∧ s'.acc=s.acc) 7 := by
  have h1 : d n+1<2^W := pm_small_lt hW (by have := d_le_b n; omega)
  have h2 : 2<2^W := pm_const_lt hW (by norm_num)
  refine TblDo.block _ _ ?_ ⟨funext fun i => ?_,?_⟩
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hs,pmVals,pmVal,pmNV]
    omega
  · fin_cases i <;> simp [compactPmRootVals,tblExactList,TblIns.exact,hs,pmVals,pmVal,
      CompactSizes.Kroot,pmNV]
  · simp [tblExactList,TblIns.exact]

/-- Recompute slot 4 as the root `(d + 1)/2` of slot 3, then as the uniform balanced width of
slot 9 above it, restoring the scratch cell to zero. Every other parameter and the accumulator
are preserved exactly. -/
theorem compactPmOverwrite_do (n : ℕ) (hW : 4*b n+32≤W) (s : TblSt pmNV A)
    (hs : s.val=pmVals n) :
    TblDo A W w compactPmOverwrite s
      (fun s' => s'.val=compactPmVals n ∧ s'.acc=s.acc) (compactPmOverwriteAtoms n) :=
  (compactPm_root n hW s hs).seq (fun s₁ h₁ => (compactPm_width n s₁ h₁.1).mono
    (fun _ h => ⟨h.1,h.2.trans h₁.2⟩) le_rfl)

lemma compactPmVals_chunk (n : ℕ) : compactPmVals n 4=CompactSizes.K n := by
  simp [compactPmVals]

lemma compactPmVals_other (n : ℕ) (i : Fin pmNV) (hi : i≠4) : compactPmVals n i=pmVals n i := by
  simp [compactPmVals,hi]

end
end IntegerMultBounds.MathlibTM2.Fast.TableVM
