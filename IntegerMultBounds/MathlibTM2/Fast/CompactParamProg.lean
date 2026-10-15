module

public import IntegerMultBounds.MathlibTM2.Fast.ParamProg
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes

/-! Charged eighth-root overwrite of the clean parameter table. The legacy
parameter program and table contracts retain their original meanings. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Mult
open IntegerMultBounds.MathlibTM2.Mult.Sizes
noncomputable section
variable {A W w : ℕ}

/-- Same parameter table, with only the chunk entry replaced. -/
def compactPmVals (n : ℕ) : Fin pmNV → ℕ := Function.update (pmVals n) 4 (CompactSizes.K n)

def compactPmRootReg : Fin 6 → Fin pmNV := ![3,4,31,32,33,34]

def compactPmRootClear : TblCode pmNV :=
  tblBlock pmNV [.zero 31,.zero 32,.zero 33] (.zero 34)

def compactPmOverwrite : TblCode pmNV :=
  (pmIrootC 3).rename compactPmRootReg ;; compactPmRootClear

def compactPmOverwriteAtoms (n : ℕ) : ℕ := 36+26*CompactSizes.K n

private theorem compactPm_clear (n : ℕ) (s : TblSt pmNV A) (acc : List (Fin (A+4)))
    (ha : s.acc=acc) (h3 : s.val 3=d n) (h4 : s.val 4=CompactSizes.K n)
    (hoff : ∀ i, (∀ j,compactPmRootReg j≠i) → s.val i=pmVals n i) :
    TblDo A W w compactPmRootClear s
      (fun s' => s'.val=compactPmVals n ∧ s'.acc=acc) 4 := by
  refine TblDo.block _ _ (by simp [tblFitsList,TblIns.fits]) ⟨funext fun i => ?_,?_⟩
  · have hsrc : ∀ i : Fin pmNV,i≠3 → i≠4 → i≠31 → i≠32 → i≠33 → i≠34 →
        s.val i=pmVals n i := by
      intro i h3 h4 h31 h32 h33 h34
      apply hoff i
      intro j
      fin_cases j <;> simp_all [compactPmRootReg,ne_comm]
    fin_cases i <;> simp [compactPmVals,tblExactList,TblIns.exact,
      pmVals,pmVal,h3,h4,hsrc,pmNV]
  · simp [tblExactList,TblIns.exact,ha]

/-- Recompute slot 4 from original slot 3, restoring all scratch cells to zero.
Every other parameter and the accumulator are preserved exactly. -/
theorem compactPmOverwrite_do (n : ℕ) (hW : 4*b n+16≤W) (s : TblSt pmNV A)
    (hs : s.val=pmVals n) :
    TblDo A W w compactPmOverwrite s
      (fun s' => s'.val=compactPmVals n ∧ s'.acc=s.acc) (compactPmOverwriteAtoms n) := by
  have hd : (s.restrict compactPmRootReg).val 0=d n := by
    simp [TblSt.restrict,compactPmRootReg,hs,pmVals,pmVal,pmNV]
  have hroot := TblDo.rename (f:=compactPmRootReg) (by decide : Function.Injective compactPmRootReg)
    (pmIrootC_do (w:=w) 3 (s.restrict compactPmRootReg) hd (pm_sq_lt hW (d_le_b n))
      (pm_const_lt hW (by norm_num)))
  refine (hroot.seq (fun s' h => compactPm_clear n s' s.acc h.1.2.2 h.1.1 h.1.2.1
    (fun i hi => (h.2 i hi).trans (congrFun hs i)))).mono (fun _ h => h) ?_
  simp [compactPmOverwriteAtoms,CompactSizes.K,CompactSizes.cExp,CompactSizes.d]
  omega

lemma compactPmVals_chunk (n : ℕ) : compactPmVals n 4=CompactSizes.K n := by
  simp [compactPmVals]

lemma compactPmVals_other (n : ℕ) (i : Fin pmNV) (hi : i≠4) : compactPmVals n i=pmVals n i := by
  simp [compactPmVals,hi]

end
end IntegerMultBounds.MathlibTM2.Fast.TableVM
