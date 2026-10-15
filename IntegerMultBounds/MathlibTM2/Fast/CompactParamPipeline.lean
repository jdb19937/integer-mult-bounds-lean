module

public import IntegerMultBounds.MathlibTM2.Fast.CompactParamProg

/-! Compose the charged compact table overwrite with existing parameter computation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Mult
open IntegerMultBounds.MathlibTM2.Mult.Sizes
noncomputable section
variable {A W w : ℕ}

def compactPmStages : TblCode pmNV := (pmStages ;; pmClearC) ;; compactPmOverwrite

def compactPmCode1 : TblCode pmNV := pmCode1 ;; compactPmOverwrite

def compactPmAtoms1 (n : ℕ) : ℕ := pmAtoms1 n+compactPmOverwriteAtoms n

/-- Populate the compact table from the input length, retaining the accumulator. -/
theorem compactPmStages_do (n : ℕ) (hn : 2≤n) (hW : 4*b n+16≤W)
    (s : TblSt pmNV A) (acc : List (Fin (A+4))) (hs : PmF n 1 acc s) :
    TblDo A W w compactPmStages s (fun s' => s'.val=compactPmVals n ∧ s'.acc=acc)
      (compactPmAtoms1 n) := by
  refine (((pmStages_do (w:=w) hn hW s hs).seq (fun s' h => pm_clear_do s' h)).seq
    (fun s' h => (compactPmOverwrite_do n hW s' h.1).mono (P':=fun z => z.val=compactPmVals n ∧ z.acc=acc)
      (fun _ hh => ⟨hh.1,hh.2.trans h.2⟩) le_rfl)).mono (fun _ h => h) ?_
  unfold compactPmAtoms1 pmAtoms1
  omega

/-- Reuse the existing complete first parameter program, including emitted axes. -/
theorem compactPmCode1_do (n : ℕ) (hn : 2≤n) (hW : 4*b n+16≤W)
    (s : TblSt pmNV A) (acc : List (Fin (A+4))) (hs : PmF n 1 acc s) :
    TblDo A W w compactPmCode1 s
      (fun s' => s'.val=compactPmVals n ∧ s'.acc=(pmTList A w n).reverse++acc)
      (compactPmAtoms1 n) :=
  (pmCode1_do hn hW s hs).seq (fun s' h => (compactPmOverwrite_do n hW s' h.1).mono
    (fun _ hh => ⟨hh.1,hh.2.trans h.2⟩) le_rfl)

/-- The patch has a uniform polynomial atom budget in the existing precision scale. -/
theorem compactPmOverwriteAtoms_le (n : ℕ) : compactPmOverwriteAtoms n≤64*(b n+1) := by
  have hk : CompactSizes.K n≤b n := (CompactSizes.K_le_d n).trans (d_le_b n)
  unfold compactPmOverwriteAtoms
  omega

end
end IntegerMultBounds.MathlibTM2.Fast.TableVM
