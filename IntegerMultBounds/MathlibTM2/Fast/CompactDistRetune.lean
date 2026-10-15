module

public import IntegerMultBounds.MathlibTM2.Fast.CompactParamProg
public import IntegerMultBounds.MathlibTM2.Fast.DistBase

/-! Retune the retained parameter table and unary chunk after legacy distribution,
before layout wires and permutations are constructed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
noncomputable section
variable {T Q A : ℕ} {U P : Type}

def compactDsRetune (rg : TblR pmNV → Fin T) (o : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg compactPmOverwrite) (.seq (uclear o) (dsUn rg 4 o))

def compactDsRetuneCost (n W oldLength : ℕ) : ℕ :=
  compactPmOverwriteAtoms n*tblC W W+
    ((2*oldLength+2)+(W*(4*CompactSizes.K n+11)+2*CompactSizes.K n+6))

/-- Only the retained table's chunk and the unary chunk output change. All other
current registers, including distribution output records, are preserved. -/
theorem compactDsRetune_runs (body : P → Pr P T Q A U)
    (rg : TblR pmNV → Fin T) (hrg : Function.Injective rg)
    (o : Fin T) (ho : ∀ r,rg r≠o) (n W : ℕ) (hW : 4*b n+32≤W)
    (wl : List (Fin (A+4))) (hwl : wl.length=W) (R : Regs T A)
    (hvals : ∀ i,pmVals n i<2^W) :
    dsRuns body (compactDsRetune rg o)
      (dsOv rg R (tblRho W wl wl ⟨pmVals n,[]⟩))
      (dsOv rg (Function.update R o (List.replicate (CompactSizes.K n) tick))
        (tblRho W wl wl ⟨compactPmVals n,[]⟩))
      (compactDsRetuneCost n W (R o).length) := by
  have hp := (compactPmOverwrite_do (w:=W) n hW (⟨pmVals n,[]⟩ : TblSt pmNV A) rfl).mono
    (P':=fun s => s=(⟨compactPmVals n,[]⟩ : TblSt pmNV A))
    (fun s h => by cases s; simp_all) le_rfl
  have hpatch := ds_code (body:=body) hrg wl wl hwl hwl le_rfl hp hvals R
  let rho := tblRho W wl wl (⟨compactPmVals n,[]⟩ : TblSt pmNV A)
  have hclear := ds_uclear (body:=body) o (dsOv rg R rho)
  rw [dsOv_off R rho ho,dsOv_update R rho ho] at hclear
  have hK : CompactSizes.K n<2^W := by
    have hd : d n<2^W := hvals 3
    exact (CompactSizes.K_le_d n).trans_lt hd
  have hem := ds_un (body:=body) hrg ho wl wl (⟨compactPmVals n,[]⟩ : TblSt pmNV A) 4
    (by simpa only [compactPmVals_chunk] using hK) (Function.update R o [])
  simp only [compactPmVals_chunk,Function.update_self,List.append_nil,
    Function.update_idem] at hem
  exact hpatch.seq (hclear.seq hem)

end
end IntegerMultBounds.MathlibTM2.Fast.TableVM
