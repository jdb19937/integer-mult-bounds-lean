module

public import IntegerMultBounds.MathlibTM2.Fast.CompactDistRetune
public import IntegerMultBounds.MathlibTM2.Fast.Dist

/-! Legacy distribution followed by a charged compact chunk retuning, before
any chunk-dependent wire layout or permutation is constructed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
noncomputable section
variable {T Q A : ℕ} {U P : Type}

def compactDsIoAll (rg : TblR pmNV → Fin T) (io : DsR → Fin T) : Pr P T Q A U :=
  .seq (dsIoAll rg io) (compactDsRetune rg (io .lK))

def compactDsVal (n Wt w : ℕ) (hd : 0<d n) (vW vw : List (Fin (A+4))) :
    DsR → List (Fin (A+4)) :=
  Function.update (dsVal n Wt w hd vW vw) .lK (List.replicate (CompactSizes.K n) tick)

def compactDsIoAllCost (n Wt w : ℕ) : ℕ :=
  dsIoAllCost n Wt w+compactDsRetuneCost n (pmW n) (K n)

/-- Concrete distribution now produces the new chunk in both the retained table
and unary output, with all remaining distribution outputs unchanged. -/
theorem compactDsIoAll_runs (body : P → Pr P T Q A U)
    (rg : TblR pmNV → Fin T) (io : DsR → Fin T)
    (hrg : Function.Injective rg) (hio : Function.Injective io)
    (hdisj : ∀ r x,rg r≠io x) {n Wt w : ℕ} (hB : Big n) (hd : 0<d n)
    (hWt : Wt<2^pmW n) (hw : 4*w+2<2^pmW n) (hWL : pmW n≤dsWL n w)
    (wl : List (Fin (A+4))) (hwl : wl.length=pmW n) (R : Regs T A)
    (huW : (R (io .uW)).length=Wt) (huw : (R (io .uw)).length=w)
    (hR0 : ∀ x,x≠.uW → x≠.uw → R (io x)=[]) :
    dsRuns body (compactDsIoAll rg io)
      (dsOv rg R (tblRho (pmW n) wl wl ⟨pmVals n,[]⟩))
      (dsOv rg (dsOv io R (compactDsVal n Wt w hd (R (io .uW)) (R (io .uw))))
        (tblRho (pmW n) wl wl ⟨compactPmVals n,[]⟩))
      (compactDsIoAllCost n Wt w) := by
  have hn : 2 ≤ n := hB.1
  have hlegacy := dsIoAll_runs (body:=body) hrg hio hdisj hB hd hWt hw hWL wl hwl R huW huw hR0
  have hpatch := compactDsRetune_runs body rg hrg (io .lK) (fun r => hdisj r .lK)
    n (pmW n) (pmW_ge n) wl hwl
    (dsOv io R (dsVal n Wt w hd (R (io .uW)) (R (io .uw)))) (ds_pmVals_lt hB)
  rw [dsOv_rg hio] at hpatch
  simp only [dsVal,List.length_replicate] at hpatch
  rw [dsOv_update_on hio] at hpatch
  exact hlegacy.seq hpatch

end
end IntegerMultBounds.MathlibTM2.Fast.TableVM
