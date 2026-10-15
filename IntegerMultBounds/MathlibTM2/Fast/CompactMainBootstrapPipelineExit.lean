module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineGlobals

/-! Clear only the retained global words after any number of transform rounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {T Q A : ℕ} {U P : Type}

private theorem clearGlobals_runs (body : P → Pr P T Q A U)
    (R : Fin T → List (Fin (A+4))) (x y : Fin T) (hxy : x≠y) (d g : ℕ)
    (hx : R x=List.replicate d tick) (hy : R y=List.replicate g tick) :
    LayRuns body (.seq (uclear x) (uclear y)) R
      (Function.update (Function.update R x []) y []) ((2*d+2)+(2*g+2)) := by
  have h := (lr_uclear body (R:=R) x).seq (lr_uclear body y)
  simpa only [Function.update_of_ne hxy.symm,hx,hy,List.length_replicate] using h

def compactMnGlobalsExit : Pr P compactMnT Q A U :=
  .seq (uclear (compactMnLay (.bc (.inl (.work 13)))))
    (uclear (compactMnLay (.bc (.inl (.work 14)))))

/-- Exit clears both globals and preserves every other current register. -/
theorem compactMnGlobalsExit_runs (body : P → Pr P compactMnT Q A U)
    (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) (h : CompactMainGlobals R p d) :
    LayRuns body compactMnGlobalsExit R
      (Function.update (Function.update R (compactMnLay (.bc (.inl (.work 13)))) [])
        (compactMnLay (.bc (.inl (.work 14)))) [])
      ((2*d+2)+(2*(4*Nat.clog 2 p+6)+2)) := by
  apply clearGlobals_runs body R _ _ _ d (4*Nat.clog 2 p+6) h.1 h.2
  intro he
  have he' := compactMnLay_injective he
  cases he'

end
end IntegerMultBounds.MathlibTM2.Fast.Main
