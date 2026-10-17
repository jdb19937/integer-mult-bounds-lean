module

public import IntegerMultBounds.MathlibTM2.Fast.SynBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! A reversible unary comparison used to select the actual synthetic round. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node
noncomputable section
variable {T Q A : ℕ} {U P : Type}

def compactSynCompare (a b s t : Fin T) (strict : Bool) (p q : Pr P T Q A U) : Pr P T Q A U :=
  .seq (ucopy a s t) <| .seq (usub b s t) <|
    .seq (if strict then synPop s else synSkip) <|
      synIfNE s (.seq (uclear s) p) (.seq (uclear s) q)

def compactSynCompareCost (a b : ℕ) (strict : Bool) : ℕ :=
  4*a+4*b+2*(a-b-(if strict then 1 else 0))+13

theorem compactSynCompare_runs (body : P → Pr P T Q A U)
    {a b s t : Fin T} (has : a≠s) (hat : a≠t) (hbs : b≠s) (hbt : b≠t) (hst : s≠t)
    (strict : Bool) {R R' : Fin T → List (Fin (A+4))} (hs : R s=[]) (ht : R t=[])
    {p q : Pr P T Q A U} {c : ℕ}
    (hp : 0<(R a).length-(R b).length-(if strict then 1 else 0) → LayRuns body p R R' c)
    (hq : ¬0<(R a).length-(R b).length-(if strict then 1 else 0) → LayRuns body q R R' c) :
    LayRuns body (compactSynCompare a b s t strict p q) R R'
      (compactSynCompareCost (R a).length (R b).length strict+c) := by
  let x := (R a).length
  let y := (R b).length
  let n := x-y-(if strict then 1 else 0)
  let R₁ := Function.update R s (List.replicate x tick)
  let R₂ := Function.update R s (List.replicate (x-y) tick)
  let R₃ := Function.update R s (List.replicate n tick)
  have e1 : LayRuns body (ucopy a s t) R R₁ (4*x+4) := by
    simpa [R₁,x,hs] using lr_ucopy body has hat hst ht
  have e2 : LayRuns body (usub b s t) R₁ R₂ (4*y+4) := by
    simpa [R₁,R₂,y,hbs,hst.symm,ht,List.drop_replicate,Function.update_idem] using
      lr_usub body (R := R₁) hbs hbt hst (by simp [R₁,hst.symm,ht])
  have e3 : LayRuns body (if strict then synPop s else synSkip) R₂ R₃ 1 := by
    cases strict
    · simpa [R₂,R₃,n] using lr_skip body R₂
    · simpa [R₂,R₃,n,List.tail_replicate,Function.update_idem] using lr_pop body (R := R₂) s
  have er : Function.update R₃ s []=R := by
    simp only [R₃,Function.update_idem]
    rw [←hs,Function.update_eq_self]
  have ec : LayRuns body (uclear s) R₃ R (2*n+2) := by
    simpa only [show (R₃ s).length=n by simp [R₃],er] using lr_uclear body (R := R₃) s
  have ei : LayRuns body (synIfNE s (.seq (uclear s) p) (.seq (uclear s) q)) R₃ R' (2*n+2+c+2) := by
    by_cases hn : 0<n
    · apply lr_ifNE_pos body (by simp [R₃]; omega)
      exact ec.seq (hp hn)
    · apply lr_ifNE_neg body (by simp [R₃]; omega)
      exact ec.seq (hq hn)
  exact (e1.seq (e2.seq (e3.seq ei))).mono (by unfold compactSynCompareCost; dsimp only [n,x,y]; omega)

end
end IntegerMultBounds.MathlibTM2.Fast
