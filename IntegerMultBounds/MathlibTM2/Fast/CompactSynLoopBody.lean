module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Actual counter setup and cleanup around each hybrid transform round. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

def compactCounterBody {T Q A : ℕ} {P U : Type} (a h t : Fin T) (pred : Bool)
    (round : Pr P T Q A U) : Pr P T Q A U :=
  .seq (ucopy a h t) (.seq (if pred then synPop h else synSkip) (.seq round (uclear h)))

theorem compactCounterBody_runs {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    {a h t io : Fin T} (hah : a≠h) (hat : a≠t) (hht : h≠t) (hio : h≠io)
    {R : Fin T → List (Fin (A+4))} (hh : R h=[]) (ht : R t=[])
    (pred : Bool) (out : List (Fin (A+4))) {round : Pr P T Q A U} {c : ℕ}
    (hrun : LayRuns body round
      (Function.update R h (List.replicate ((R a).length-(if pred then 1 else 0)) tick))
      (Function.update (Function.update R h (List.replicate ((R a).length-(if pred then 1 else 0)) tick)) io out) c) :
    LayRuns body (compactCounterBody a h t pred round) R (Function.update R io out)
      ((4*(R a).length+4)+1+c+(2*((R a).length-(if pred then 1 else 0))+2)) := by
  let y := (R a).length
  let n := y-(if pred then 1 else 0)
  let R₁ := Function.update R h (List.replicate y tick)
  let R₂ := Function.update R h (List.replicate n tick)
  have e1 : LayRuns body (ucopy a h t) R R₁ (4*y+4) := by
    simpa only [hh,List.append_nil] using lr_ucopy body hah hat hht ht
  have e2 : LayRuns body (if pred then synPop h else synSkip) R₁ R₂ 1 := by
    cases pred
    · simpa [R₁,R₂,n] using lr_skip body R₁
    · simpa only [R₁,R₂,n,ite_true,Function.update_self,List.tail_replicate,Function.update_idem] using lr_pop body (R := R₁) h
  have er : Function.update (Function.update R₂ io out) h []=Function.update R io out := by
    funext j
    by_cases hj : j=h
    · subst j; simp [R₂,hh,hio]
    · by_cases hi : j=io
      · subst j; simp [R₂,hj]
      · simp [R₂,hj,hi]
  have e3 : LayRuns body (uclear h) (Function.update R₂ io out) (Function.update R io out) (2*n+2) := by
    simpa only [er,Function.update_of_ne hio,R₂,Function.update_self,List.length_replicate] using
      lr_uclear body (R := Function.update R₂ io out) h
  exact (e1.seq (e2.seq (hrun.seq e3))).mono (by dsimp only [n,y]; omega)

theorem compactSynDispatchReg_ne_io (x : SynW) :
    compactSynDispatchReg x≠compactMnRg (.src (.v .io)) := by
  rw [←compactMnLegacyReg_rg,←mnLayE_io]
  exact compactMnLegacyReg_injective.ne (mnLayE_inj.ne (lreg_out (by simp) x))

def compactSynBodyF (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  compactCounterBody (compactSynDispatchReg (.p .c)) (compactSynDispatchReg (.p .h))
    (compactSynDispatchReg (.s 2)) false (compactSynRoundF ds)

def compactSynBodyO (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  compactCounterBody (compactSynDispatchReg (.p .t)) (compactSynDispatchReg (.p .h))
    (compactSynDispatchReg (.s 2)) true (compactSynRoundO ds)

def compactSynLoopF (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  scanP (compactSynDispatchReg (.p .c)) (compactSynDispatchReg (.p .t)) (compactSynBodyF ds)

def compactSynLoopO (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  scanP (compactSynDispatchReg (.p .c)) (compactSynDispatchReg (.p .t)) (compactSynBodyO ds)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
