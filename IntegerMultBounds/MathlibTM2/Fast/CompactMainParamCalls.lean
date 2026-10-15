module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainPrimitiveEntry

/-! Parameter code contains no recursive main calls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast.TableVM
noncomputable section

private lemma compile_calls {T Q A n : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR n → Fin T) (c : TblCode n) :
    callsWithin allowed (tblCompile (P := P) (U := U) (A := A) (Q := Q) rg c) := by
  induction c with
  | ins i => cases i <;> trivial
  | seq c d hc hd => exact ⟨hc,hd⟩
  | ite a b c d hc hd => exact ⟨by trivial,hc,hd⟩
  | loop a b c hc => exact ⟨by trivial,hc,by trivial⟩

private lemma zeroList_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR pmNV → Fin T) (xs : List (Fin pmNV)) :
    callsWithin allowed (pmZeroList (P := P) (U := U) (A := A) (Q := Q) rg xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨by trivial,ih⟩

private lemma unary_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR pmNV → Fin T) (xs : List (Fin pmNV × Fin T)) :
    callsWithin allowed (pmUnary (P := P) (U := U) (A := A) (Q := Q) rg xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨by trivial,ih⟩

private lemma params_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR pmNV → Fin T) (uN oT oS : Fin T) (us : List (Fin pmNV × Fin T)) :
    callsWithin allowed (pmParams (P := P) (U := U) (A := A) (Q := Q) rg uN oT oS us) := by
  simp only [pmParams,pmPrelude,pmPrelude2,pmHost,callsWithin,compile_calls,
    zeroList_calls,unary_calls]
  trivial

lemma compactMainParams_calls {A : ℕ} :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactMainStage (mnParams (A := A))) := by
  apply compactMainStage_calls
  unfold mnParams
  exact params_calls _ _ _ _ _ _

end
end IntegerMultBounds.MathlibTM2.Fast.Main
