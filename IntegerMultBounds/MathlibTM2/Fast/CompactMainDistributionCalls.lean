module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainPrimitiveEntry
public import IntegerMultBounds.MathlibTM2.Fast.CompactBundleWires

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

private lemma push_calls {T Q A n : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR n → Fin T) (xs : List (Fin T × Fin n × DsMode)) :
    callsWithin allowed (dsPush (P:=P) (U:=U) (Q:=Q) (A:=A) rg xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    rcases x with ⟨o,x,b⟩
    cases b <;> exact ⟨by trivial,ih⟩

private lemma zero_calls {T Q A n : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR n → Fin T) (xs : List (Fin n)) :
    callsWithin allowed (dsZeroVars (P:=P) (U:=U) (Q:=Q) (A:=A) rg xs) ∧
    callsWithin allowed (dsClearVars (P:=P) (U:=U) (Q:=Q) (A:=A) rg xs) := by
  induction xs with
  | nil => exact ⟨True.intro,True.intro⟩
  | cons x xs ih => exact ⟨⟨by trivial,ih.1⟩,⟨by trivial,ih.2⟩⟩

private lemma unL_calls {T Q A t₀ : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) (xs : List (Fin pmNV × DsY t₀)) :
    callsWithin allowed (dsUnL (P:=P) (U:=U) (Q:=Q) (A:=A) rg g xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨by trivial,ih⟩

private lemma copyL_calls {T Q A t₀ : ℕ} {P U : Type} (allowed : P → Prop)
    (g : DsY t₀ → Fin T) (src tm : DsY t₀) (xs : List (DsY t₀)) :
    callsWithin allowed (dsCopyL (P:=P) (U:=U) (Q:=Q) (A:=A) g src tm xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨by trivial,ih⟩

private lemma main_calls {T Q A t₀ : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) :
    callsWithin allowed (dsMain (P:=P) (U:=U) (Q:=Q) (A:=A) rg g) := by
  simp only [dsMain,dsWid,dsSrc,dsStep,dsStepB,dsP1,dsPC,dsP2a,dsP2b,dsP2c,
    dsAxes,dsAxBody,dsGLoop,dsGBody,dsTwist,tblHost,scanP,callsWithin,
    compile_calls,push_calls,unL_calls,copyL_calls,(zero_calls allowed _ _).1,(zero_calls allowed _ _).2]
  repeat' apply And.intro
  all_goals trivial

private lemma wire_zero_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR 40 → Fin T) (xs : List (Fin 40)) :
    callsWithin allowed (dsyZeroVars (P:=P) (U:=U) (Q:=Q) (A:=A) rg xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨by trivial,ih⟩

private lemma wire_clear_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR 40 → Fin T) (xs : List (TblR 40)) :
    callsWithin allowed (dsyClearL (P:=P) (U:=U) (Q:=Q) (A:=A) rg xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨by trivial,ih⟩

private lemma wires_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : TblR 40 → Fin T) (io : DsX → Fin T) (oPark oB oLg oL oNr oRec oPos : Fin T) :
    callsWithin allowed (dsySyn (P:=P) (U:=U) (Q:=Q) (A:=A) rg io oPark oB oLg oL oNr oRec oPos) := by
  simp only [dsySyn,dsyPhase,dsyPhase0,callsWithin,compile_calls,wire_zero_calls,wire_clear_calls]
  repeat' apply And.intro
  all_goals trivial

lemma compactMainDistribution_calls
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ),MnPostParam R n → BdPostParam R n) :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactMainStage (compactBdDist hP).distP) := by
  apply compactMainStage_calls
  change callsWithin (fun f : MnProc => f≠.main)
    (.seq (.seq (dsMain mnPm bdG) bdRnd) (.seq (compactDsRetune mnPm (bdIo .lK)) dsyProg))
  refine ⟨⟨main_calls _ _ _,?_⟩,?_,?_⟩
  · simp only [bdRnd,dsStep,dsStepB,callsWithin,compile_calls]
    repeat' apply And.intro
    all_goals trivial
  · simp only [compactDsRetune,callsWithin,compile_calls]
    trivial
  · exact ⟨wires_calls _ _ _ _ _ _ _ _ _ _,by trivial⟩

end
end IntegerMultBounds.MathlibTM2.Fast.Main
