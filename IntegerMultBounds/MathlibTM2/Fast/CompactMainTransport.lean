module

public import IntegerMultBounds.MathlibTM2.Host.StatePlacement
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainConstants
public import IntegerMultBounds.MathlibTM2.Fast.MainProg

/-! Executable legacy main stages on the expanded compact register and state capacities. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {A : ℕ}

/-- Disjoint names for old main procedures and the compact layer procedures. -/
abbrev CompactMainProc := MnProc ⊕ LProc

def compactMainOldProc : MnProc → CompactMainProc := Sum.inl

def compactMainLayerProc : LProc → CompactMainProc := Sum.inr

/-- Pure placement and state lift, with no extra step for an already embedded local state. -/
def compactMainTransport (p : MnPr A) : CompactMnPr CompactMainProc A :=
  statePlacedPr compactMnLegacyReg compactMnQ_legacy mnQ_pos compactMainOldProc p

/-- A stage entry usable after either legacy or compact code; its normalization costs one step. -/
def compactMainStage (p : MnPr A) : CompactMnPr CompactMainProc A :=
  statePlacedNormalized compactMnLegacyReg compactMnQ_legacy mnQ_pos compactMainOldProc p

/-- Old calls retain their exact table; the compact branch is separately supplied. -/
def compactMainTransportTable (legacy : MnProc → MnPr A)
    (compact : LProc → CompactMnPr CompactMainProc A) : CompactMainProc → CompactMnPr CompactMainProc A
  | .inl f => compactMainTransport (legacy f)
  | .inr f => compact f

@[simp] lemma compactMainTransportTable_old (legacy : MnProc → MnPr A)
    (compact : LProc → CompactMnPr CompactMainProc A) (f : MnProc) :
    compactMainTransportTable legacy compact (compactMainOldProc f)=compactMainTransport (legacy f) := rfl

/-- Concrete executable wrappers for unchanged main stages. -/
def compactMainRead : CompactMnPr CompactMainProc A := compactMainStage mnRead
def compactMainParams : CompactMnPr CompactMainProc A := compactMainStage mnParams
def compactMainPoint : CompactMnPr CompactMainProc A := compactMainStage mnPoint
def compactMainRound : CompactMnPr CompactMainProc A := compactMainStage mnRound
def compactMainOut : CompactMnPr CompactMainProc A := compactMainStage mnOut

def compactMainStateDown (v : HS compactMnT compactMnQ A Unit) : HS mnT mnQ A Unit :=
  stateLiftDown mnQ_pos (embDn compactMnLegacyReg v)

def compactMainFinalStacks (S₁ : Stacks mnT A) (S : Stacks compactMnT A) : Stacks compactMnT A :=
  embOvr compactMnLegacyReg S₁.get S

/-- Exact reuse of an old execution from an embedded local state, including recursive old calls. -/
theorem compactMainTransport_exec (legacy : MnProc → MnPr A)
    (compact : LProc → CompactMnPr CompactMainProc A)
    {p : MnPr A} {v₀ w : HS mnT mnQ A Unit} {S₀ S₁ : Stacks mnT A} {n : ℕ}
    (hrun : Exec legacy p (mk v₀ S₀) n (mk w S₁))
    (v : HS compactMnT compactMnQ A Unit)
    (hv : embDn compactMnLegacyReg v=stateLiftUp compactMnQ_legacy v₀)
    (S : Stacks compactMnT A) (hS : embStk compactMnLegacyReg S=S₀) :
    ∃ v',embDn compactMnLegacyReg v'=stateLiftUp compactMnQ_legacy w ∧ v'.user=w.user ∧
      Exec (compactMainTransportTable legacy compact) (compactMainTransport p)
        (mk v S) n (mk v' (compactMainFinalStacks S₁ S)) :=
  statePlaced_exec compactMnLegacyReg compactMnLegacyReg_injective compactMnQ_legacy mnQ_pos
    compactMainOldProc (compactMainTransportTable_old legacy compact) hrun v hv S hS

/-- Every old main-stage contract can run from an arbitrary expanded-host state for one extra step. -/
theorem compactMainStage_exec (legacy : MnProc → MnPr A)
    (compact : LProc → CompactMnPr CompactMainProc A) {p : MnPr A}
    (v : HS compactMnT compactMnQ A Unit) (S : Stacks compactMnT A)
    {w : HS mnT mnQ A Unit} {S₁ : Stacks mnT A} {n : ℕ}
    (hrun : Exec legacy p (mk (compactMainStateDown v) (embStk compactMnLegacyReg S)) n (mk w S₁)) :
    ∃ v',embDn compactMnLegacyReg v'=stateLiftUp compactMnQ_legacy w ∧ v'.user=w.user ∧
      Exec (compactMainTransportTable legacy compact) (compactMainStage p)
        (mk v S) (1+n) (mk v' (compactMainFinalStacks S₁ S)) :=
  statePlaced_exec_normalized compactMnLegacyReg compactMnLegacyReg_injective compactMnQ_legacy mnQ_pos
    compactMainOldProc (compactMainTransportTable_old legacy compact) v S hrun

/-- All old tapes, input, and output agree with the original final stack file. -/
lemma compactMainFinalStacks_projection (S₁ : Stacks mnT A) (S : Stacks compactMnT A) :
    embStk compactMnLegacyReg (compactMainFinalStacks S₁ S)=S₁ :=
  embStk_ovr compactMnLegacyReg_injective S₁ S

private lemma placedStacks_io {T T' : ℕ} (e : Fin T → Fin T') (S₁ : Stacks T A) (S : Stacks T' A) :
    (embOvr e S₁.get S).inp=S₁.inp ∧ (embOvr e S₁.get S).out=S₁.out := ⟨rfl,rfl⟩

lemma compactMainFinalStacks_io (S₁ : Stacks mnT A) (S : Stacks compactMnT A) :
    (compactMainFinalStacks S₁ S).inp=S₁.inp ∧ (compactMainFinalStacks S₁ S).out=S₁.out :=
  placedStacks_io compactMnLegacyReg S₁ S

/-- The compact private bank survives every transported legacy stage unchanged. -/
lemma compactMainFinalStacks_private (S₁ : Stacks mnT A) (S : Stacks compactMnT A) (b : CompactBReg) :
    (compactMainFinalStacks S₁ S).L (compactMnLay (.bc (.inl b)))=S.L (compactMnLay (.bc (.inl b))) ∧
    (compactMainFinalStacks S₁ S).R (compactMnLay (.bc (.inl b)))=S.R (compactMnLay (.bc (.inl b))) :=
  embOvr_off S₁.get S (fun i => compactMnLegacyReg_ne_private i b)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
