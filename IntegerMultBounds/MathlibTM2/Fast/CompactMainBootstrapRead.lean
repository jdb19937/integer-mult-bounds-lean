module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainRegs
public import IntegerMultBounds.MathlibTM2.Node.CompactGlobalBootstrap

/-! Copy the original main inputs into bootstrap scratch, preserving their named sources. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactMnSyn (x : SynW) : Fin compactMnT := compactMnLay (.wire (synWire x))

lemma compactMnSyn_injective : Function.Injective compactMnSyn := by
  intro x y h
  exact synWire_inj (LReg.wire.inj (compactMnLay_injective h))

lemma compactMnSyn_legacy (x : SynW) :
    compactMnLayerReg (compactLegacyReg (sreg x))=compactMnSyn x := by
  simp only [sreg_eq,compactLegacyReg,compactMapReg_reg,compactMapRegName,
    compactMnLayerReg,reg_inj,reduceCtorEq,ite_false,compactMnSyn]
  rw [show reg (BReg:=CompactHostBReg) (.wire (synWire x)) =
    regEquiv CompactHostBReg (.wire (synWire x)) from rfl,Equiv.symm_apply_apply]

def compactMnBootstrapRead : Pr P compactMnT Q A U :=
  .seq (ucopy (compactMnRg (.io .dpn)) (compactMnSyn (.s 0)) (compactMnSyn (.s 2)))
    (ucopy (compactMnSyn (.p .D)) (compactMnSyn (.s 1)) (compactMnSyn (.s 2)))

def compactMnBootstrapCopied (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) :=
  Function.update (Function.update R (compactMnSyn (.s 0)) (List.replicate p tick))
    (compactMnSyn (.s 1)) (List.replicate d tick)

theorem compactMnBootstrapRead_runs (body : P → Pr P compactMnT Q A U)
    (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ)
    (hp : (R (compactMnRg (.io .dpn))).length=p)
    (hd : (R (compactMnLayerReg (compactLegacyReg (sreg (.p .D))))).length=d)
    (h0 : R (compactMnSyn (.s 0))=[]) (h1 : R (compactMnSyn (.s 1))=[])
    (h2 : R (compactMnSyn (.s 2))=[]) :
    LayRuns body compactMnBootstrapRead R (compactMnBootstrapCopied R p d)
      ((4*p+4)+(4*d+4)) := by
  rw [compactMnSyn_legacy] at hd
  have hne (x y : SynW) (h : x≠y) : compactMnSyn x≠compactMnSyn y :=
    fun he => h (compactMnSyn_injective he)
  have hp0 : compactMnRg (.io .dpn)≠compactMnSyn (.s 0) := compactMnRg_ne_lay _ _
  have hp2 : compactMnRg (.io .dpn)≠compactMnSyn (.s 2) := compactMnRg_ne_lay _ _
  have e₁ := lr_ucopy body hp0 hp2 (hne (.s 0) (.s 2) (by decide)) h2
  rw [hp,h0,List.append_nil] at e₁
  have e₂ := lr_ucopy body (R:=Function.update R (compactMnSyn (.s 0)) (List.replicate p tick))
    (hne (.p .D) (.s 1) (by decide)) (hne (.p .D) (.s 2) (by decide))
    (hne (.s 1) (.s 2) (by decide))
    (by rw [Function.update_of_ne (hne (.s 2) (.s 0) (by decide))]; exact h2)
  rw [Function.update_of_ne (hne (.p .D) (.s 0) (by decide)),hd,
    Function.update_of_ne (hne (.s 1) (.s 0) (by decide)),h1,List.append_nil] at e₂
  exact e₁.seq e₂

end
end IntegerMultBounds.MathlibTM2.Fast.Main
