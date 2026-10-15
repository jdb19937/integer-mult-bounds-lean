module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupPlacement

/-! A fixed register permutation directs synthesized counters into the persistent compact bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section

def compactBasisRefreshWork (i : Fin 7) : Fin 30 := ![3,4,5,7,9,0,11] i

/-- Swapping names before numbering avoids any change to the fixed global register count. -/
def compactBasisRefreshPerm : Equiv.Perm (LReg CompactHostBReg) :=
  (Equiv.swap (.wire (synWire (.s 15))) (.bc (.inl (.work 3)))).trans <|
  (Equiv.swap (.wire (synWire (.s 6))) (.bc (.inl (.work 4)))).trans <|
  (Equiv.swap (.wire (synWire (.s 26))) (.bc (.inl (.work 5)))).trans <|
  (Equiv.swap (.wire (synWire (.s 11))) (.bc (.inl (.work 7)))).trans <|
  (Equiv.swap (.wire (synWire (.s 16))) (.bc (.inl (.work 9)))).trans <|
  (Equiv.swap (.wire (synWire (.s 18))) (.bc (.inl (.work 0)))).trans <|
  Equiv.swap (.wire (synWire (.s 19))) (.bc (.inl (.work 11)))

def compactBasisRefreshReg (i : Fin (nT SXReg)) : Fin (nT CompactHostBReg) :=
  reg (compactBasisRefreshPerm (compactMapRegName Sum.inr ((regEquiv SXReg).symm i)))

lemma compactBasisRefreshReg_injective : Function.Injective compactBasisRefreshReg :=
  reg_injective.comp (compactBasisRefreshPerm.injective.comp
    ((compactMapRegName_injective Sum.inr_injective).comp (regEquiv SXReg).symm.injective))

@[simp] lemma compactBasisRefreshReg_reg (x : LReg SXReg) :
    compactBasisRefreshReg (reg x)=reg (compactBasisRefreshPerm (compactMapRegName Sum.inr x)) := by
  simp [compactBasisRefreshReg,reg]

lemma compactBasisRefreshReg_output (i : Fin 7) :
    compactBasisRefreshReg (sreg (compactBasisOutputWire i))=
      reg (.bc (.inl (.work (compactBasisRefreshWork i)))) := by
  fin_cases i <;> simp [sreg_eq,compactMapRegName,compactBasisRefreshPerm,
    compactBasisOutputWire,compactBasisRefreshWork,Equiv.swap_apply_def]

lemma compactBasisRefreshReg_source (x : SynW)
    (hx : ∀ i, x≠compactBasisOutputWire i) :
    compactBasisRefreshReg (sreg x)=reg (.wire (synWire x)) := by
  have h15 := hx 0; have h6 := hx 1; have h26 := hx 2; have h11 := hx 3
  have h16 := hx 4; have h18 := hx 5; have h19 := hx 6
  change x≠.s 15 at h15
  change x≠.s 6 at h6
  change x≠.s 26 at h26
  change x≠.s 11 at h11
  change x≠.s 16 at h16
  change x≠.s 18 at h18
  change x≠.s 19 at h19
  simp [sreg_eq,compactMapRegName,compactBasisRefreshPerm,Equiv.swap_apply_def,
    h15,h6,h26,h11,h16,h18,h19]

/-- Five persistent outputs and two temporary copies, which are cleared immediately. -/
def compactBasisRefreshDst (i : Fin 7) : Fin (nT CompactHostBReg) :=
  reg (.bc (.inl (.work (compactBasisRefreshWork i))))

lemma compactBasisRefreshDst_injective : Function.Injective compactBasisRefreshDst := by
  intro i j h
  have hh : compactBasisRefreshWork i=compactBasisRefreshWork j := by
    simpa only [compactBasisRefreshDst,reg_inj,LReg.bc.injEq,Sum.inl.injEq,CompactBReg.work.injEq] using h
  exact (show Function.Injective compactBasisRefreshWork by decide) hh

end
end IntegerMultBounds.MathlibTM2.LayerMachine
