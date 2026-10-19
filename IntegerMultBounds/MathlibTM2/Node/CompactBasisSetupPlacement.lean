module

public import IntegerMultBounds.MathlibTM2.Node.CompactRegisterEmbedding
public import IntegerMultBounds.MathlibTM2.Fast.SynBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! A fixed register permutation directs synthesized counters into the persistent compact bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section

def compactBasisOutputWire (i : Fin 7) : SynW := ![.s 15,.s 6,.s 26,.s 11,.s 16,.s 18,.s 19] i

def compactBasisOutputWork (i : Fin 7) : Fin 30 := ![3,4,5,7,9,13,14] i

/-- Swapping names before numbering avoids any change to the fixed global register count. -/
def compactBasisSetupPerm : Equiv.Perm (LReg CompactHostBReg) :=
  (Equiv.swap (.wire (synWire (.s 15))) (.bc (.inl (.work 3)))).trans <|
  (Equiv.swap (.wire (synWire (.s 6))) (.bc (.inl (.work 4)))).trans <|
  (Equiv.swap (.wire (synWire (.s 26))) (.bc (.inl (.work 5)))).trans <|
  (Equiv.swap (.wire (synWire (.s 11))) (.bc (.inl (.work 7)))).trans <|
  (Equiv.swap (.wire (synWire (.s 16))) (.bc (.inl (.work 9)))).trans <|
  (Equiv.swap (.wire (synWire (.s 18))) (.bc (.inl (.work 13)))).trans <|
  Equiv.swap (.wire (synWire (.s 19))) (.bc (.inl (.work 14)))

def compactBasisSetupReg (i : Fin (nT SXReg)) : Fin (nT CompactHostBReg) :=
  reg (compactBasisSetupPerm (compactMapRegName Sum.inr ((regEquiv SXReg).symm i)))

lemma compactBasisSetupReg_injective : Function.Injective compactBasisSetupReg :=
  reg_injective.comp (compactBasisSetupPerm.injective.comp
    ((compactMapRegName_injective Sum.inr_injective).comp (regEquiv SXReg).symm.injective))

@[simp] lemma compactBasisSetupReg_reg (x : LReg SXReg) :
    compactBasisSetupReg (reg x)=reg (compactBasisSetupPerm (compactMapRegName Sum.inr x)) := by
  simp [compactBasisSetupReg,reg]

lemma compactBasisSetupReg_output (i : Fin 7) :
    compactBasisSetupReg (sreg (compactBasisOutputWire i))=
      reg (.bc (.inl (.work (compactBasisOutputWork i)))) := by
  fin_cases i <;> simp [sreg_eq,compactMapRegName,compactBasisSetupPerm,
    compactBasisOutputWire,compactBasisOutputWork,Equiv.swap_apply_def]

lemma compactBasisSetupReg_source (x : SynW)
    (hx : ∀ i, x≠compactBasisOutputWire i) :
    compactBasisSetupReg (sreg x)=reg (.wire (synWire x)) := by
  have h15 := hx 0; have h6 := hx 1; have h26 := hx 2; have h11 := hx 3
  have h16 := hx 4; have h18 := hx 5; have h19 := hx 6
  change x≠.s 15 at h15
  change x≠.s 6 at h6
  change x≠.s 26 at h26
  change x≠.s 11 at h11
  change x≠.s 16 at h16
  change x≠.s 18 at h18
  change x≠.s 19 at h19
  simp [sreg_eq,compactMapRegName,compactBasisSetupPerm,Equiv.swap_apply_def,
    h15,h6,h26,h11,h16,h18,h19]

end
end IntegerMultBounds.MathlibTM2.LayerMachine
