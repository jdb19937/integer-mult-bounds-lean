module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasis
public import IntegerMultBounds.MathlibTM2.Node.Regs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Concrete layer-machine wiring for compact basis changes. Global reservation
counters persist in bc registers; current-node parameters alias the layer counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section

inductive CompactBReg where
  | slot (x : CxSlotReg)
  | work (i : Fin 30)
  deriving DecidableEq, Fintype

def compactBasisNative (x : CxSlotReg) : Fin (nT CompactBReg) :=
  reg (.bc (.slot x))

lemma compactBasisNative_injective : Function.Injective compactBasisNative := by
  intro i j h
  simpa [compactBasisNative] using h

lemma compactBasisNative_count : swapT 6 ≤ nT CompactBReg := by
  have h : Function.Injective fun j : Fin (swapT 6) => compactBasisNative (.bank 0 j) :=
    fun a b e => by simpa using compactBasisNative_injective e
  simpa using Fintype.card_le_of_injective _ h

/-- Dynamic node parameters are aliases, so child calls automatically expose the
current offset, row count, total width and residue to the descriptor builder. -/
def compactBasisRole (i : Fin 30) : LReg CompactBReg :=
  if i=1 then .K else if i=2 then .a₀ else if i=6 then .n else if i=8 then .rows
  else if i=10 then .w else if i=15 then .ρ else .bc (.work i)

def compactBasisDescriptor (i : Fin 30) : Fin (nT CompactBReg) := reg (compactBasisRole i)

lemma compactBasisDescriptor_injective : Function.Injective compactBasisDescriptor := by
  intro i j h
  have hh := reg_injective h
  unfold compactBasisRole at hh
  split_ifs at hh <;> simp_all

lemma compactBasisDescriptor_native (i : Fin 30) (j : CxSlotReg) :
    compactBasisDescriptor i≠compactBasisNative j := by
  simp only [compactBasisDescriptor,compactBasisNative,ne_eq,reg_inj]
  unfold compactBasisRole
  split_ifs <;> simp

lemma compactBasisDescriptor_L (i : Fin 30) : reg (BReg:=CompactBReg) .L≠compactBasisDescriptor i := by
  simp only [compactBasisDescriptor,ne_eq,reg_inj]
  unfold compactBasisRole
  split_ifs <;> simp

lemma compactBasisDescriptor_wire (i : Fin 30) (fw : NWire) :
    compactBasisDescriptor i≠reg (.wire fw) := by
  simp only [compactBasisDescriptor,ne_eq,reg_inj]
  unfold compactBasisRole
  split_ifs <;> simp

lemma compactBasisDescriptor_tmp (i : Fin 30) : compactBasisDescriptor i≠reg .tmp := by
  simp only [compactBasisDescriptor,ne_eq,reg_inj]
  unfold compactBasisRole
  split_ifs <;> simp

/-- The seven persistent global inputs; all other bc registers are empty at rest.
The unused work copies of aliased layer parameters also remain empty. -/
def compactBasisRest {A : ℕ} (s : Shape) (o r : ℕ) : CompactBReg → List (Fin (A+4)) → Prop
  | .slot _, l => l=[]
  | .work i, l =>
    if i=3 then l.length=o else if i=4 then l.length=s.H+s.B
    else if i=5 then l.length=s.active else if i=7 then l.length=s.bits
    else if i=9 then l.length=r else if i=13 then l.length=s.axes
    else if i=14 then l.length=s.guard else l=[]

variable {Q K : ℕ} {U P : Type}

def compactBasisW (hQ : compactRuntimeStates ≤ Q) (fw : NWire)
    (vv : BinaryWalsh.Address m) (x : Fin m) : Pr P (nT CompactBReg) Q (prime+K) U :=
  compactBasisProg x hQ compactBasisNative compactBasisNative_injective compactBasisNative_count
    compactBasisDescriptor (reg .L) (reg (.wire fw)) (fun i => by simp [compactBasisNative]) vv

/-- A concrete basisW contract on the generic layer register file. Persistent
reservation counters survive literally, as do the child slot length and all other wires. -/
theorem compactBasisW_exec {s : Shape} {n a₀ k ρ left right o rowCount r w j u : ℕ}
    (body : P → Pr P (nT CompactBReg) Q (prime+K) U) (hQ : compactRuntimeStates ≤ Q)
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x : Fin m)
    (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk) (hr : 0<rowCount)
    (hrecord : s.bits+1 ≤ s.payload) (hA : 4 ≤ prime+K)
    (hpayload : s.payload=2^o*(3*(r*w))) (D : ℕ)
    (hp : CompactSlotPacked s k (2^(n-s.bits)*rowCount) D)
    (fw : NWire) (vv : BinaryWalsh.Address m) (hv : vv x=1)
    (Z : ZArr (Fin rowCount × Fin r) (o+n))
    (v : HS (nT CompactBReg) Q (prime+K) U) (S : Stacks (nT CompactBReg) (prime+K))
    (hL : ∀ z,S.L z=[])
    (hpar : ParState S.R j u s.chunk ρ (o+a₀) (s.chunk*k) rowCount (o+n) w (r*w))
    (hbc : ∀ z,compactBasisRest s o r z (S.R (reg (.bc z))))
    (_htmp : S.R (reg .tmp)=[]) (hstream : S.R (reg (.wire fw))=encZ (prime+K) w Z) :
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ ((basisTargets vv x).map
        (compactBasisTargetCost layout x hG hGK hr hrecord D hp (nT CompactBReg) K o r w)).sum+1 ∧
      Exec body (compactBasisW hQ fw vv x) (mk v S) steps
        (mk v' {S with R:=Function.update S.R (reg (.wire fw)) (encZ (prime+K) w
          (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (basisMap vv x) Z))}) := by
  have hin : ∀ i : Fin 16,i≠0 → i≠11 → i≠12 →
      (S.R (compactBasisDescriptor (Fin.castAdd 14 i))).length=
        compactDescriptorBankInputs layout o rowCount r w x x i := by
    intro i hi0 hi11 hi12
    fin_cases i
    · exact (hi0 rfl).elim
    · exact hpar .K
    · exact hpar .a₀
    · exact hbc (.work 3)
    · exact hbc (.work 4)
    · exact hbc (.work 5)
    · exact hpar .n
    · exact hbc (.work 7)
    · exact hpar .rows
    · exact hbc (.work 9)
    · exact hpar .w
    · exact (hi11 rfl).elim
    · exact (hi12 rfl).elim
    · exact hbc (.work 13)
    · exact hbc (.work 14)
    · exact hpar .ρ
  exact compactBasis_exec layout x hG hGK hr hrecord D hp body hQ compactBasisNative
    compactBasisNative_injective compactBasisNative_count compactBasisDescriptor
    compactBasisDescriptor_injective (reg .L) (reg (.wire fw)) compactBasisDescriptor_L
    (reg_ne (by simp)) compactBasisDescriptor_native (fun i => compactBasisDescriptor_wire i fw)
    (fun j => by simp [compactBasisNative]) (fun j => by simp [compactBasisNative])
    hA hpayload vv hv Z v S hL (fun i => hbc (.slot i)) (hpar .L) hstream hin

end
end IntegerMultBounds.MathlibTM2.LayerMachine
