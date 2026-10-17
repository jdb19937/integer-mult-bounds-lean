module

public import IntegerMultBounds.MathlibTM2.Node.CompactGlobalBootstrapCounts
import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupRest
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupFrame
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Bootstrap original depth/guard into the shared persistent bank, clearing the copied inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactGlobalBootstrapSource (i : Fin 7) : SynW := ![.s 19,.s 18,.s 0,.s 1,.s 6,.s 15,.s 26] i

def compactGlobalBootstrapValues (p d : ℕ) : Fin 7 → ℕ := ![4*Nat.clog 2 p+6,d,0,0,0,0,0]

def compactGlobalBootstrapDst : Fin 7 → Fin (nT CompactHostBReg) :=
  compactBasisSetupReg ∘ (sreg ∘ compactGlobalBootstrapSource)

lemma compactGlobalBootstrapDst_injective : Function.Injective compactGlobalBootstrapDst :=
  compactBasisSetupReg_injective.comp (sreg_injective.comp
    (show Function.Injective compactGlobalBootstrapSource by decide))

@[simp] lemma compactGlobalBootstrapDst_guard :
    compactGlobalBootstrapDst 0=reg (.bc (.inl (.work 14))) := compactBasisSetupReg_output 6

@[simp] lemma compactGlobalBootstrapDst_depth :
    compactGlobalBootstrapDst 1=reg (.bc (.inl (.work 13))) := compactBasisSetupReg_output 5

@[simp] lemma compactGlobalBootstrapDst_p :
    compactGlobalBootstrapDst 2=reg (.wire (synWire (.s 0))) :=
  compactBasisSetupReg_source (.s 0) (by intro i; fin_cases i <;> simp [compactBasisOutputWire])

@[simp] lemma compactGlobalBootstrapDst_d :
    compactGlobalBootstrapDst 3=reg (.wire (synWire (.s 1))) :=
  compactBasisSetupReg_source (.s 1) (by intro i; fin_cases i <;> simp [compactBasisOutputWire])

/-- Original unary p/d are copied to s0/s1 by the caller; both copies are consumed.
No assumption identifies the original precision with a working coefficient width. -/
def compactGlobalBootstrap : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactBasisSetupReg (fun f : Empty => f.elim) (compactGlobalBootstrapCounts (P:=Empty))

private theorem compactGlobalBootstrap_output
    (v : SynW → List (Fin (A+4))) (p d : ℕ)
    (h6 : v (.s 6)=[]) (h15 : v (.s 15)=[]) (h26 : v (.s 26)=[]) :
    Function.update (Function.update (Function.update (Function.update v
      (.s 19) (List.replicate (4*Nat.clog 2 p+6) tick)) (.s 18) (List.replicate d tick))
      (.s 0) []) (.s 1) [] =
    compactSetupUpdate7 v compactGlobalBootstrapSource (compactGlobalBootstrapValues p d) := by
  funext z
  by_cases h6z : z=.s 6
  · subst z; simp [compactSetupUpdate7,compactGlobalBootstrapSource,compactGlobalBootstrapValues,h6]
  by_cases h15z : z=.s 15
  · subst z; simp [compactSetupUpdate7,compactGlobalBootstrapSource,compactGlobalBootstrapValues,h15]
  by_cases h26z : z=.s 26
  · subst z; simp [compactSetupUpdate7,compactGlobalBootstrapSource,compactGlobalBootstrapValues,h26]
  simp [compactSetupUpdate7,compactGlobalBootstrapSource,compactGlobalBootstrapValues,
    Function.update_of_ne,h6z,h15z,h26z]

theorem compactGlobalBootstrap_exec (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (p d : ℕ) (hp : 2≤p) (h0 : (v (.s 0)).length=p) (h1 : (v (.s 1)).length=d)
    (hz : ∀ i : Fin 32,i∈[2,6,9,10,12,15,17,18,19,23,26] → v (.s i)=[])
    (vbig : HS (nT CompactHostBReg) Q A U) (S : Stacks (nT CompactHostBReg) A)
    (hL : ∀ i,S.L (compactBasisSetupReg i)=[]) (hR : S.R ∘ compactBasisSetupReg=synG R v) :
    ∃ v' steps,v'.user=vbig.user ∧ steps≤compactGlobalBootstrapCost p d ∧
      Exec body compactGlobalBootstrap (mk vbig S) steps
        (mk v' {S with R:=compactSetupUpdate7 S.R compactGlobalBootstrapDst (compactGlobalBootstrapValues p d)}) := by
  have h := sg_compactGlobalBootstrapCounts (Q:=Q) (A:=A) (U:=U) (fun f : Empty => f.elim)
    R v p d hp h0 h1 (fun i hi => hz i (by simp only [List.mem_cons] at hi ⊢; tauto))
  have hout := (congrArg (synG R) (compactGlobalBootstrap_output v p d
    (hz 6 (by simp)) (hz 15 (by simp)) (hz 26 (by simp)))).trans
    (compactSetupUpdate7_map (synG R) sreg (fun v x l => (synG_update (R:=R) (v:=v) x l).symm)
      v compactGlobalBootstrapSource (compactGlobalBootstrapValues p d))
  rw [hout] at h
  exact compactSetup7_exec compactBasisSetupReg compactBasisSetupReg_injective body h vbig S hL hR

/-- The global counters are canonical and the two copied input slots are empty. -/
theorem compactGlobalBootstrap_initialized
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (p d : ℕ) :
    let R' := compactSetupUpdate7 R compactGlobalBootstrapDst (compactGlobalBootstrapValues p d)
    R' (reg (.bc (.inl (.work 13))))=List.replicate d tick ∧
    R' (reg (.bc (.inl (.work 14))))=List.replicate (4*Nat.clog 2 p+6) tick ∧
    R' (reg (.wire (synWire (.s 0))))=[] ∧ R' (reg (.wire (synWire (.s 1))))=[] := by
  have hget := compactSetupUpdate7_get compactGlobalBootstrapDst compactGlobalBootstrapDst_injective
    R (compactGlobalBootstrapValues p d)
  exact ⟨by simpa [compactGlobalBootstrapValues] using hget 1,
    by simpa [compactGlobalBootstrapValues] using hget 0,
    by simpa [compactGlobalBootstrapValues] using hget 2,
    by simpa [compactGlobalBootstrapValues] using hget 3⟩

end
end IntegerMultBounds.MathlibTM2.LayerMachine
