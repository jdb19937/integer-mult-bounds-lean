module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupOutput

/-! Actual persistent compact bank setup, with original source words and all scratch restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape (Shape)
open IntegerMultBounds.MathlibTM2.Layer
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Call-free setup program on the actual shared host. -/
def compactBasisSetup : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactBasisSetupReg (fun f : Empty => f.elim) (compactBasisCounts (P:=Empty))

/-- Exact frame: only the seven persistent counters change; all original input words,
all legacy private registers, and every arithmetic scratch word are preserved. -/
theorem compactBasisSetup_exec (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d g K D o r : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D)
    (ho : (v (.s 7)).length=o) (hr : (v (.p .r)).length=r)
    (hs : ∀ i : Fin 32,i≠0 → i≠1 → i≠7 → v (.s i)=[])
    (vbig : HS (nT CompactHostBReg) Q A U) (S : Stacks (nT CompactHostBReg) A)
    (hL : ∀ i,S.L (compactBasisSetupReg i)=[]) (hR : S.R ∘ compactBasisSetupReg=synG R v) :
    ∃ v' steps,v'.user=vbig.user ∧ steps≤compactBasisCountsCost d g K D o r ∧
      Exec body compactBasisSetup (mk vbig S) steps
        (mk v' {S with R:=compactSetupUpdate7 S.R compactBasisPersistent (compactBasisSetupValues d g K D o r)}) := by
  have h := sg_compactBasisCounts (Q:=Q) (A:=A) (U:=U) (fun f : Empty => f.elim) R v d g K D o r hdpos hk hd hg hK hD ho hr hs
  rw [compactBasisCountsOutput_file] at h
  have he : compactBasisSetupReg ∘ (sreg ∘ compactBasisOutputWire)=compactBasisPersistent := by
    funext i
    exact compactBasisSetupReg_output i
  have hrun := compactSetup7_exec compactBasisSetupReg compactBasisSetupReg_injective body h vbig S hL hR
  rw [he] at hrun
  exact hrun

end
end IntegerMultBounds.MathlibTM2.LayerMachine
