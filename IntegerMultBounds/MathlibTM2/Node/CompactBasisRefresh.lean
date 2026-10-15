module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetup
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisCleanup
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefreshPlacement

/-! Per-round five-counter refresh. Original depth/guard remain untouched in work13/work14. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {T Q A : ℕ} {U P : Type}

def compactZeroTail (values : Fin 7 → ℕ) := Function.update (Function.update values 5 0) 6 0

def compactClearTail (e : Fin 7 → Fin T) : Pr P T Q A U := .seq (uclear (e 5)) (uclear (e 6))

def compactClearTailCost (values : Fin 7 → ℕ) := (2*values 5+2)+(2*values 6+2)

lemma compactClearTailCost_vector (x0 x1 x2 x3 x4 x5 x6 : ℕ) :
    compactClearTailCost ![x0,x1,x2,x3,x4,x5,x6]=(2*x5+2)+(2*x6+2) := rfl

theorem compactClearTail_runs (body : P → Pr P T Q A U) (e : Fin 7 → Fin T)
    (he : Function.Injective e) (R : Fin T → List (Fin (A+4))) (values : Fin 7 → ℕ) :
    LayRuns body (compactClearTail e) (compactSetupUpdate7 R e values)
      (compactSetupUpdate7 R e (compactZeroTail values)) (compactClearTailCost values) := by
  refine lr_weaken body
    ((lr_uclear body (R:=compactSetupUpdate7 R e values) (e 5)).seq (lr_uclear body (e 6))) ?_ ?_
  · funext z
    by_cases h5 : z=e 5
    · subst z; simp [compactSetupUpdate7,compactZeroTail,he.eq_iff]
    by_cases h6 : z=e 6
    · subst z; simp [compactSetupUpdate7,compactZeroTail]
    simp [compactSetupUpdate7,compactZeroTail,Function.update_of_ne,h5,h6]
  · simp [compactSetupUpdate7,he.eq_iff,compactClearTailCost]

theorem compactSetup7_clearTail_exec {T T' : ℕ}
    (e : Fin T → Fin T') (he : Function.Injective e) (body : P → Pr P T' Q A U)
    {p : Pr Empty T Q A U} {R : Fin T → List (Fin (A+4))}
    {src : Fin 7 → Fin T} (hsrc : Function.Injective src) {values : Fin 7 → ℕ} {c : ℕ}
    (h : LayRuns (fun f : Empty => f.elim) p R (compactSetupUpdate7 R src values) c)
    (v : HS T' Q A U) (S : Stacks T' A) (hL : ∀ i,S.L i=[]) (hR : S.R ∘ e=R) :
    ∃ v' steps,v'.user=v.user ∧ steps≤c+compactClearTailCost values ∧
      Exec body (.seq (embProg e (fun f : Empty => f.elim) p) (compactClearTail (e ∘ src)))
        (mk v S) steps (mk v' {S with R:=compactSetupUpdate7 S.R (e ∘ src) (compactZeroTail values)}) := by
  obtain ⟨v₁,c₁,hu₁,hc₁,he₁⟩ := compactSetup7_exec e he body h v S (fun i => hL (e i)) hR
  obtain ⟨v₂,c₂,hu₂,hc₂,he₂⟩ := compactClearTail_runs body (e ∘ src) (he.comp hsrc) S.R values
    v₁ {S with R:=compactSetupUpdate7 S.R (e ∘ src) values} hL rfl
  exact ⟨v₂,c₁+c₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂⟩

def compactBasisRefresh : Pr P (nT CompactHostBReg) Q A U :=
  .seq (embProg compactBasisRefreshReg (fun f : Empty => f.elim) (compactBasisCounts (P:=Empty)))
    (compactClearTail compactBasisRefreshDst)

def compactBasisRefreshCost (d g K D o r : ℕ) :=
  compactBasisCountsCost d g K D o r+(2*d+2)+(2*g+2)

/-- Only o/back/active/bits/r are initialized. Temporary copies of original d/g are
cleared; the globally retained work13/work14 are never in the execution's register image. -/
theorem compactBasisRefresh_exec (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d g K D o r : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D)
    (ho : (v (.s 7)).length=o) (hr : (v (.p .r)).length=r)
    (hs : ∀ i : Fin 32,i≠0 → i≠1 → i≠7 → v (.s i)=[])
    (vbig : HS (nT CompactHostBReg) Q A U) (S : Stacks (nT CompactHostBReg) A)
    (hL : ∀ i,S.L i=[]) (hR : S.R ∘ compactBasisRefreshReg=synG R v) :
    ∃ v' steps,v'.user=vbig.user ∧ steps≤compactBasisRefreshCost d g K D o r ∧
      Exec body compactBasisRefresh (mk vbig S) steps
        (mk v' {S with R:=(compactSetupUpdate7 S.R compactBasisRefreshDst
          (compactZeroTail (compactBasisSetupValues d g K D o r)))}) := by
  have h := sg_compactBasisCounts (Q:=Q) (A:=A) (U:=U) (fun f : Empty => f.elim)
    R v d g K D o r hdpos hk hd hg hK hD ho hr hs
  rw [compactBasisCountsOutput_file] at h
  have he : compactBasisRefreshReg ∘ (sreg ∘ compactBasisOutputWire)=compactBasisRefreshDst := by
    funext i
    exact compactBasisRefreshReg_output i
  have hsrc : Function.Injective (sreg ∘ compactBasisOutputWire) :=
    sreg_injective.comp (show Function.Injective compactBasisOutputWire by decide)
  have hrun := compactSetup7_clearTail_exec compactBasisRefreshReg compactBasisRefreshReg_injective body
    hsrc h vbig S hL hR
  rw [he] at hrun
  rw [compactClearTailCost_vector] at hrun
  have hcost : compactBasisCountsCost d g K D o r+((2*d+2)+(2*g+2))=
      compactBasisRefreshCost d g K D o r := (Nat.add_assoc _ _ _).symm
  rw [hcost] at hrun
  exact hrun

/-- Per-round cleanup restores the five initially blank fields while retaining global d/g. -/
def compactBasisRefreshCleanup : Pr P (nT CompactHostBReg) Q A U := compactClear7 compactBasisRefreshDst

theorem compactBasisRefreshCleanup_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (values : Fin 7 → ℕ)
    (hz : ∀ i,R (compactBasisRefreshDst i)=[]) :
    LayRuns body compactBasisRefreshCleanup
      (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values)) R
      (compactClear7Cost (compactZeroTail values)) :=
  compactClear7_runs body compactBasisRefreshDst compactBasisRefreshDst_injective R (compactZeroTail values) hz

lemma compactBasisRefresh_preserves_global (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (values : Fin 7 → ℕ) (i : Fin 30) (hi : i=13 ∨ i=14) :
    compactSetupUpdate7 R compactBasisRefreshDst values (reg (.bc (.inl (.work i))))=
      R (reg (.bc (.inl (.work i)))) := by
  apply compactSetupUpdate7_off
  intro j
  rcases hi with rfl | rfl <;> fin_cases j <;>
    simp [compactBasisRefreshDst,compactBasisRefreshWork,reg_inj]

end
end IntegerMultBounds.MathlibTM2.LayerMachine
