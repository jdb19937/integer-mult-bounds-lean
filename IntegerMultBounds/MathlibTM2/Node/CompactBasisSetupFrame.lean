module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupCounts
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupPlacement
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerPlaced
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopPlaced

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

/-- A finite output file, independent of host register counts. -/
def compactSetupUpdate7 {I : Type} [DecidableEq I] (R : I → List (Fin (A+4)))
    (e : Fin 7 → I) (values : Fin 7 → ℕ) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update R (e 0) (List.replicate (values 0) tick))
      (e 1) (List.replicate (values 1) tick)) (e 2) (List.replicate (values 2) tick))
      (e 3) (List.replicate (values 3) tick)) (e 4) (List.replicate (values 4) tick))
      (e 5) (List.replicate (values 5) tick)) (e 6) (List.replicate (values 6) tick)

theorem compactSetupUpdate7_map {I J : Type} [DecidableEq I] [DecidableEq J]
    (G : (I → List (Fin (A+4))) → J → List (Fin (A+4))) (e : I → J)
    (hG : ∀ R x l,G (Function.update R x l)=Function.update (G R) (e x) l)
    (R : I → List (Fin (A+4))) (src : Fin 7 → I) (values : Fin 7 → ℕ) :
    G (compactSetupUpdate7 R src values)=compactSetupUpdate7 (G R) (e ∘ src) values := by
  simp only [compactSetupUpdate7,hG,Function.comp_apply]

def compactBasisSetupValues (d g K D o r : ℕ) : Fin 7 → ℕ :=
  let q := CompactGlobalRowPadding.rowAxes Layer.NW m d
  ![o,K*backChunks d g K,D-q-frontChunks d g K-backChunks d g K,K*(D-q),r,d,g]

def compactBasisPersistent (i : Fin 7) : Fin (nT CompactHostBReg) :=
  reg (.bc (.inl (.work (compactBasisOutputWork i))))

private theorem embOvr_right_update {T T' : ℕ} {e : Fin T → Fin T'}
    (he : Function.Injective e) (S : Stacks T' A) (R : Fin T → List (Fin (A+4)))
    (x : Fin T) (l : List (Fin (A+4))) :
    embOvr e ({embStk e S with R:=Function.update R x l}.get) S =
      {embOvr e ({embStk e S with R:=R}.get) S with
        R:=Function.update (embOvr e ({embStk e S with R:=R}.get) S).R (e x) l} :=
  embOvr_updR he {embStk e S with R:=R} S x l

private theorem compactSetupUpdate7_emb {T T' : ℕ} {e : Fin T → Fin T'}
    (he : Function.Injective e) (S : Stacks T' A) (src : Fin 7 → Fin T) (values : Fin 7 → ℕ) :
    embOvr e ({embStk e S with R:=compactSetupUpdate7 (embStk e S).R src values}.get) S =
      {S with R:=compactSetupUpdate7 S.R (e ∘ src) values} := by
  have hbase : embOvr e ({embStk e S with R:=(embStk e S).R}.get) S=S := embOvr_stk S
  simp only [compactSetupUpdate7,embOvr_right_update he,hbase,Function.comp_apply]

/-- Generic execution transport for seven outputs, before specializing the large finite banks. -/
theorem compactSetup7_exec {T T' : ℕ} (e : Fin T → Fin T') (he : Function.Injective e)
    (body : P → Pr P T' Q A U) {p : Pr Empty T Q A U}
    {R : Fin T → List (Fin (A+4))} {src : Fin 7 → Fin T} {values : Fin 7 → ℕ} {c : ℕ}
    (h : LayRuns (fun f : Empty => f.elim) p R (compactSetupUpdate7 R src values) c)
    (v : HS T' Q A U) (S : Stacks T' A) (hL : ∀ i,S.L (e i)=[]) (hR : S.R ∘ e=R) :
    ∃ v' steps,v'.user=v.user ∧ steps≤c ∧
      Exec body (embProg e (fun f : Empty => f.elim) p) (mk v S) steps
        (mk v' {S with R:=compactSetupUpdate7 S.R (e ∘ src) values}) := by
  obtain ⟨v',steps,hu,hc,he'⟩ := compactEmptySetup_exec e he body h v S hL hR
  have hfile : R=(embStk e S).R := hR.symm
  rw [hfile] at he'
  rw [compactSetupUpdate7_emb he] at he'
  exact ⟨v',steps,hu,hc,he'⟩

end
end IntegerMultBounds.MathlibTM2.LayerMachine
