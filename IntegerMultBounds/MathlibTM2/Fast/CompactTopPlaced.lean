module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopOriginal
public import IntegerMultBounds.MathlibTM2.Node.CompactRegisterEmbedding

/-! Original-input construction runs on the compact register bank through a
fixed embedding. Empty procedure names ensure no compatibility assumption on
the compact layer's procedure table is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Embedding a call-free constructor preserves its exact execution bound and
all unplaced tapes, regardless of the target procedure table. -/
theorem compactEmptySetup_exec {T T' : ℕ} (e : Fin T → Fin T')
    (he : Function.Injective e) (body : P → Pr P T' Q A U)
    {p : Pr Empty T Q A U} {R₀ R₁ : Fin T → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns (fun f : Empty => f.elim) p R₀ R₁ c)
    (v : HS T' Q A U) (S : Stacks T' A)
    (hL : ∀ i,S.L (e i)=[]) (hR : S.R ∘ e=R₀) :
    ∃ v' steps, v'.user=v.user ∧ steps≤c ∧
      Exec body (embProg e (fun f : Empty => f.elim) p)
        (mk v S) steps (mk v' (embOvr e
          ({embStk e S with R:=R₁}.get) S)) := by
  obtain ⟨v₁,steps,hu,hc,hrun⟩ := h (embDn e v) (embStk e S) hL hR
  obtain ⟨v',_,hu',he'⟩ := exec_emb_ovr he
    (body':=body) (ι:=fun f : Empty => f.elim) (by intro f; cases f) hrun v rfl S rfl
  exact ⟨v',steps,hu'.trans hu,hc,he'⟩

/-- The unchanged original-input program, now on the actual compact bank. -/
def compactTopPlaced (G F : ℕ) (rowsSrc : SynW) : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim)
    (compactTopOriginal (P:=Empty) G F rowsSrc)

/-- Concrete placed execution with the source file read along the fixed embedding. -/
def CompactPlacedRuns (body : P → Pr P (nT CompactHostBReg) Q A U)
    (p : Pr P (nT CompactHostBReg) Q A U)
    (R₀ R₁ : Fin (nT SXReg) → List (Fin (A+4))) (c : ℕ) : Prop :=
  ∀ (v : HS (nT CompactHostBReg) Q A U) (S : Stacks (nT CompactHostBReg) A),
    (∀ i,S.L (compactLegacyReg i)=[]) → S.R ∘ compactLegacyReg=R₀ →
    ∃ v' steps, v'.user=v.user ∧ steps≤c ∧
      Exec body p (mk v S) steps (mk v' (embOvr compactLegacyReg
        ({embStk compactLegacyReg S with R:=R₁}.get) S))

theorem compactTopPlaced_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (rowsSrc : SynW) (hsrc : ∀ i, rowsSrc≠.s i)
    (hsrcpr : rowsSrc≠.p .pr) (_hsrccf : rowsSrc≠.p .cf) (_hsrcw2 : rowsSrc≠.p .w2)
    (G F N d g K D o W Rv : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) (ho : (v (.s 7)).length=o)
    (hW : (v (.p .w)).length=W) (hRows : (v rowsSrc).length=Rv)
    (hpr : v (.p .pr)=[]) (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    let E := b+synE G F active active
    let a := N-(o+K*(D-q))
    let shift := (D+1)/2+(q+f)+E
    let record := topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active))
    CompactPlacedRuns body (compactTopPlaced G F rowsSrc) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.p .pr) record) (.p .cf)
        (topRec (topCfg W shift a Rv (compactTopRows d Rv a) (q+f)
          (o+K*(b+active)) K o D)).reverse)
        (.p .w2) (List.replicate (W+shift+D) tick)))
      (compactTopOriginalCost G F N d g K D o W Rv) := by
  dsimp only
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (sg_compactTopOriginal (fun f : Empty => f.elim) R v rowsSrc hsrc hsrcpr _hsrccf _hsrcw2
      G F N d g K D o W Rv hdpos hk hN hd hg hK hD ho hW hRows hpr hcf hw2 hs)
    vbig S hL hR

end
end IntegerMultBounds.MathlibTM2.Fast
