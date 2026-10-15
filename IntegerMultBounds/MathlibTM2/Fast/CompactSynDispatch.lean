module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynCompare
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainLayer

/-! Actual counter-driven dispatch between compact chunk rounds and legacy direct rounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {A Ka : ℕ}

def compactSynDispatchReg (x : SynW) : Fin compactMnT :=
  compactMnLegacyReg (mnLayE (sreg x))

lemma compactSynDispatchReg_injective : Function.Injective compactSynDispatchReg :=
  compactMnLegacyReg_injective.comp (mnLayE_inj.comp sreg_injective)

def compactSynDispatchWith (chunk direct : CompactMnPr CompactMainProc A) :
    CompactMnPr CompactMainProc A :=
  compactSynCompare (compactSynDispatchReg (.p .ℓ)) (compactSynDispatchReg (.p .h))
    (compactSynDispatchReg (.s 1)) (compactSynDispatchReg (.s 2)) true
    (compactSynCompare (compactSynDispatchReg (.p .b)) (compactSynDispatchReg (.p .h))
      (compactSynDispatchReg (.s 1)) (compactSynDispatchReg (.s 2)) false direct chunk) direct

def compactSynDispatchCost (ℓ K h : ℕ) : ℕ :=
  compactSynCompareCost ℓ h true+
    if h+1<ℓ then compactSynCompareCost (layB ℓ K) h false else 0

def compactMainDirect (ds : ComplexFramedExecution.Directions) :
    CompactMnPr CompactMainProc (prime+Ka) :=
  compactMainStage (embProg mnLayE MnProc.lay (synLayerStep ds))

def compactSynDispatch (ds : ComplexFramedExecution.Directions) :
    CompactMnPr CompactMainProc (prime+Ka) :=
  compactSynDispatchWith (compactMainChunk ds) (compactMainDirect ds)

/-- Both tests read the stored counters; they restore all scratch before entering
 either branch. Branch contracts are required only for the branch actually selected. -/
theorem compactSynDispatchWith_runs (body : CompactMainProc → CompactMnPr CompactMainProc A)
    {es : List ℕ} {ℓ K w l h : ℕ} {L : Equiv.Perm (Fin es.sum)}
    {v : SynW → List (Fin (A+4))} (hv : SynV v es ℓ K w l h L)
    {R R' : Fin compactMnT → List (Fin (A+4))}
    (hR : ∀ x,R (compactSynDispatchReg x)=v x)
    {chunk direct : CompactMnPr CompactMainProc A} {cc cd : ℕ}
    (hc : synChunk ℓ K h → LayRuns body chunk R R' cc)
    (hd : ¬synChunk ℓ K h → LayRuns body direct R R' cd) :
    LayRuns body (compactSynDispatchWith chunk direct) R R'
      (compactSynDispatchCost ℓ K h+(if synChunk ℓ K h then cc else cd)) := by
  have hne (x y : SynW) (hxy : x≠y) : compactSynDispatchReg x≠compactSynDispatchReg y :=
    compactSynDispatchReg_injective.ne hxy
  have hs : R (compactSynDispatchReg (.s 1))=[] := (hR _).trans (hv.hs 1)
  have ht : R (compactSynDispatchReg (.s 2))=[] := (hR _).trans (hv.hs 2)
  have hℓ : (R (compactSynDispatchReg (.p .ℓ))).length=ℓ := by rw [hR,hv.hℓ]
  have hh : (R (compactSynDispatchReg (.p .h))).length=h := by rw [hR,hv.hh]
  have hb : (R (compactSynDispatchReg (.p .b))).length=layB ℓ K := by rw [hR,hv.hb]
  unfold compactSynDispatchWith compactSynDispatchCost
  refine (compactSynCompare_runs body (hne _ _ (by decide)) (hne _ _ (by decide))
    (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) true hs ht
    (c := (if h+1<ℓ then compactSynCompareCost (layB ℓ K) h false else 0)+
      (if synChunk ℓ K h then cc else cd)) ?_ ?_).mono ?_
  · intro htop
    have htop' : h+1<ℓ := by rw [hℓ,hh] at htop; simp only [ite_true] at htop; omega
    have ei := compactSynCompare_runs body (hne (.p .b) (.s 1) (by decide))
      (hne _ _ (by decide)) (hne (.p .h) (.s 1) (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) false hs ht (p := direct) (q := chunk) (R' := R')
      (c := if synChunk ℓ K h then cc else cd)
    have ei' := ei (fun hn => by
        have hlow : h<layB ℓ K := by rw [hb,hh] at hn; simp only [Bool.false_eq_true,ite_false,Nat.sub_zero] at hn; omega
        have hnc : ¬synChunk ℓ K h := by intro hz; have := hz.2; omega
        simpa only [hnc,ite_false] using hd hnc)
      (fun hn => by
        have hchunk : synChunk ℓ K h := by
          constructor
          · exact htop'
          · rw [hb,hh] at hn; simp only [Bool.false_eq_true,ite_false,Nat.sub_zero] at hn; omega
        simpa only [hchunk,ite_true] using hc hchunk)
    simpa only [hℓ,hh,hb,htop',ite_true] using ei'
  · intro htop
    have htop' : ¬h+1<ℓ := by rw [hℓ,hh] at htop; simp only [ite_true] at htop; omega
    have hnc : ¬synChunk ℓ K h := fun hz => htop' hz.1
    simpa only [hℓ,hh,htop',ite_false,hnc,Nat.zero_add] using hd hnc
  · rw [hℓ,hh]
    omega

end
end IntegerMultBounds.MathlibTM2.Fast.Main
