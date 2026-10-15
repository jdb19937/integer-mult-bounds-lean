module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapView
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineExit

/-! Bootstrap and exit preserve the transform's legacy registers exactly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

lemma compactMnBootstrapDst_work4 : compactMnBootstrapDst 4=compactMnLay (.bc (.inl (.work 4))) := by
  rw [compactMnBootstrapDst_eq]
  change compactMnLayerReg (compactBasisSetupReg (sreg (compactBasisOutputWire 1)))=_
  rw [compactBasisSetupReg_output,compactMnLayerReg_private]
  rfl

lemma compactMnBootstrapDst_work3 : compactMnBootstrapDst 5=compactMnLay (.bc (.inl (.work 3))) := by
  rw [compactMnBootstrapDst_eq]
  change compactMnLayerReg (compactBasisSetupReg (sreg (compactBasisOutputWire 0)))=_
  rw [compactBasisSetupReg_output,compactMnLayerReg_private]
  rfl

lemma compactMnBootstrapDst_work5 : compactMnBootstrapDst 6=compactMnLay (.bc (.inl (.work 5))) := by
  rw [compactMnBootstrapDst_eq]
  change compactMnLayerReg (compactBasisSetupReg (sreg (compactBasisOutputWire 2)))=_
  rw [compactBasisSetupReg_output,compactMnLayerReg_private]
  rfl

lemma compactMnBootstrapDestinations_blank (R : Fin compactMnT → List (Fin (A+4)))
    (hs : ∀ i : Fin 32,R (compactMnSyn (.s i))=[])
    (hb : ∀ z : CompactBReg,R (compactMnLay (.bc (.inl z)))=[]) :
    ∀ i,R (compactMnBootstrapDst i)=[] := by
  intro i
  fin_cases i
  · change R (compactMnBootstrapDst 0)=[]
    rw [compactMnBootstrapDst_guard]; exact hb _
  · change R (compactMnBootstrapDst 1)=[]
    rw [compactMnBootstrapDst_depth]; exact hb _
  · change R (compactMnBootstrapDst 2)=[]
    rw [compactMnBootstrapDst_p]; exact hs 0
  · change R (compactMnBootstrapDst 3)=[]
    rw [compactMnBootstrapDst_d]; exact hs 1
  · change R (compactMnBootstrapDst 4)=[]
    rw [compactMnBootstrapDst_work4]; exact hb _
  · change R (compactMnBootstrapDst 5)=[]
    rw [compactMnBootstrapDst_work3]; exact hb _
  · change R (compactMnBootstrapDst 6)=[]
    rw [compactMnBootstrapDst_work5]; exact hb _

private lemma bootstrapOnlyGlobals {T : ℕ} (R : Fin T → List (Fin (A+4)))
    (e : Fin 7 → Fin T) (he : Function.Injective e) (g d : ℕ)
    (hz : ∀ i,R (e i)=[]) :
    compactSetupUpdate7 R e ![g,d,0,0,0,0,0]=
      Function.update (Function.update R (e 0) (List.replicate g tick))
        (e 1) (List.replicate d tick) := by
  funext z
  by_cases h2 : z=e 2
  · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
  by_cases h3 : z=e 3
  · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
  by_cases h4 : z=e 4
  · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
  by_cases h5 : z=e 5
  · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
  by_cases h6 : z=e 6
  · subst z; simp [compactSetupUpdate7,he.eq_iff,hz]
  simp [compactSetupUpdate7,Function.update_of_ne,h2,h3,h4,h5,h6]

lemma compactMnBootstrapFinal_globalsOnly (R : Fin compactMnT → List (Fin (A+4)))
    (p d : ℕ) (hs : ∀ i : Fin 32,R (compactMnSyn (.s i))=[])
    (hb : ∀ z : CompactBReg,R (compactMnLay (.bc (.inl z)))=[]) :
    compactMnBootstrapFinal R p d=
      Function.update (Function.update R (compactMnLay (.bc (.inl (.work 14))))
        (List.replicate (4*Nat.clog 2 p+6) tick))
        (compactMnLay (.bc (.inl (.work 13)))) (List.replicate d tick) := by
  rw [compactMnBootstrapFinal_base]
  have h := bootstrapOnlyGlobals R compactMnBootstrapDst compactMnBootstrapDst_injective
    (4*Nat.clog 2 p+6) d (compactMnBootstrapDestinations_blank R hs hb)
  simpa only [compactGlobalBootstrapValues,compactMnBootstrapDst_guard,
    compactMnBootstrapDst_depth] using h

lemma compactMnBootstrapFinal_view (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ)
    (hs : ∀ i : Fin 32,R (compactMnSyn (.s i))=[])
    (hb : ∀ z : CompactBReg,R (compactMnLay (.bc (.inl z)))=[]) :
    compactSynView (compactMnBootstrapFinal R p d)=compactSynView R := by
  rw [compactMnBootstrapFinal_globalsOnly R p d hs hb]
  funext i
  simp only [compactSynView,Function.comp_apply,
    Function.update_of_ne (compactMnLegacyReg_ne_private (mnLayE i) (.work 13)),
    Function.update_of_ne (compactMnLegacyReg_ne_private (mnLayE i) (.work 14))]

lemma compactMnBootstrapFinal_ready (M : ℕ) (hM : 2≤M)
    (R : Fin compactMnT → List (Fin (A+4)))
    (hs : ∀ i : Fin 32,R (compactMnSyn (.s i))=[])
    (hb : ∀ z : CompactBReg,R (compactMnLay (.bc (.inl z)))=[]) :
    CompactSynReady (compactMnBootstrapFinal R (Mult.Sizes.p M) (Mult.Sizes.d M)) M := by
  apply compactSynReady_of_globals M hM _ (compactMnBootstrap_globals R _ _)
  intro z h13 h14
  rw [compactMnBootstrapFinal_globalsOnly R _ _ hs hb]
  have hne (i : Fin 30) (hi : z≠.work i) :
      compactMnLay (.bc (.inl z))≠compactMnLay (.bc (.inl (.work i))) := by
    intro he
    exact hi (Sum.inl_injective (LReg.bc.inj (compactMnLay_injective he)))
  rw [Function.update_of_ne (hne 13 h13),Function.update_of_ne (hne 14 h14),hb]

private lemma clearGlobalsAfterOutput {T : ℕ} (R : Fin T → List (Fin (A+4)))
    (x y io : Fin T) (hxy : x≠y) (hxi : x≠io) (hyi : y≠io)
    (gx gy out : List (Fin (A+4))) (hx : R x=[]) (hy : R y=[]) :
    Function.update (Function.update
      (Function.update (Function.update (Function.update R x gx) y gy) io out) y []) x []=
      Function.update R io out := by
  funext z
  by_cases hz : z=x
  · subst z; simp [hxi,hx]
  by_cases hz' : z=y
  · subst z; simp [hxy.symm,hyi,hy]
  simp only [Function.update_of_ne hz,Function.update_of_ne hz']
  by_cases hi : z=io
  · subst z; simp
  · simp [Function.update_of_ne hi,Function.update_of_ne hz,Function.update_of_ne hz']

/-- Exit restores the original complete file except for the transform's output stream. -/
theorem compactMnGlobalsExit_after_transform (body : P → Pr P compactMnT Q A U)
    (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) (out : List (Fin (A+4)))
    (hs : ∀ i : Fin 32,R (compactMnSyn (.s i))=[])
    (hb : ∀ z : CompactBReg,R (compactMnLay (.bc (.inl z)))=[]) :
    LayRuns body compactMnGlobalsExit
      (Function.update (compactMnBootstrapFinal R p d) (compactMnRg (.src (.v .io))) out)
      (Function.update R (compactMnRg (.src (.v .io))) out)
      ((2*d+2)+(2*(4*Nat.clog 2 p+6)+2)) := by
  have hg := compactMainGlobals_io_update (compactMnBootstrapFinal R p d) p d out
    (compactMnBootstrap_globals R p d)
  have h := compactMnGlobalsExit_runs body _ p d hg
  rw [compactMnBootstrapFinal_globalsOnly R p d hs hb] at h
  have hxy : compactMnLay (.bc (.inl (.work 14)))≠compactMnLay (.bc (.inl (.work 13))) := by
    intro he
    have he' := compactMnLay_injective he
    cases he'
  rw [clearGlobalsAfterOutput R _ _ _ hxy (compactMnRg_ne_lay _ _).symm
    (compactMnRg_ne_lay _ _).symm _ _ out (hb _) (hb _)] at h
  simpa only [compactMnBootstrapFinal_globalsOnly R p d hs hb] using h

end
end IntegerMultBounds.MathlibTM2.Fast.Main
