module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainCleanup
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainParamCalls
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedDistributionEntry
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainDistributionCalls
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainStableFrame

/-! Actual input, parameters, and retuned distribution enter the expanded main chain. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Fast.TableVM Filter
noncomputable section

/-- Input preparation and distribution share one normalized legacy-host entry. -/
def compactMainInputDist
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ),MnPostParam R n → BdPostParam R n) :
    CompactMnPr CompactMainProc bdA :=
  compactMainStage (.seq (.seq (.seq mnRead mnLen) mnParams) (compactBdDist hP).distP)

/-- Input preparation executes from the true empty expanded machine; distribution
supplies the actual retuned wires, stage file, and stable chain precondition. -/
theorem compactMainInputDist_exec_eventually
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ),MnPostParam R n → BdPostParam R n) :
    ∀ᶠ N : ℕ in atTop, ∀ (main : CompactMnPr CompactMainProc bdA) (x y : ℕ),
      (pairEnc (x,y)).length=N →
      ∃ (v : HS compactMnT compactMnQ bdA Unit) (S : Stacks compactMnT bdA) (m : ℕ),
        m≤8*N+14+pmCost N mnUs+(compactBdDist hP).cost N+1 ∧
        Exec (compactMainEntryTable main) (compactMainInputDist hP)
          (Store.only compactMainV₀ .inp (pairEnc (x,y))) m (mk v S) ∧
        S.inp=[] ∧ S.out=[] ∧ compactMainStablePre N S ∧
        MnDistOut (embStk compactMnLegacyReg S).R N (dsW N) (bdE N)
          (mnσ (blP₀ dsW N) (compactDsyV₀ N)) ∧
        MnMid (embStk compactMnLegacyReg S) x y N := by
  filter_upwards [compactBdDist_entry_eventually hP,eventually_ge_atTop 2] with N hdist hN
  intro main x y hlen
  let old : MnPr bdA := .act .done
  obtain ⟨v₁,S₁,m₁,hm₁,he₁,hfront⟩ := mn_front_exec (body := mnBody mnLb old) (A := bdA) x y
  rw [hlen] at hm₁ hfront
  have hA : 4≤bdA := by
    exact (by omega : 4≤96).trans mnKa_alpha
  obtain ⟨v₂,S₂,m₂,hm₂,he₂,hin₂,hout₂,hL₂,hι₂,hpost,hmid₂⟩ :=
    mn_params_exec hN hA v₁ S₁ hfront
  obtain ⟨v₃,S₃,m₃,hm₃,he₃,hin₃,hout₃,hL₃,hfields,hmid₃,hentry⟩ :=
    hdist old x y v₂ S₂ hL₂ hι₂ hpost hmid₂
  have he := (he₁.seq he₂).seq he₃
  have hstart : mk mnV₀ (mnIn (A := bdA) (pairEnc (x,y)))=
      mk (compactMainStateDown compactMainV₀)
        (embStk compactMnLegacyReg (compactMainIn (pairEnc (x,y)))) := by
    rw [compactMainV₀_projection]
    rfl
  rw [hstart] at he
  obtain ⟨v,hv,hu,hex⟩ := compactMainStage_exec (mnBody mnLb old)
    (compactMainNativeTable Cost.brDirs) compactMainV₀ (compactMainIn (pairEnc (x,y))) he
  have hcall : callsWithin (fun g => g≠compactMainOldProc .main) (compactMainInputDist hP) := by
    unfold compactMainInputDist
    rw [compactMainStage,statePlacedNormalized,callsWithin_embProg_iff]
    refine ⟨True.intro,?_⟩
    rw [callsWithin_stateLiftPr_iff]
    have hd := compactMainDistribution_calls hP
    rw [compactMainStage,statePlacedNormalized,callsWithin_embProg_iff] at hd
    simp only [callsWithin] at hd
    rw [callsWithin_stateLiftPr_iff] at hd
    have hp := compactMainParams_calls (A := bdA)
    rw [compactMainStage,statePlacedNormalized,callsWithin_embProg_iff] at hp
    simp only [callsWithin] at hp
    rw [callsWithin_stateLiftPr_iff] at hp
    exact ⟨⟨by trivial,hp.2⟩,hd.2⟩
  have hex' := compactMainEntry_exec main old hex hcall
  rw [←compactMain_only_inp] at hex'
  refine ⟨v,compactMainFinalStacks S₃ (compactMainIn (pairEnc (x,y))),1+(m₁+m₂+m₃),
    by omega,hex',?_,?_,?_,?_,?_⟩
  · exact (compactMainFinalStacks_io _ _).1.trans (hin₃.trans hin₂)
  · exact (compactMainFinalStacks_io _ _).2.trans (hout₃.trans hout₂)
  · exact compactMainStablePre_of_mid (hentry _ (fun _ => rfl) (fun _ => rfl))
  · rw [compactMainFinalStacks_projection]
    exact hfields
  · rw [compactMainFinalStacks_projection]
    exact hmid₃

end
end IntegerMultBounds.MathlibTM2.Fast.Main
