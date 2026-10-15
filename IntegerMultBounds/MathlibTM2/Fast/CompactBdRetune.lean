module

public import IntegerMultBounds.MathlibTM2.Fast.CompactDistWiresExec

/-! Retune actual source-converter parking before constructing compact wires. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
noncomputable section

def compactBdRetuneFile (n : ℕ) (R : Regs mnT bdA) : Regs mnT bdA :=
  dsOv mnPm (Function.update R (bdIo .lK) (List.replicate (CompactSizes.K n) tick))
    (tblRho (pmW n) (bdWl n) (bdWl n) ⟨compactPmVals n,[]⟩)

lemma compactBdRetuneFile_off (n : ℕ) (R : Regs mnT bdA) (x : Fin mnT)
    (hp : ∀ q,mnPm q≠x) (hk : x≠bdIo .lK) : compactBdRetuneFile n R x=R x := by
  rw [compactBdRetuneFile,dsOv_off _ _ hp,Function.update_of_ne hk]

lemma compactBdRetuneFile_pre (n : ℕ) (R : Regs mnT bdA) (h : BdPre R n) :
    CompactBdWiresPre (compactBdRetuneFile n R) n := by
  constructor
  · intro x
    have hpm : ∀ q,mnPm q≠bdIo x := fun q => mnRg_ne_lay _ _
    rw [compactBdRetuneFile,dsOv_off _ _ hpm]
    by_cases hx : x=.lK
    · subst x; simp [compactBdO]
    · rw [Function.update_of_ne (bdIo_inj.ne hx),h.io]
      cases x <;> first | rfl | exact absurd rfl hx
  · intro x hx
    rw [compactBdRetuneFile_off n R _ (fun q => mnRg_ne_lay _ _)
      (fun he => hx .lK (mnLay_inj he).symm)]
    exact h.lay x hx

lemma compactBdRetune_runs (n : ℕ) (hn : 2≤n) (mainP : MnPr bdA)
    (R : Regs mnT bdA) (h : BdPre R n) :
    dsRuns (mnBody mnLb mainP) (compactDsRetune mnPm (bdIo .lK)) R
      (compactBdRetuneFile n R) (compactDsRetuneCost n (pmW n) (K n)) := by
  have hr := compactDsRetune_runs (mnBody mnLb mainP) mnPm bdPm_inj (bdIo .lK)
    (fun q => mnRg_ne_lay _ _) n (pmW n) (pmW_ge n) (bdWl n) (bdWl_length n) R (ds_pmVals_lt hn)
  have hin : R=dsOv mnPm R (bdρ n) := dsOv_eq_of bdPm_inj h.pm (fun _ _ => rfl)
  rw [←hin,h.io] at hr
  simpa only [compactBdRetuneFile,bdO,dsSrcO,List.length_replicate] using hr

/-- Complete wire stage from the existing main distribution precondition. -/
def compactBdWiresProg : MnPr bdA := .seq (compactDsRetune mnPm (bdIo .lK)) dsyProg

def compactBdWiresCost (n : ℕ) : ℕ := compactDsRetuneCost n (pmW n) (K n)+compactDsyWiresCost n

theorem compactBdWires_spec : ∀ᶠ n in atTop, ∀ mainP : MnPr bdA,
    ∀ (v : HS mnT mnQ bdA Unit) (S : Stacks mnT bdA),
    (∀ y,S.L y=[]) → (∀ j,S.R (mnι j)=[]) → BdPre S.R n →
    ∃ (v' : HS mnT mnQ bdA Unit) (S' : Stacks mnT bdA) (m : ℕ), m≤compactBdWiresCost n ∧
      Exec (mnBody mnLb mainP) compactBdWiresProg (mk v S) m (mk v' S') ∧
      S'.inp=S.inp ∧ S'.out=S.out ∧ S'.L=S.L ∧ (∀ j,S'.R (mnι j)=[]) ∧
      (∀ x,S'.R (mnLay x)=mnσ (blP₀ dsW n) (compactDsyV₀ n) x) ∧
      ∀ r,bdWKeep r → S'.R (mnRg r)=S.R (mnRg r) := by
  filter_upwards [eventually_ge_atTop 2,compactDsyWires_spec] with n hn hwire
  intro mainP v S hL hι hpre
  obtain ⟨v₁,m₁,hu₁,hc₁,he₁⟩ := compactBdRetune_runs n hn mainP S.R hpre v S rfl
  have hi : ∀ j,compactBdRetuneFile n S.R (mnι j)=[] := by
    intro j
    rw [compactBdRetuneFile_off n S.R _ (fun q => mnRg_ne_ι _ _)
      (fun he => mnι_ne_lay j _ he),hι]
  obtain ⟨v₂,S₂,m₂,hc₂,he₂,hin,hout,hleft,hscratch,hlay,hkeep⟩ :=
    hwire mainP v₁ {S with R:=compactBdRetuneFile n S.R} hL hi (compactBdRetuneFile_pre n S.R hpre)
  refine ⟨v₂,S₂,m₁+m₂,by unfold compactBdWiresCost; omega,Exec.seq he₁ he₂,
    hin,hout,hleft,hscratch,hlay,?_⟩
  intro r hr
  exact (hkeep r hr).trans (compactBdRetuneFile_off n S.R _
    (fun q he => hr.1 q (mnRg_inj he).symm) (mnRg_ne_lay _ _))

end
end IntegerMultBounds.MathlibTM2.Fast.Main
