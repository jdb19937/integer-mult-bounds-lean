module

import IntegerMultBounds.MathlibTM2.Fast.CompactMainPrimitiveRuns
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainEntryTable
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Primitive contracts remain valid after installing the expanded main entry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

/-- A source-register contract with layer-only calls survives the main-table replacement. -/
theorem compactMainEntry_srcRuns (main : CompactMnPr CompactMainProc (prime+mnKa))
    (old : MnPr (prime+mnKa))
    {Pre : Stacks compactMnT (prime+mnKa) → Prop}
    {p : CompactMnPr CompactMainProc (prime+mnKa)}
    {ρ ρ' : MnR → List (Fin (prime+mnKa+4))} {c : ℕ}
    (h : SrcRuns (compactMainBody (mnBody mnLb old) Cost.brDirs) compactMnRg
      (compactMnLegacyReg ∘ mnι) Pre p ρ ρ' c)
    (hp : callsWithin (fun g => g≠compactMainOldProc .main) p) :
    SrcRuns (compactMainEntryTable main) compactMnRg
      (compactMnLegacyReg ∘ mnι) Pre p ρ ρ' c := by
  intro v S hc hpre hS
  obtain ⟨w,S',n,hu,hn,hex,hρ,hfr⟩ := h v S hc hpre hS
  exact ⟨w,S',n,hu,hn,compactMainEntry_exec main old hex hp,hρ,hfr⟩

lemma compactMainStage_calls {A : ℕ} (p : MnPr A)
    (hp : callsWithin (fun f : MnProc => f≠.main) p) :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactMainStage p) := by
  rw [compactMainStage,statePlacedNormalized,callsWithin_embProg_iff]
  refine ⟨True.intro,?_⟩
  rw [callsWithin_stateLiftPr_iff]
  simpa only [Function.comp_def,compactMainOldProc,ne_eq,Sum.inl.injEq,id_eq] using hp

/-- Direct adapter from an old primitive contract to the installed main table. -/
theorem compactMainEntry_primitive (main : CompactMnPr CompactMainProc (prime+mnKa))
    (old : MnPr (prime+mnKa))
    {Pre : Stacks mnT (prime+mnKa) → Prop} {Pre' : Stacks compactMnT (prime+mnKa) → Prop}
    (hpre : ∀ S,Pre' S → Pre (embStk compactMnLegacyReg S))
    {p : MnPr (prime+mnKa)} {ρ ρ' : MnR → List (Fin (prime+mnKa+4))} {c : ℕ}
    (h : SrcRuns (mnBody mnLb old) mnRg mnι Pre p ρ ρ' c)
    (hp : callsWithin (fun f : MnProc => f≠.main) p) :
    SrcRuns (compactMainEntryTable main) compactMnRg (compactMnLegacyReg ∘ mnι) Pre'
      (compactMainStage p) ρ ρ' (1+c) :=
  compactMainEntry_srcRuns main old (compactMainBody_srcRuns _ _ hpre h)
    (compactMainStage_calls p hp)

lemma compactMainDigits_calls {A : ℕ} (src : MnIO) :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactMainStage (mnDigits (A := A) src)) :=
  compactMainStage_calls _ (by trivial)

lemma compactMainMv_calls {A : ℕ} (a b : MnR) :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactMainStage (mnMv (A := A) a b)) :=
  compactMainStage_calls _ (by trivial)

private lemma seqList_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (ps : List (Pr P T Q A U)) (h : ∀ p ∈ ps,callsWithin allowed p) :
    callsWithin allowed (Prog.seqList ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨h p (by simp),ih (fun q hq => h q (by simp [hq]))⟩

private lemma placedRun_calls {s T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (M : Machine.Program s Q A) (ι : Fin s → Fin T) (hι : Function.Injective ι) (hT : s≤T) :
    callsWithin allowed (placedRun (F := P) (U := U) M ι hι hT) := by
  unfold placedRun
  refine ⟨?_,?_,?_,?_⟩
  · apply seqList_calls
    simp only [List.mem_map]
    rintro p ⟨i,hi,rfl⟩
    trivial
  · unfold foreign simIter
    refine ⟨True.intro,True.intro,?_,True.intro⟩
    apply seqList_calls
    intro p hp
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hp
    rcases hp with ⟨i,hi,rfl⟩ | rfl <;> trivial
  · apply seqList_calls
    simp only [List.mem_map]
    rintro p ⟨i,hi,rfl⟩
    trivial
  · apply seqList_calls
    simp only [List.mem_map]
    rintro p ⟨i,hi,rfl⟩
    trivial

private lemma ssMul_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (ι : Fin 64 → Fin T) (hι : Function.Injective ι) (hT : 64≤T) (hQ : SS.states≤Q)
    (a b n c : Fin T) : callsWithin allowed (ssMul (F := P) (U := U) (A := A) ι hι hT hQ a b n c) := by
  unfold ssMul
  exact ⟨by trivial,placedRun_calls _ _ _ _ _,by trivial⟩

private lemma point_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (ι : Fin 64 → Fin T) (hι : Function.Injective ι) (hT : 64≤T) (hQ : SS.states≤Q)
    (cr : CR → Fin T) :
    callsWithin allowed (cmulStream cr (cmulOne (P := P) (U := U) (A := A) ι hι hT hQ cr)) := by
  simp only [cmulStream,cmulBlock,cwhileP,cmulOne,cmulProds,callsWithin,ssMul_calls]
  trivial

lemma compactMainPoint_calls {A : ℕ} :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactMainStage (mnPoint (A := A))) := by
  apply compactMainStage_calls
  unfold mnPoint
  exact point_calls _ _ _ _ _ _

private lemma round_calls {T Q A : ℕ} {P U : Type} (allowed : P → Prop)
    (rg : RndReg → Fin T) (ι : Fin 64 → Fin T) (hι : Function.Injective ι)
    (hT : 64≤T) (hQ : SS.states≤Q) :
    callsWithin allowed (roundStage (P := P) (U := U) (A := A) rg ι hι hT hQ) := by
  simp only [roundStage,rndWhile,rndCoeffProg,rndPhaseB,callsWithin,ssMul_calls]
  trivial

lemma compactMainRound_calls {A : ℕ} :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactMainStage (mnRound (A := A))) := by
  apply compactMainStage_calls
  unfold mnRound
  exact round_calls _ _ _ _ _ _

lemma compactMainClearCm_calls {A : ℕ} (c : CR) :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactMainStage (uclear (A := A) (mnCm c))) :=
  compactMainStage_calls _ (by trivial)

lemma compactMainReadLen_calls {A : ℕ} :
    callsWithin (fun g => g≠compactMainOldProc .main)
      (compactMainStage (.seq (mnRead (A := A)) mnLen)) :=
  compactMainStage_calls _ (by trivial)

lemma compactMainOut_calls {A : ℕ} :
    callsWithin (fun g => g≠compactMainOldProc .main) (compactMainStage (mnOut (A := A))) :=
  compactMainStage_calls _ (by trivial)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
