module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepExecution
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepSemantics
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStep
public import IntegerMultBounds.MathlibTM2.Fast.CompactPieceGeometry
public import IntegerMultBounds.Machine.CompactReservationGrowth
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecution
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! A whole actual chunk round, from existing synthetic state and initialized
original globals, through the real compact top, back to the original register file. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Rounds
open CompactGadgetReservationCapacity
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q Ka : ℕ} {U : Type}
open Filter

theorem compactSynLayerStep_eventually_exec_stream (hQ : compactRuntimeStates≤Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
      (hgate : ∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
      (es : List ℕ) (ℓ W l h p : ℕ),
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let K := Mult.Sizes.K M
    let D := es.length
    let o := K*((h-layB ℓ K)/K*D)
    let ρ := (h-layB ℓ K)%K
    let r := 2^l
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let a := es.sum-n
    ∀ (_hdpos : 0<d) (hKpos : 1≤K) (_hchunk : synChunk ℓ K h) (_H : LayHyp es ℓ K)
      (hcap : CompactReservationFits d g K D) (hD : D≤d)
      (_haddr : o+K*D≤es.sum)
      (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a)
      (_hprecision : es.sum+1≤Mult.Sizes.p M)
      (_hrun : Mult.Sizes.r M≤r) (_hwrun : Mult.Sizes.p M≤W) (_hW : p+2≤W),
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let R₂ := compactTopRows d 1 a
    let s := (D+1)/2+q+(backChunks d g K+
      synE (gateCount (program ds)) (factorCount (program ds))
        (compactReservationActive d g K D) (compactReservationActive d g K D))
    let working := W+s+D
    let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfg W s a 1 R₂ q aT K o D
    let pfs := topPcRec K pcs
    let hρ : ρ<K := Nat.mod_lt _ (by omega)
    let _hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
    let _low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    ∀ (v : SynW → List (Fin (prime+Ka+4))) (L : Equiv.Perm (Fin es.sum))
      (_hv : SynV v es ℓ K W l h L) (P₀ : List (Fin (prime+Ka+4)))
      (Y : ℕ → Fin r → GaussianInt)
      (_hY : ∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p)
      (R : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
      (_hlegacy : R ∘ compactLegacyReg=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        R (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
      (_hdepth : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
      (_hguard : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g),
    LayRuns (compactPlacedLayerTable (Ka := Ka) (U := U) hQ ds) (compactSynLayerStep ds) R
      (Function.update R (reg (BReg := CompactHostBReg) .io) (cstream (prime+Ka) W (rpStream (2^es.sum) (synTrunc
        (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
          (fun x c => GaussianInt.toComplex (Y x c)))))))
      (compactSynLayerRoundOverhead (gateCount (program ds)) (factorCount (program ds))
        es.sum d g K D o W r h (layB ℓ K) ρ working
        (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length
        (synStashCostW v synXS)+
        compactTopCost W working s n a 1 r K ρ q aT o D R₂ pcs
          (compactTopCallCost ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
          (compactTopCallCost ds shape 1 n o r working ρ)) := by
  filter_upwards [compactSynLayerStep_eventually_exec_Hl (Q := Q) (Ka := Ka) (U := U) hQ hA hA9 hNW] with M hexec
  intro ds hd hgate es ℓ W l h p
  dsimp only
  intro hdpos hKpos hchunk H hcap hD haddr ha hprecision hrun hwrun hW v L hv P₀ Y hY R hlegacy hblank hdepth hguard
  have hn : Mult.Sizes.K M*((h-layB ℓ (Mult.Sizes.K M))/Mult.Sizes.K M*es.length)+
      Mult.Sizes.K M*(es.length-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M))≤es.sum := by
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _).trans haddr
  have hna := Nat.add_sub_of_le hn
  let n := Mult.Sizes.K M*((h-layB ℓ (Mult.Sizes.K M))/Mult.Sizes.K M*es.length)+
      Mult.Sizes.K M*(es.length-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M))
  have hinput : R ∘ compactLegacyReg=synG (synIdle
      (encZ (prime+Ka) W (synZ (n+(es.sum-n)) Y)) P₀) v := by
    rw [encZ_synZ,hna]
    exact hlegacy
  have he := hexec ds hd hgate es ℓ W l h p hdpos hKpos hchunk hcap hD haddr ha
    hprecision hrun hwrun hW v L hv P₀ (synZ _ Y) (fun z => hY _ _) R
    hinput hblank hdepth hguard
  let o := Mult.Sizes.K M*((h-layB ℓ (Mult.Sizes.K M))/Mult.Sizes.K M*es.length)
  have hvals := compactTopSelection_vals ds (oS := o) (n := n) (a := es.sum-n) hcap
    (Nat.mod_lt (h-layB ℓ (Mult.Sizes.K M)) (by omega))
    (compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W))
    (compactTopKernel_geometry (o := o) hcap
      (Nat.mod_lt (h-layB ℓ (Mult.Sizes.K M)) (by omega)) ha).1
  have hout := compactSynSelection_stream (A := prime+Ka) (W := W) H hchunk (by omega) _ Y hvals
  have hna' : n+(es.sum-n)=es.sum := hna
  have hstream : cstream (prime+Ka) W (rpStream (2^(n+(es.sum-n))) (synTrunc
      (bflyL ((selBits es h).map (twPosL (layPerm es ℓ (Mult.Sizes.K M))))
        (fun x c => GaussianInt.toComplex (Y x c))))) =
      cstream (prime+Ka) W (rpStream (2^es.sum) (synTrunc
      (bflyL ((selBits es h).map (twPosL (layPerm es ℓ (Mult.Sizes.K M))))
        (fun x c => GaussianInt.toComplex (Y x c))))) := by rw [hna']
  rw [hout.trans hstream] at he
  exact he

end
end IntegerMultBounds.MathlibTM2.Fast
