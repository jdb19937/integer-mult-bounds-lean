module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainCoefficients

/-! Carry the verified coefficient stream directly onto the expanded host output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.TableVM Filter
open Computability
noncomputable section

def compactMainOutR (r : OReg) : Fin compactMnT := compactMnRg (.out r)

def compactMainOutput : CompactMnPr CompactMainProc (prime+mnKa) := carryOut compactMainOutR

/-- The chain's output and preserved distribution fields suffice for the final carry stage. -/
theorem compactMainOutput_exec_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ (body : CompactMainProc → CompactMnPr CompactMainProc (prime+mnKa)) (x y : ℕ),
    Nat.size x≤n → Nat.size y≤n →
    ∀ (B : Stacks compactMnT (prime+mnKa)),
    MnDistOut (embStk compactMnLegacyReg B).R n (dsW n) (compactRetunedDist.E n)
      (mnσ (blP₀ dsW n) (compactDsyV₀ n)) →
    MnMid (embStk compactMnLegacyReg B) x y n →
    ∀ (v : HS compactMnT compactMnQ (prime+mnKa) Unit) (St : Stacks compactMnT (prime+mnKa)),
    St.R (compactMnRg (.out .dat))=mnWords mnKa n x y →
    (∀ r,r≠.dat → St.R (compactMnRg (.out r))=B.R (compactMnRg (.out r))) →
    ∃ (v' : HS compactMnT compactMnQ (prime+mnKa) Unit) (St' : Stacks compactMnT (prime+mnKa)),
      Exec body compactMainOutput (mk v St) (carryOutCost (mnWo n) (b n) (S n)) (mk v' St') ∧
      St'.inp=St.inp ∧ St'.out=encodingNatBool.encode (x*y)++St.out ∧ St'.L=St.L := by
  filter_upwards [compactMainCoeffs_eventually] with n hcoeff
  intro body x y hsx hsy B hdo hmid v St hdat hfr
  obtain ⟨hb,hW,hcs⟩ := hcoeff
  obtain ⟨hcsb,hev⟩ := hcs x y hsx hsy
  have hobr : St.R (compactMainOutR .br)=List.replicate (b n) tick := by
    rw [compactMainOutR,hfr .br (by simp)]
    have h := hmid.obr
    simpa only [embStk_R,mnOutR,compactMnLegacyReg_rg,mn_pmVals_b] using h
  have hoe : ∀ r : OReg,r≠.dat → mnDistKeep (.out r) → MnR.out r∉mnUsRegs →
      St.R (compactMainOutR r)=[] := by
    intro r hr hk hu
    rw [compactMainOutR,hfr r hr]
    have h := hmid.rest (.out r) hk hu
    simpa only [embStk_R,compactMnLegacyReg_rg] using h
  have hwr : (St.R (compactMainOutR .wr)).length=mnWo n := by
    rw [compactMainOutR,hfr .wr (by simp)]
    simpa only [embStk_R,mnOutR,compactMnLegacyReg_rg] using hdo.owr
  obtain ⟨v',hu,he⟩ := carryOut_exec (body := body) (oreg := compactMainOutR)
    (fun _ _ h => MnR.out.inj (compactMnRg_injective h)) hb hW hcsb
    (lw := St.R (compactMainOutR .wr)) (lb := St.R (compactMainOutR .br))
    hwr (by rw [hobr,List.length_replicate]) v St
    (by rw [compactMainOutR,hdat,compactMainCoeffs_words]) rfl rfl
    (hoe .ct (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (hoe .cr (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (hoe .sm (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (hoe .acc (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
  rw [compactMainCoeffs_length] at he
  exact ⟨v',_,he,rfl,by rw [hev],rfl⟩

end
end IntegerMultBounds.MathlibTM2.Fast.Main
