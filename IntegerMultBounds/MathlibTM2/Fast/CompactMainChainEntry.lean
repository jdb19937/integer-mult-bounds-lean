module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainChainExec
public import IntegerMultBounds.MathlibTM2.Fast.CompactRetunedMainBound

/-! The complete arithmetic chain starts directly from the actual distribution output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM
open Filter
noncomputable section

theorem compactRetunedChain_entry_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ (main : CompactMnPr CompactMainProc (prime+mnKa)) (x y : ℕ)
    (_hsx : Nat.size x ≤ n) (_hsy : Nat.size y ≤ n)
    (v : HS compactMnT compactMnQ (prime+mnKa) Unit) (St : Stacks compactMnT (prime+mnKa)),
    compactMainStablePre n St →
    MnDistOut (embStk compactMnLegacyReg St).R n (dsW n) (compactRetunedDist.E n)
      (mnσ (blP₀ dsW n) (compactDsyV₀ n)) →
    MnMid (embStk compactMnLegacyReg St) x y n →
    ∃ (v' : HS compactMnT compactMnQ (prime+mnKa) Unit)
      (St' : Stacks compactMnT (prime+mnKa)) (m : ℕ),
      m ≤ mnChainCost n (dsW n)
        (compactMainRuns compactRetunedDist compactRetunedCF compactRetunedCO n) + 12 ∧
      Exec (compactMainEntryTable main) compactMainChain (mk v St) m (mk v' St') ∧
      St'.inp=St.inp ∧ St'.out=St.out ∧ St'.L=St.L ∧
      St'.R (compactMnRg (.out .dat))=mnWords mnKa n x y ∧
      ∀ r,r≠.dat → St'.R (compactMnRg (.out r))=St.R (compactMnRg (.out r)) := by
  filter_upwards [compactMainChain_exec_eventually, eventually_big, eventually_small,
    eventually_margins, compactRetunedDist.base, compactRetunedDist.crt,
    compactRetunedDist.ln, compactRetunedDist.str, compactRetunedDist.sb,
    compactRetunedDist.widths] with n hchain hbig hsmall hmarg hbase hcrt hln hstr hsb hwid
  intro main x y hsx hsy v St hstable hout hmid
  obtain ⟨hEs,-⟩ := hmarg
  obtain ⟨hw,hwW,hWA,hWB,hWs,hWk⟩ := hwid
  have h := hchain main mnKa_alpha hbig hsmall hEs hw hwW hWA hWB hWs hWk
    (compactRetunedDist.E n) (hbase (srcHd0 hbig)) hcrt hln hstr hsb x y hsx hsy v St hstable
    (fun r => by simpa only [embStk_R, compactMnLegacyReg_rg] using hout.src r) hmid
    (by simpa only [embStk_R, mnIo, compactMnLegacyReg_rg] using hout.dwn)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rwn)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rmn)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rnn)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rsq)
    (by simpa only [embStk_R, mnRnd, compactMnLegacyReg_rg] using hout.rwo)
  simpa only [compactMain_runs_eq compactRetunedDist compactRetunedCF compactRetunedCO
    (srcHd0 hbig), compactRetunedCF, compactRetunedCO] using h

end
end IntegerMultBounds.MathlibTM2.Fast.Main
