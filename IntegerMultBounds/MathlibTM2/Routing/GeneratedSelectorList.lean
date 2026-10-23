module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedSelectorRuns
public import IntegerMultBounds.MathlibTM2.Routing.SparseSelectorCompress
public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunCompile

/-! Generate the reusable absent-selector frame once, expand the whole compact
stream, restore that input, and erase the frame. Only dense output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W : ℕ} {P U : Type}

theorem generatedSelectorList_exec (body : P → Pr P T Q A U)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg) (hblockReg : zero .dst = rg .block)
    (Lw Lg L : ℕ) (hL : L < 2 ^ Lw)
    (qs : List (Fin (W + 1))) (hsize : qs.length < 2 ^ Lg)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (zero .width) = binSyms Lw L) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hsrc : S.R (rg .src) = selectorRunFrames Lg L (SparseSelectorRun.compress qs).reverse)
    (harchive : S.R (rg .archive) = []) (hblock : S.R (rg .block) = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (Lw * (4 * L + 11) + 8 * L + 13) + selectorRunLoopCost Lg L (SparseSelectorRun.compress qs).reverse +
        2 * (selectorRunFrames (A := A) Lg L (SparseSelectorRun.compress qs).reverse).length + 3 + (2 * (L + 1) + 2) ∧
      Exec body (generatedSelectorRunsProgram zero rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (descriptorSelectorFrames L (qs) ++ S.R (rg .dst)) }) := by
  have hfit : ∀ run ∈ (SparseSelectorRun.compress qs).reverse, run.gap < 2 ^ Lg := by
    intro run hr
    have hm : run ∈ SparseSelectorRun.compress qs := by simpa using hr
    exact (SparseSelectorRun.compress_gap_lt_length qs run hm).trans hsize
  obtain ⟨v', steps, hu, ht, he⟩ := generatedSelectorRuns_exec body zero hzero rg hrg hblockReg
    Lw Lg L hL (SparseSelectorRun.compress qs).reverse hfit v S hwidth hunary hscratch
    hsrc harchive hblock hblank
  simp only [List.reverse_reverse, SparseSelectorRun.expand_compress] at he
  exact ⟨v', steps, hu, ht, he⟩

end IntegerMultBounds.MathlibTM2.Routing
