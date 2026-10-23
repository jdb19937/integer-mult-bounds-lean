module

public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorCompile

/-! Compile an actual descriptor table from compact selector runs. Dense selector
frames are generated, consumed/restored by the descriptor compiler, then erased.
The compact input and all non-output tapes survive; every phase is charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W : ℕ} {P U : Type}

theorem compactPatternTable_exec (body : P → Pr P T Q A U)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (runs : SelectorRunReg → Fin T) (hruns : Function.Injective runs) (hblockReg : zero .dst = runs .block)
    (mask : BinaryMaskReg → Fin T) (hmask : Function.Injective mask)
    (saved out : Fin T) (hss : runs .dst ≠ saved) (hso : runs .dst ≠ out) (hao : saved ≠ out)
    (hsrcMask : ∀ r, runs .dst ≠ mask r) (hsavedMask : ∀ r, saved ≠ mask r) (houtMask : ∀ r, out ≠ mask r)
    (Lw Lg L : ℕ) (hL : L < 2 ^ Lw) (hW : W + 1 < 2 ^ L)
    {N : ℕ} (pattern : Fin N → Option (Fin W)) (hsize : N < 2 ^ Lg)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (zero .width) = binSyms Lw L) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hinput : S.R (runs .src) = selectorRunFrames Lg L (SparseSelectorRun.compress (List.ofFn (patternIndex pattern)).reverse).reverse)
    (harchive : S.R (runs .archive) = []) (hblock : S.R (runs .block) = []) (hselectors : S.R (runs .dst) = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (runs r) = [])
    (hready : DescriptorCompileReady mask S.R L (W + 1)) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ ((Lw * (4 * L + 11) + 8 * L + 13) + selectorRunLoopCost Lg L (SparseSelectorRun.compress (List.ofFn (patternIndex pattern)).reverse).reverse +
        2 * (selectorRunFrames (A := A) Lg L (SparseSelectorRun.compress (List.ofFn (patternIndex pattern)).reverse).reverse).length + 3 + (2 * (L + 1) + 2)) +
        (N * (descriptorCompileCallCost L (W + 1) + 2) + 2 * (N * (L + 1)) + 4) +
        (2 * (N * (L + 1)) + 2) ∧
      Exec body (compactDescriptorProgram zero runs mask saved out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out ((patternTable pattern).flatten.map (bitSymbol (a := A)) ++ S.R out) }) := by
  obtain ⟨v', steps, hu, ht, he⟩ := compactDescriptor_exec body zero hzero runs hruns hblockReg mask hmask
    saved out hss hso hao hsrcMask hsavedMask houtMask Lw Lg L hL hW
    (List.ofFn (patternIndex pattern)) (by simpa using hsize) v S hwidth hunary hscratch
    hinput harchive hblock hselectors hblank hready hsaved
  exact ⟨v', steps, hu, by simpa only [List.length_ofFn] using ht, he⟩

end IntegerMultBounds.MathlibTM2.Routing
