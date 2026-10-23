module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedSelectorList

/-! Compile an actual descriptor table from compact selector runs. Dense selector
frames are generated, consumed/restored by the descriptor compiler, then erased.
The compact input and all non-output tapes survive; every phase is charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W : ℕ} {P U : Type}

def compactDescriptorProgram (zero : BinaryZeroReg → Fin T) (runs : SelectorRunReg → Fin T)
    (mask : BinaryMaskReg → Fin T) (saved out : Fin T) : Pr P T Q A U :=
  .seq (generatedSelectorRunsProgram zero runs)
    (.seq (descriptorCompileProgram mask (runs .dst) saved out) (bclear (runs .dst)))

theorem compactDescriptor_exec (body : P → Pr P T Q A U)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (runs : SelectorRunReg → Fin T) (hruns : Function.Injective runs) (hblockReg : zero .dst = runs .block)
    (mask : BinaryMaskReg → Fin T) (hmask : Function.Injective mask)
    (saved out : Fin T) (hss : runs .dst ≠ saved) (hso : runs .dst ≠ out) (hao : saved ≠ out)
    (hsrcMask : ∀ r, runs .dst ≠ mask r) (hsavedMask : ∀ r, saved ≠ mask r) (houtMask : ∀ r, out ≠ mask r)
    (Lw Lg L : ℕ) (hL : L < 2 ^ Lw) (hW : W + 1 < 2 ^ L)
    (qs : List (Fin (W + 1))) (hsize : qs.length < 2 ^ Lg)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (zero .width) = binSyms Lw L) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hinput : S.R (runs .src) = selectorRunFrames Lg L (SparseSelectorRun.compress qs.reverse).reverse)
    (harchive : S.R (runs .archive) = []) (hblock : S.R (runs .block) = []) (hselectors : S.R (runs .dst) = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (runs r) = [])
    (hready : DescriptorCompileReady mask S.R L (W + 1)) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ ((Lw * (4 * L + 11) + 8 * L + 13) + selectorRunLoopCost Lg L (SparseSelectorRun.compress qs.reverse).reverse +
        2 * (selectorRunFrames (A := A) Lg L (SparseSelectorRun.compress qs.reverse).reverse).length + 3 + (2 * (L + 1) + 2)) +
        (qs.length * (descriptorCompileCallCost L (W + 1) + 2) + 2 * (qs.length * (L + 1)) + 4) +
        (2 * (qs.length * (L + 1)) + 2) ∧
      Exec body (compactDescriptorProgram zero runs mask saved out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out ((sourceTable qs).flatten.map (bitSymbol (a := A)) ++ S.R out) }) := by
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := generatedSelectorList_exec body zero hzero runs hruns hblockReg
    Lw Lg L hL qs.reverse (by simpa using hsize) v S hwidth hunary hscratch hinput harchive hblock hblank
  rw [hselectors, List.append_nil] at he₁
  let selectors := descriptorSelectorFrames (A := A) L qs.reverse
  let S₁ : Stacks T A := { S with R := Function.update S.R (runs .dst) selectors }
  have hm : DescriptorCompileReady mask S₁.R L (W + 1) := by
    constructor
    · simp only [S₁, Function.update_of_ne (hsrcMask .width).symm]; exact hready.width
    · intro r hr
      simp only [S₁, Function.update_of_ne (hsrcMask r).symm]; exact hready.blank r hr
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := sourceTableCompile_exec body mask hmask (runs .dst) saved out hss hso hao
    hsrcMask hsavedMask houtMask L hW qs v₁ S₁ hm (by simp [S₁, selectors])
    (by simp [S₁, hss.symm, hsaved])
  have ho : S₁.R out = S.R out := Function.update_of_ne hso.symm _ _
  rw [ho] at he₂
  let word := (sourceTable qs).flatten.map (bitSymbol (a := A)) ++ S.R out
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R out word }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (runs .dst) v₂ S₂
  have hs : S₂.R (runs .dst) = selectors := by simp [S₂, S₁, hso]
  have hf : Function.update S₂.R (runs .dst) [] = Function.update S.R out word := by
    funext j
    by_cases hj : j = runs .dst
    · subst j; simp [hso, hselectors]
    · by_cases ho : j = out
      · subst j; simp [S₂, S₁, hj]
      · simp [S₂, S₁, hj, ho]
  rw [hf, hs] at he₃
  have hl : selectors.length = qs.length * (L + 1) := by simp [selectors, descriptorSelectorFrames_length]
  rw [hl] at he₃
  exact ⟨v₃, n₁ + (n₂ + (2 * (qs.length * (L + 1)) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
