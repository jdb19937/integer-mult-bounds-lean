module

public import IntegerMultBounds.MathlibTM2.Routing.CoordinateSelectorGenerate

/-! Compute descriptor tables from absolute sparse coordinates, erasing both
compact and dense intermediate streams. Only the descriptor output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W : ℕ} {P U : Type}

def coordinateDescriptorProgram (coord : SparseCoordinateReg → Fin T) (saved : Fin T)
    (zero : BinaryZeroReg → Fin T) (rg : SelectorRunReg → Fin T)
    (mask : BinaryMaskReg → Fin T) (archive out : Fin T) : Pr P T Q A U :=
  .seq (coordinateSelectorProgram coord saved zero rg)
    (.seq (descriptorCompileProgram mask (rg .dst) archive out) (bclear (rg .dst)))

theorem coordinateDescriptor_exec (body : P → Pr P T Q A U)
    (coord : SparseCoordinateReg → Fin T) (hcoord : Function.Injective coord)
    (saved : Fin T) (hsavedSep : ∀ r, saved ≠ coord r)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg)
    (hjoin : rg .src = coord .dst) (hblockReg : zero .dst = rg .block)
    (hzeroSep : ∀ r, zero r ≠ coord .dst)
    (hrunSep : ∀ r, r ≠ .src → rg r ≠ coord .dst)
    (Lw L Ls cursor : ℕ) (hLs : Ls < 2 ^ Lw)
    (entries : List (ℕ × Fin (W + 1)))
    (hready : SparseCoordinatesReady L cursor (sparseCoordinateValues entries))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (coord .src) = sparseCoordinateFrames L Ls (sparseCoordinateValues entries))
    (harchive : S.R (coord .archive) = []) (hcursor : S.R (coord .cursor) = binSyms L cursor)
    (hone : S.R (coord .one) = binSyms L 1) (hsaved : S.R saved = []) (hcompact : S.R (coord .dst) = [])
    (hcoordBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S.R (coord r) = [])
    (hwidth : S.R (zero .width) = binSyms Lw Ls) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hrArchive : S.R (rg .archive) = []) (hrBlock : S.R (rg .block) = [])
    (hrBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = [])
    (mask : BinaryMaskReg → Fin T) (hmask : Function.Injective mask) (archive out : Fin T)
    (hsa : rg .dst ≠ archive) (hso : rg .dst ≠ out) (hao : archive ≠ out)
    (hselectorMask : ∀ r, rg .dst ≠ mask r) (harchiveMask : ∀ r, archive ≠ mask r) (houtMask : ∀ r, out ≠ mask r)
    (qs : List (Fin (W + 1)))
    (hindices : SparseSelectorRun.expand (sparseCoordinateRuns cursor entries) = qs.reverse)
    (hW : W + 1 < 2 ^ Ls) (hselectors : S.R (rg .dst) = [])
    (hmaskReady : DescriptorCompileReady mask S.R Ls (W + 1)) (harchiveBlank : S.R archive = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ coordinateSelectorCost Lw L Ls cursor entries +
        (qs.length * (descriptorCompileCallCost Ls (W + 1) + 2) + 2 * (qs.length * (Ls + 1)) + 4) +
        (2 * (qs.length * (Ls + 1)) + 2) ∧
      Exec body (coordinateDescriptorProgram coord saved zero rg mask archive out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out ((sourceTable qs).flatten.map (bitSymbol (a := A)) ++ S.R out) }) := by
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := coordinateSelector_exec body coord hcoord saved hsavedSep zero hzero rg hrg
    hjoin hblockReg hzeroSep hrunSep Lw L Ls cursor hLs entries hready v S hsrc harchive hcursor hone hsaved hcompact
    hcoordBlank hwidth hunary hscratch hrArchive hrBlock hrBlank
  rw [hindices, hselectors, List.append_nil] at he₁
  let selectors := descriptorSelectorFrames (A := A) Ls qs.reverse
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .dst) selectors }
  have hm : DescriptorCompileReady mask S₁.R Ls (W + 1) := by
    constructor
    · dsimp only [S₁]; rw [Function.update_of_ne (hselectorMask .width).symm]; exact hmaskReady.width
    · intro r hr; dsimp only [S₁]; rw [Function.update_of_ne (hselectorMask r).symm]; exact hmaskReady.blank r hr
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := sourceTableCompile_exec body mask hmask (rg .dst) archive out hsa hso hao
    hselectorMask harchiveMask houtMask Ls hW qs v₁ S₁ hm (by simp [S₁, selectors])
    (by simp [S₁, hsa.symm, harchiveBlank])
  have ho : S₁.R out = S.R out := Function.update_of_ne hso.symm _ _
  rw [ho] at he₂
  let word := (sourceTable qs).flatten.map (bitSymbol (a := A)) ++ S.R out
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R out word }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg .dst) v₂ S₂
  have hs : S₂.R (rg .dst) = selectors := by simp [S₂, S₁, hso]
  have hf : Function.update S₂.R (rg .dst) [] = Function.update S.R out word := by
    funext j
    by_cases hj : j = rg .dst
    · subst j; simp [hso, hselectors]
    · by_cases ho : j = out
      · subst j; simp [S₂, S₁, hj]
      · simp [S₂, S₁, hj, ho]
  rw [hf, hs] at he₃
  have hl : selectors.length = qs.length * (Ls + 1) := by simp [selectors, descriptorSelectorFrames_length]
  rw [hl] at he₃
  exact ⟨v₃, n₁ + (n₂ + (2 * (qs.length * (Ls + 1)) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
