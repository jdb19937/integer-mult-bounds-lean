module

public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorLayout

/-! Concrete compact descriptor jobs share workspace and keep outputs in the
core. Initial input words and shared blanks derive each job's readiness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

noncomputable section

variable {N J A : ℕ}

def compactBankJob (dst : Fin J → Fin N) (Lw Lg L W : Fin J → ℕ)
    (qs : (j : Fin J) → List (Fin (W j + 1))) (j : Fin J) : CompactDescriptorJob (compactDescriptorT N J) where
  zero := compactBankZero j
  runs := compactBankRuns j
  mask := compactBankMask j
  saved := compactDescriptorAux .maskSaved
  dst := compactDescriptorCore (dst j)
  widthBits := Lw j
  gapBits := Lg j
  width := L j
  sourceWidth := W j
  indices := qs j

theorem compactBankJob_ready (dst : Fin J → Fin N) (Lw Lg L W : Fin J → ℕ)
    (qs : (j : Fin J) → List (Fin (W j + 1))) (j : Fin J)
    (R : Fin (compactDescriptorT N J) → List (Fin (A + 4)))
    (hL : L j < 2 ^ Lw j) (hW : W j + 1 < 2 ^ L j) (hsize : (qs j).length < 2 ^ Lg j)
    (hwidth : R (compactDescriptorAux (.width j)) = binSyms (Lw j) (L j))
    (hsourceWidth : R (compactDescriptorAux (.sourceWidth j)) = binSyms (L j) (W j + 1))
    (hinput : R (compactDescriptorAux (.input j)) = selectorRunFrames (Lg j) (L j) (SparseSelectorRun.compress (qs j).reverse).reverse)
    (hblank : ∀ r : CompactDescriptorRole J,
      (∀ k, r ≠ .input k) → (∀ k, r ≠ .width k) → (∀ k, r ≠ .sourceWidth k) → R (compactDescriptorAux r) = []) :
    (compactBankJob dst Lw Lg L W qs j).Ready R := by
  have hb (r : CompactDescriptorRole J) (hi : ∀ k, r ≠ .input k)
      (hw : ∀ k, r ≠ .width k) (hs : ∀ k, r ≠ .sourceWidth k) := hblank r hi hw hs
  refine ⟨compactBankZero_injective j, compactBankRuns_injective j, compactBankMask_injective j,
    rfl, compactBank_dense_saved j, ?_, ?_, compactBank_dense_mask j, compactBank_saved_mask j, ?_,
    hL, hW, hsize, hwidth, ?_, ?_, hinput, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (compactDescriptorCore_aux (dst j) _).symm
  · exact (compactDescriptorCore_aux (dst j) _).symm
  · intro r; exact compactDescriptorCore_aux (dst j) _
  · exact hb .zeroUnary (by simp) (by simp) (by simp)
  · intro i; exact hb (.zeroScratch i) (by simp) (by simp) (by simp)
  · exact hb .archive (by simp) (by simp) (by simp)
  · exact hb .block (by simp) (by simp) (by simp)
  · exact hb .dense (by simp) (by simp) (by simp)
  · intro r hs ha hblock hd
    cases r <;> first
      | exact (hs rfl).elim
      | exact (ha rfl).elim
      | exact (hblock rfl).elim
      | exact (hd rfl).elim
      | exact hb _ (by simp [compactRunRole]) (by simp [compactRunRole]) (by simp [compactRunRole])
  · constructor
    · exact hsourceWidth
    · intro r hr
      cases r with
      | width => exact (hr rfl).elim
      | source => exact hb .maskSource (by simp) (by simp) (by simp)
      | low => exact hb .maskLow (by simp) (by simp) (by simp)
      | high => exact hb .maskHigh (by simp) (by simp) (by simp)
      | dst => exact hb .maskDst (by simp) (by simp) (by simp)
      | scratch i => exact hb (.maskScratch i) (by simp) (by simp) (by simp)
  · exact hb .maskSaved (by simp) (by simp) (by simp)

theorem compactBank_exec {Q : ℕ} {P U : Type}
    (body : P → Pr P (compactDescriptorT N J) Q A U)
    (dst : Fin J → Fin N) (Lw Lg L W : Fin J → ℕ)
    (qs : (j : Fin J) → List (Fin (W j + 1)))
    (v : HS (compactDescriptorT N J) Q A U) (S : Stacks (compactDescriptorT N J) A)
    (hL : ∀ j, L j < 2 ^ Lw j) (hW : ∀ j, W j + 1 < 2 ^ L j)
    (hsize : ∀ j, (qs j).length < 2 ^ Lg j)
    (hwidth : ∀ j, S.R (compactDescriptorAux (.width j)) = binSyms (Lw j) (L j))
    (hsourceWidth : ∀ j, S.R (compactDescriptorAux (.sourceWidth j)) = binSyms (L j) (W j + 1))
    (hinput : ∀ j, S.R (compactDescriptorAux (.input j)) = selectorRunFrames (Lg j) (L j) (SparseSelectorRun.compress (qs j).reverse).reverse)
    (hblank : ∀ r : CompactDescriptorRole J,
      (∀ k, r ≠ .input k) → (∀ k, r ≠ .width k) → (∀ k, r ≠ .sourceWidth k) → S.R (compactDescriptorAux r) = []) :
    let jobs := List.ofFn (compactBankJob dst Lw Lg L W qs)
    ∃ (v' : HS (compactDescriptorT N J) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ compactDescriptorBatchCost jobs ∧
      Exec body (compactDescriptorBatch jobs) (mk v S) steps
        (mk v' { S with R := compactDescriptorBankGenerated S.R jobs }) := by
  apply compactDescriptorBatch_exec
  · intro job hj other ho r
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    exact compactDescriptorCore_aux (dst j) _
  · intro job hj other ho r
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    exact compactDescriptorCore_aux (dst j) _
  · intro job hj other ho r
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    exact compactDescriptorCore_aux (dst j) _
  · intro job hj other ho
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    exact compactDescriptorCore_aux (dst j) _
  · intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    exact compactBankJob_ready dst Lw Lg L W qs j S.R (hL j) (hW j) (hsize j)
      (hwidth j) (hsourceWidth j) (hinput j) hblank

end
end IntegerMultBounds.MathlibTM2.Routing
