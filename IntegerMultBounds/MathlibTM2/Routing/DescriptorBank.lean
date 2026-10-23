module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorBankLayout

/-! Generate a complete finite descriptor bank from binary input words.
All tables share one compiler and archive; only core output registers change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {N J Q A : ℕ} {P U : Type}

def descriptorBankJob (dst : Fin J → Fin N) (L W : Fin J → ℕ)
    (qs : (j : Fin J) → List (Fin (W j))) (j : Fin J) : DescriptorJob (N + (2 * J + 12)) where
  reg := descriptorBankReg j
  selectors := descriptorBankSelectors j
  saved := descriptorBankSaved
  dst := descriptorCore (dst j)
  width := L j
  sourceWidth := W j
  indices := qs j

theorem descriptorBankJob_ready (dst : Fin J → Fin N) (L W : Fin J → ℕ)
    (qs : (j : Fin J) → List (Fin (W j))) (j : Fin J)
    (R : Fin (N + (2 * J + 12)) → List (Fin (A + 4))) (hfit : W j < 2 ^ L j)
    (hwidth : R (descriptorBankReg j .width) = binSyms (L j) (W j))
    (hinput : R (descriptorBankSelectors j) = descriptorSelectorFrames (L j) (qs j).reverse)
    (hblank : ∀ i : Fin (2 * J + 12), 2 * J ≤ i.val → R (descriptorAux i) = []) :
    (descriptorBankJob dst L W qs j).Ready R := by
  refine ⟨descriptorBankReg_injective j, descriptorBankSelectors_saved j, ?_, ?_,
    descriptorBankSelectors_reg j, descriptorBankSaved_reg j, ?_, hfit, ?_, hinput, ?_⟩
  · exact (descriptorCore_aux (dst j) _).symm
  · exact (descriptorCore_aux (dst j) _).symm
  · exact descriptorCore_reg (dst j) j
  · constructor
    · exact hwidth
    · intro r hr
      cases r with
      | width => exact (hr rfl).elim
      | source => exact hblank _ (by change 2 * J ≤ 2 * J + 1; omega)
      | low => exact hblank _ (by change 2 * J ≤ 2 * J + 2; omega)
      | high => exact hblank _ (by change 2 * J ≤ 2 * J + 3; omega)
      | dst => exact hblank _ (by change 2 * J ≤ 2 * J + 4; omega)
      | scratch i => exact hblank _ (by change 2 * J ≤ 2 * J + 5 + i.val; omega)
  · exact hblank _ (by change 2 * J ≤ 2 * J; omega)

theorem descriptorBank_exec (body : P → Pr P (N + (2 * J + 12)) Q A U)
    (dst : Fin J → Fin N) (L W : Fin J → ℕ) (qs : (j : Fin J) → List (Fin (W j)))
    (v : HS (N + (2 * J + 12)) Q A U) (S : Stacks (N + (2 * J + 12)) A)
    (hfit : ∀ j, W j < 2 ^ L j)
    (hwidth : ∀ j, S.R (descriptorBankReg j .width) = binSyms (L j) (W j))
    (hinput : ∀ j, S.R (descriptorBankSelectors j) = descriptorSelectorFrames (L j) (qs j).reverse)
    (hblank : ∀ i : Fin (2 * J + 12), 2 * J ≤ i.val → S.R (descriptorAux i) = []) :
    let jobs := List.ofFn (descriptorBankJob dst L W qs)
    ∃ (v' : HS (N + (2 * J + 12)) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ descriptorBatchCost jobs ∧
      Exec body (descriptorBatch jobs) (mk v S) m
        (mk v' { S with R := descriptorBankGenerated S.R jobs }) := by
  apply descriptorBatch_exec
  · intro job hj other ho r
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    exact descriptorCore_reg (dst j) k r
  · intro job hj other ho
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    exact descriptorCore_aux (dst j) _
  · intro job hj other ho
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    exact descriptorCore_aux (dst j) _
  · intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    exact descriptorBankJob_ready dst L W qs j S.R (hfit j) (hwidth j) (hinput j) hblank

end IntegerMultBounds.MathlibTM2.Routing
