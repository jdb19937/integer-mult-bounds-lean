module

public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorBatch

/-! Compact tables use three persistent inputs per job and one shared workspace.
Outputs remain in an arbitrary core bank, disjoint from every compiler tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

inductive CompactDescriptorRole (J : ℕ) where
  | input (j : Fin J) | width (j : Fin J) | sourceWidth (j : Fin J)
  | zeroUnary | zeroScratch (i : Fin 3)
  | archive | gap | entry | loadTmp | count | saved | block | dense | work | tmp | ctmp
  | maskSource | maskLow | maskHigh | maskDst | maskScratch (i : Fin 7) | maskSaved
  deriving DecidableEq, Fintype

noncomputable section

abbrev compactDescriptorT (N J : ℕ) := N + Fintype.card (CompactDescriptorRole J)

def compactDescriptorCore {N J : ℕ} (i : Fin N) : Fin (compactDescriptorT N J) := ⟨i.val, by have := i.isLt; unfold compactDescriptorT; omega⟩

def compactDescriptorAux {N J : ℕ} (r : CompactDescriptorRole J) : Fin (compactDescriptorT N J) :=
  ⟨N + (Fintype.equivFin (CompactDescriptorRole J) r).val, by
    have := (Fintype.equivFin (CompactDescriptorRole J) r).isLt; unfold compactDescriptorT; omega⟩

theorem compactDescriptorCore_injective {N J : ℕ} : Function.Injective (compactDescriptorCore (N := N) (J := J)) := by
  intro i j he; exact Fin.ext (congrArg (fun x : Fin (compactDescriptorT N J) => x.val) he)

theorem compactDescriptorAux_injective {N J : ℕ} : Function.Injective (compactDescriptorAux (N := N) (J := J)) := by
  intro r s he
  apply (Fintype.equivFin (CompactDescriptorRole J)).injective
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [compactDescriptorAux] at hv
  omega

theorem compactDescriptorCore_aux {N J : ℕ} (i : Fin N) (r : CompactDescriptorRole J) :
    compactDescriptorCore i ≠ compactDescriptorAux r := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [compactDescriptorCore, compactDescriptorAux] at hv
  omega

def compactZeroRole {J : ℕ} (j : Fin J) : BinaryZeroReg → CompactDescriptorRole J
  | .width => .width j
  | .unary => .zeroUnary
  | .dst => .block
  | .scratch i => .zeroScratch i

def compactRunRole {J : ℕ} (j : Fin J) : SelectorRunReg → CompactDescriptorRole J
  | .src => .input j
  | .archive => .archive
  | .gap => .gap
  | .entry => .entry
  | .loadTmp => .loadTmp
  | .count => .count
  | .saved => .saved
  | .block => .block
  | .dst => .dense
  | .work => .work
  | .tmp => .tmp
  | .ctmp => .ctmp

def compactMaskRole {J : ℕ} (j : Fin J) : BinaryMaskReg → CompactDescriptorRole J
  | .width => .sourceWidth j
  | .source => .maskSource
  | .low => .maskLow
  | .high => .maskHigh
  | .dst => .maskDst
  | .scratch i => .maskScratch i

def compactBankZero {N J : ℕ} (j : Fin J) : BinaryZeroReg → Fin (compactDescriptorT N J) :=
  compactDescriptorAux ∘ compactZeroRole j

def compactBankRuns {N J : ℕ} (j : Fin J) : SelectorRunReg → Fin (compactDescriptorT N J) :=
  compactDescriptorAux ∘ compactRunRole j

def compactBankMask {N J : ℕ} (j : Fin J) : BinaryMaskReg → Fin (compactDescriptorT N J) :=
  compactDescriptorAux ∘ compactMaskRole j

theorem compactBankZero_injective {N J : ℕ} (j : Fin J) : Function.Injective (compactBankZero (N := N) j) := by
  intro r s he
  have hh := compactDescriptorAux_injective he
  cases r <;> cases s <;> simp_all [compactZeroRole]

theorem compactBankRuns_injective {N J : ℕ} (j : Fin J) : Function.Injective (compactBankRuns (N := N) j) := by
  intro r s he
  have hh := compactDescriptorAux_injective he
  cases r <;> cases s <;> simp_all [compactRunRole]

theorem compactBankMask_injective {N J : ℕ} (j : Fin J) : Function.Injective (compactBankMask (N := N) j) := by
  intro r s he
  have hh := compactDescriptorAux_injective he
  cases r <;> cases s <;> simp_all [compactMaskRole]

@[simp] theorem compactBank_block {N J : ℕ} (j : Fin J) :
    compactBankZero (N := N) j .dst = compactBankRuns j .block := rfl

theorem compactBank_dense_saved {N J : ℕ} (j : Fin J) :
    compactBankRuns (N := N) j .dst ≠ compactDescriptorAux (.maskSaved : CompactDescriptorRole J) :=
  compactDescriptorAux_injective.ne (by simp [compactRunRole])

theorem compactBank_dense_mask {N J : ℕ} (j : Fin J) (r : BinaryMaskReg) :
    compactBankRuns (N := N) j .dst ≠ compactBankMask j r := by
  apply compactDescriptorAux_injective.ne
  cases r <;> simp [compactRunRole, compactMaskRole]

theorem compactBank_saved_mask {N J : ℕ} (j : Fin J) (r : BinaryMaskReg) :
    compactDescriptorAux (N := N) (.maskSaved : CompactDescriptorRole J) ≠ compactBankMask j r := by
  apply compactDescriptorAux_injective.ne
  cases r <;> simp [compactMaskRole]

end
end IntegerMultBounds.MathlibTM2.Routing
