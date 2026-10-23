module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorBank
public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupData

/-! The eleven actual R2 descriptor jobs: two per selective offset plus the
repair key descriptor. Binary selector inputs remain to be generated. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev RepairDescriptorKey := Option (Off × Fin 2)

def repairDescriptorKey (j : Fin 11) : RepairDescriptorKey :=
  [none, some (.A, 0), some (.A, 1), some (.Z, 0), some (.Z, 1),
    some (.Y, 0), some (.Y, 1), some (.YZ, 0), some (.YZ, 1), some (.X, 0), some (.X, 1)].get j

def repairDescriptorSource : RepairDescriptorKey → Fin repairT
  | none => repairSetupSource (.inr .keyDescriptor)
  | some (off, k) => repairSetupSource (.inl (.desc off k))

def repairDescriptorWidth (p : Par) (X : ℕ) : RepairDescriptorKey → ℕ
  | none => p.wy + 2 * p.wc + X + 1
  | some (off, _) => selectiveSourceWidth p X off + 1

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def repairDescriptorIndices : (key : RepairDescriptorKey) → List (Fin (repairDescriptorWidth p X key))
  | none => List.ofFn (patternIndex (selectiveKeyPattern p X active s))
  | some (off, k) => List.ofFn (patternIndex (selectivePatterns p X hG hK active s off k))

def repairDescriptorWord {A : ℕ} : RepairDescriptorKey → List (Fin (A + 4))
  | none => (patternTable (selectiveKeyPattern p X active s)).flatten.map bitSymbol
  | some (off, k) => (patternTable (selectivePatterns p X hG hK active s off k)).flatten.map bitSymbol

theorem repairDescriptorIndices_word {A : ℕ} (key : RepairDescriptorKey) :
    (sourceTable (repairDescriptorIndices p X hG hK active s key)).flatten.map (bitSymbol (a := A)) =
      repairDescriptorWord p X hG hK active s key := by
  cases key with
  | none => rfl
  | some k => rcases k with ⟨off, k⟩; rfl

def repairDescriptorJobs (L : Fin 11 → ℕ) : List (DescriptorJob (repairT + (2 * 11 + 12))) :=
  List.ofFn (descriptorBankJob (fun j => repairDescriptorSource (repairDescriptorKey j)) L
    (fun j => repairDescriptorWidth p X (repairDescriptorKey j))
    (fun j => repairDescriptorIndices p X hG hK active s (repairDescriptorKey j)))

theorem repairDescriptorBank_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P (repairT + (2 * 11 + 12)) Q A U) (L : Fin 11 → ℕ)
    (v : HS (repairT + (2 * 11 + 12)) Q A U) (S : Stacks (repairT + (2 * 11 + 12)) A)
    (hfit : ∀ j, repairDescriptorWidth p X (repairDescriptorKey j) < 2 ^ L j)
    (hwidth : ∀ j, S.R (descriptorBankReg j .width) = binSyms (L j) (repairDescriptorWidth p X (repairDescriptorKey j)))
    (hinput : ∀ j, S.R (descriptorBankSelectors j) = descriptorSelectorFrames (L j)
      (repairDescriptorIndices p X hG hK active s (repairDescriptorKey j)).reverse)
    (hblank : ∀ i : Fin (2 * 11 + 12), 2 * 11 ≤ i.val → S.R (descriptorAux i) = []) :
    ∃ (v' : HS (repairT + (2 * 11 + 12)) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ descriptorBatchCost (repairDescriptorJobs p X hG hK active s L) ∧
      Exec body (descriptorBatch (repairDescriptorJobs p X hG hK active s L)) (mk v S) m
        (mk v' { S with R := descriptorBankGenerated S.R (repairDescriptorJobs p X hG hK active s L) }) := by
  exact descriptorBank_exec body _ L _ _ v S hfit hwidth hinput hblank

end
end IntegerMultBounds.MathlibTM2.Routing
