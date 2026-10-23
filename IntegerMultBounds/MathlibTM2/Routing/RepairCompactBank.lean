module

public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorContents
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactPattern
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorContents

/-! The actual eleven repair descriptor jobs compiled from compact inputs.
All jobs share one workspace; exact outputs and complete auxiliary restoration
follow from concrete initial words and blanks. Compact inputs remain supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev repairCompactT := compactDescriptorT repairT 11

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def repairCompactIndices (j : Fin 11) :=
  List.ofFn (patternIndex (repairCompactPattern p X hG hK active s (repairDescriptorKey j)))

def repairCompactJobs (Lw Lg L : Fin 11 → ℕ) :=
  List.ofFn (compactBankJob (fun j => repairDescriptorSource (repairDescriptorKey j)) Lw Lg L
    (fun j => repairCompactSourceWidth p X (repairDescriptorKey j)) (repairCompactIndices p X hG hK active s))

theorem repairCompactBank_exec {Q : ℕ} {P U : Type}
    (body : P → Pr P (repairCompactT) Q A U)
    (Lw Lg L : Fin 11 → ℕ)
    (v : HS (repairCompactT) Q A U) (S : Stacks (repairCompactT) A)
    (hL : ∀ j, L j < 2 ^ Lw j) (hW : ∀ j, repairCompactSourceWidth p X (repairDescriptorKey j) + 1 < 2 ^ L j)
    (hsize : ∀ j, repairCompactRows p (repairDescriptorKey j) < 2 ^ Lg j)
    (hwidth : ∀ j, S.R (compactDescriptorAux (.width j)) = binSyms (Lw j) (L j))
    (hsourceWidth : ∀ j, S.R (compactDescriptorAux (.sourceWidth j)) = binSyms (L j) (repairCompactSourceWidth p X (repairDescriptorKey j) + 1))
    (hinput : ∀ j, S.R (compactDescriptorAux (.input j)) = selectorRunFrames (Lg j) (L j) (SparseSelectorRun.compress (repairCompactIndices p X hG hK active s j).reverse).reverse)
    (hblank : ∀ r : CompactDescriptorRole 11,
      (∀ k, r ≠ .input k) → (∀ k, r ≠ .width k) → (∀ k, r ≠ .sourceWidth k) → S.R (compactDescriptorAux r) = []) :
    let jobs := repairCompactJobs p X hG hK active s Lw Lg L
    ∃ (v' : HS (repairCompactT) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ compactDescriptorBatchCost jobs ∧
      Exec body (compactDescriptorBatch jobs) (mk v S) steps
        (mk v' { S with R := compactDescriptorBankGenerated S.R jobs }) := by
  apply compactBank_exec body (fun j => repairDescriptorSource (repairDescriptorKey j)) Lw Lg L
    (fun j => repairCompactSourceWidth p X (repairDescriptorKey j)) (repairCompactIndices p X hG hK active s)
    v S hL hW
  · intro j; simpa [repairCompactIndices] using hsize j
  · exact hwidth
  · exact hsourceWidth
  · exact hinput
  · exact hblank

theorem repairCompactBank_contents {A : ℕ} (Lw Lg L : Fin 11 → ℕ)
    (R : Fin repairCompactT → List (Fin (A + 4))) (j : Fin 11) :
    compactDescriptorBankGenerated R (repairCompactJobs p X hG hK active s Lw Lg L)
      (compactDescriptorCore (repairDescriptorSource (repairDescriptorKey j))) =
      repairDescriptorWord p X hG hK active s (repairDescriptorKey j) ++
        R (compactDescriptorCore (repairDescriptorSource (repairDescriptorKey j))) := by
  rw [← repairCompactPattern_word p X hG hK active s]
  exact compactBankContents _ repairDescriptorSource_injective Lw Lg L _ _ R j

end
end IntegerMultBounds.MathlibTM2.Routing
