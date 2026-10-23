module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactWidthData
public import IntegerMultBounds.MathlibTM2.Routing.FieldPairClean

/-! Actual width generation inside the combined descriptor/width bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev repairCompactConfigurationT := repairCompactT + 6

def repairCompactWidthJobs (Lr Lm rb wy : ℕ) : List (BinaryFieldJob repairCompactConfigurationT) :=
  fieldPairJobs (compactDescriptorCore (repairSetupSource (.inr .row)))
    (compactDescriptorCore (repairSetupSource (.inr .keyMask))) Lr Lm rb wy

def repairCompactWidthBank {A : ℕ} (rb wy : ℕ)
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) :=
  fieldPairGenerated (compactDescriptorCore (repairSetupSource (.inr .row)))
    (compactDescriptorCore (repairSetupSource (.inr .keyMask))) rb wy bank

theorem repairCompactWidthBank_project {A : ℕ} (rb wy : ℕ)
    (bank : Fin repairCompactConfigurationT → List (Fin (A + 4))) :
    (fun i => repairCompactWidthBank rb wy bank (fieldCore i)) =
      repairCompactWidths rb wy (fun i => bank (fieldCore i)) :=
  fieldPairGenerated_project _ _ rb wy bank

theorem repairCompactWidths_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P repairCompactConfigurationT Q A U) (Lr Lm rb wy : ℕ)
    (hr : rb < 2 ^ Lr) (hm : wy < 2 ^ Lm)
    (v : HS repairCompactConfigurationT Q A U) (S : Stacks repairCompactConfigurationT A)
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm wy)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (compactDescriptorCore (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R (fieldCore (compactDescriptorCore (repairSetupSource (.inr .keyMask)))) = []) :
    ∃ (v' : HS repairCompactConfigurationT Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * wy + 11) + 2 * wy + 6) + 1 ∧
      Exec body (binaryFieldBatch (repairCompactWidthJobs Lr Lm rb wy)) (mk v S) m
        (mk v' { S with R := repairCompactWidthBank rb wy S.R }) := by
  exact fieldPair_exec body _ _ (compactDescriptorCore_injective.ne (by simp [repairSetupSource]))
    Lr Lm rb wy hr hm v S hrowWidth hmaskWidth hscratch hrow hmask

end
end IntegerMultBounds.MathlibTM2.Routing
