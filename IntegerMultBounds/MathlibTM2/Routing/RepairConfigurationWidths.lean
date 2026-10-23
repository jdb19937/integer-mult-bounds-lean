module

public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationData
public import IntegerMultBounds.MathlibTM2.Routing.FieldPairClean

/-! Actual width generation inside the combined descriptor/width bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev repairDescriptorT := repairT + (2 * 11 + 12)
abbrev repairConfigurationT := repairDescriptorT + 6

def repairConfigurationWidthJobs (Lr Lm rb wy : ℕ) : List (BinaryFieldJob repairConfigurationT) :=
  fieldPairJobs (descriptorCore (repairSetupSource (.inr .row)))
    (descriptorCore (repairSetupSource (.inr .keyMask))) Lr Lm rb wy

def repairConfigurationWidthBank {A : ℕ} (rb wy : ℕ)
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) :=
  fieldPairGenerated (descriptorCore (repairSetupSource (.inr .row)))
    (descriptorCore (repairSetupSource (.inr .keyMask))) rb wy bank

theorem repairConfigurationWidthBank_project {A : ℕ} (rb wy : ℕ)
    (bank : Fin repairConfigurationT → List (Fin (A + 4))) :
    (fun i => repairConfigurationWidthBank rb wy bank (fieldCore i)) =
      repairConfigurationWidths rb wy (fun i => bank (fieldCore i)) :=
  fieldPairGenerated_project _ _ rb wy bank

theorem repairConfigurationWidths_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P repairConfigurationT Q A U) (Lr Lm rb wy : ℕ)
    (hr : rb < 2 ^ Lr) (hm : wy < 2 ^ Lm)
    (v : HS repairConfigurationT Q A U) (S : Stacks repairConfigurationT A)
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm wy)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (descriptorCore (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R (fieldCore (descriptorCore (repairSetupSource (.inr .keyMask)))) = []) :
    ∃ (v' : HS repairConfigurationT Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * wy + 11) + 2 * wy + 6) + 1 ∧
      Exec body (binaryFieldBatch (repairConfigurationWidthJobs Lr Lm rb wy)) (mk v S) m
        (mk v' { S with R := repairConfigurationWidthBank rb wy S.R }) := by
  exact fieldPair_exec body _ _ (descriptorCore_injective.ne (by simp [repairSetupSource]))
    Lr Lm rb wy hr hm v S hrowWidth hmaskWidth hscratch hrow hmask

end
end IntegerMultBounds.MathlibTM2.Routing
