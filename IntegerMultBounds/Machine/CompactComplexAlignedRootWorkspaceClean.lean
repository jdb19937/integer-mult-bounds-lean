module

public import IntegerMultBounds.Machine.CompactComplexRootWorkspaceClean
public import IntegerMultBounds.Machine.CompactComplexAlignedBoundaryPaths

/-! Explicit scalar and basis cleanup on the exact prime-alphabet root output
bank. Together with the binary endpoint certificate, these cover the actual
role, frame, leaf, work, scalar and basis workspace of the halted trace. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedRootWorkspaceClean
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyScalarWorkspace (roles scratch)
open CompactComplexActualCallFullAlignment (localTapes)
open CompactComplexAlignedBoundaryPaths (alignedBank)
variable {stackCount : ℕ}

/-- The actual aligned output clears every scalar-work tape and its head. -/
theorem scalar_blank (outputBank : Tapes (CompactComplexSourceReadyWorkspace.tapes stackCount roles) 2)
    (scalarPort : Fin scratch) :
    (alignedBank (outputBank.append (SharedBank.empty scratch 2))).head
      (Fin.castAdd (localTapes roles)
        (Fin.natAdd (CompactComplexSourceReadyWorkspace.tapes stackCount roles) scalarPort))=0 ∧
    (alignedBank (outputBank.append (SharedBank.empty scratch 2))).tape
      (Fin.castAdd (localTapes roles)
        (Fin.natAdd (CompactComplexSourceReadyWorkspace.tapes stackCount roles) scalarPort))=(fun _ => (blank : Fin (prime+4))) := by
  constructor
  · simp only [alignedBank,Tapes.append,Fin.addCases_left,Fin.addCases_right,Alphabet.mapTapes,SharedBank.empty]
  · funext cell
    simp only [alignedBank,Tapes.append,Fin.addCases_left,Fin.addCases_right,Alphabet.mapTapes,SharedBank.empty]
    rfl

/-- The actual aligned output clears the complete appended basis workspace. -/
theorem basis_blank (outputBank : Tapes (CompactComplexSourceReadyWorkspace.tapes stackCount roles) 2)
    (basisPort : Fin (localTapes roles)) :
    (alignedBank (outputBank.append (SharedBank.empty scratch 2))).head
      (Fin.natAdd (CompactComplexSourceReadyScalarWorkspace.tapes stackCount roles) basisPort)=0 ∧
    (alignedBank (outputBank.append (SharedBank.empty scratch 2))).tape
      (Fin.natAdd (CompactComplexSourceReadyScalarWorkspace.tapes stackCount roles) basisPort)=(fun _ => (blank : Fin (prime+4))) := by
  constructor <;> simp only [alignedBank,Tapes.append,Fin.addCases_right,SharedBank.empty]

/-- Both actual physical suffixes are clean on the same root endpoint used by
the halting theorem, rather than on a separately chosen clean bank. -/
theorem aligned_suffix_clean (outputBank : Tapes (CompactComplexSourceReadyWorkspace.tapes stackCount roles) 2) :
    (∀ scalarPort : Fin scratch,
      (alignedBank (outputBank.append (SharedBank.empty scratch 2))).head
        (Fin.castAdd (localTapes roles)
          (Fin.natAdd (CompactComplexSourceReadyWorkspace.tapes stackCount roles) scalarPort))=0 ∧
      (alignedBank (outputBank.append (SharedBank.empty scratch 2))).tape
        (Fin.castAdd (localTapes roles)
          (Fin.natAdd (CompactComplexSourceReadyWorkspace.tapes stackCount roles) scalarPort))=(fun _ => (blank : Fin (prime+4)))) ∧
    (∀ basisPort : Fin (localTapes roles),
      (alignedBank (outputBank.append (SharedBank.empty scratch 2))).head
        (Fin.natAdd (CompactComplexSourceReadyScalarWorkspace.tapes stackCount roles) basisPort)=0 ∧
      (alignedBank (outputBank.append (SharedBank.empty scratch 2))).tape
        (Fin.natAdd (CompactComplexSourceReadyScalarWorkspace.tapes stackCount roles) basisPort)=(fun _ => (blank : Fin (prime+4)))) :=
  ⟨scalar_blank outputBank,basis_blank outputBank⟩

end
end IntegerMultBounds.Machine.CompactComplexAlignedRootWorkspaceClean
