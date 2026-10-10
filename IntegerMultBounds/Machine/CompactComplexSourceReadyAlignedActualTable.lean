import IntegerMultBounds.Machine.CompactComplexActualCallFullAlignment
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedActualTable

/-! One fixed corrected recursive table includes physical forward/reverse
basis passes around each actual child call. The finite alphabet and appended
basis workspace are shared by every block; original saved PCs are unchanged.
This identifies the complete table, not a reached recursive execution proof. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyAlignedActualTable
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexActualCallFullAlignment (tapes localTapes)
open CompactNativeRoleConjugatedPorts (encoding)
open Networks.ComplexRecursiveCallSchema (Call)
open CompactComplexCompletedLiveLower (Event schedule)
variable {s q : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites schedule CompactComplexRolePhaseSite.roleCount

/-- Existing arithmetic/control blocks retain their state counts, exact tape
indices and runtimes while sharing the basis alphabet and appended workspace. -/
def liftPair (M : Σ r,Program (CompactComplexSourceReadyScalarWorkspace.tapes s roles) r 2) :
    Σ r,Program (tapes s roles) r prime :=
  ⟨M.1,extend (Alphabet.program encoding M.2) (localTapes roles)⟩

/-- Alphabet lifting and the fixed workspace extension add no transitions;
the appended basis workspace is retained literally throughout old blocks. -/
theorem lift_runs {r B : ℕ}
    (M : Program (CompactComplexSourceReadyScalarWorkspace.tapes s roles) r 2)
    (v w : Tapes (CompactComplexSourceReadyScalarWorkspace.tapes s roles) 2)
    (suffix : Tapes (localTapes roles) prime)
    (h : HoareTime M (fun z => z=v) (fun z => z=w) B) :
    HoareTime (liftPair ⟨r,M⟩).2
      (fun z => z=(Alphabet.mapTapes encoding v).append suffix)
      (fun z => z=(Alphabet.mapTapes encoding w).append suffix) B := by
  have hm := Alphabet.map_hoare encoding h
  have he : HoareTime (Alphabet.program encoding M)
      (fun z => z=Alphabet.mapTapes encoding v)
      (fun z => z=Alphabet.mapTapes encoding w) B :=
    hm.consequence (fun _ hz => ⟨v,rfl,hz⟩)
      (by rintro _ ⟨original,rfl,rfl⟩;rfl) le_rfl
  exact hoare_extend_eq he suffix

def controls (pcStack : Fin s) : Fin 4 → Σ r,Program (tapes s roles) r prime :=
  fun tag => liftPair (CompactComplexSourceReadyCorrectedActualTable.controls pcStack tag)

def classify (pcStack : Fin s) : Fin (controls pcStack 0).1 → Bool :=
  CompactComplexSourceReadyCorrectedActualTable.classify pcStack

def scalar (g : CompactComplexScalarIntegerRows.GroupIndex) :
    Σ r,Program (tapes s roles) r prime :=
  liftPair (CompactComplexSourceReadyActualTable.scalar (s:=s) g)

def event (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) : Event → Σ r,Program (tapes s roles) r prime
  | .scalar g => scalar g
  | .child call => CompactComplexActualCallFullAlignment.child P headerStack pcStack liveStack call

def savedStackSlot (pcStack : Fin s) : Fin (tapes s roles) :=
  Fin.castAdd (localTapes roles) (CompactComplexSourceReadyCorrectedActualTable.savedStackSlot pcStack)

/-- The native stage program is one fixed finite witness for all runtime
geometries; depth remains tape data, and every child uses this same table. -/
def program (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) : Σ r,Program (tapes s roles) r prime :=
  ⟨_,CompactComplexFixedNodeTable.fixedProgram
    (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt) (savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (controls pcStack) (event P headerStack pcStack liveStack) (classify pcStack)⟩

/-- Literal table lookup includes the forward basis pass before real entry. -/
theorem table_child (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (i : Fin schedule.length) (call : Call)
    (hi : schedule.get i=Event.child call) :
    CompactComplexFixedNodeTable.tablePrograms
      (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt)
      (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
      (controls pcStack) (event P headerStack pcStack liveStack)
      (Fin.natAdd CompactComplexScheduledPCLayout.originalCount (Fin.natAdd 4 i))=
      CompactComplexActualCallFullAlignment.child P headerStack pcStack liveStack call := by
  rw [CompactComplexFixedNodeTable.table_event,hi]
  rfl

/-- The literal scalar block still uses the original scalar lifecycle. -/
theorem table_scalar (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (i : Fin schedule.length)
    (g : CompactComplexScalarIntegerRows.GroupIndex) (hi : schedule.get i=Event.scalar g) :
    CompactComplexFixedNodeTable.tablePrograms
      (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt)
      (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
      (controls pcStack) (event P headerStack pcStack liveStack)
      (Fin.natAdd CompactComplexScheduledPCLayout.originalCount (Fin.natAdd 4 i))=scalar g := by
  rw [CompactComplexFixedNodeTable.table_event,hi]
  rfl

/-- The original decoded return slot includes the reverse pass after real
parent restoration, with the original return address encoding retained. -/
theorem table_return (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (call : Call) :
    CompactComplexFixedNodeTable.tablePrograms
      (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt)
      (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
      (controls pcStack) (event P headerStack pcStack liveStack)
      (Fin.castAdd (4+schedule.length) (CompactComplexScheduledPCDecode.callAddress call))=
      CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack call :=
  CompactComplexFixedNodeTable.table_return _ _ _ _ call

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyAlignedActualTable
