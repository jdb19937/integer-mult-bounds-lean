module

public import IntegerMultBounds.Machine.CompactComplexRecursiveStageScaleBudget

/-! Runtime invariants on the actual statically chosen recursive-provider
budgets. The recurrence retains the real stopping branch, original call
multiplicity, physical boundary coefficient and per-depth local allowance. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexActualProviderRuntime
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactRecursiveDependencyBudget (Path)
open CompactGlobalRowPadding (rowsAt)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.RecursiveInduction
  (BudgetInvariant PackingFamily SuccessorBudgetInvariant UniformProvider)
attribute [local irreducible] ComplexRank25.program ComplexRank25.rankSum
  ComplexRecursiveCallSchema.sites ComplexRecursiveCallSchema.calls
  CompactComplexRolePhaseSite.roleCount CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

def localCoefficient (shape : Shape) (basisConstant : ℝ) (childExponent : ℕ) : ℝ :=
  (CompactComplexScheduleRuntimeBudget.scalarCoefficient+CompactComplexScheduleRuntimeBudget.groupCount+
    ComplexRank25.rankSum*CompactComplexSourceReadyActualScheduleBudget.childLocalCoefficient shape childExponent : ℕ)+
  6*(ComplexRank25.rankSum : ℝ)*basisConstant*(shape.guard : ℝ)^Parameters.tau*
    ((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.tau

/-- Child execution is charged only when the original classifier actually
recurses. All original nonleaf boundary and local physical work is paid. -/
def pathCoefficient (shape : Shape) (basisConstant : ℝ) : ℕ → ℝ
  | 0 => 0
  | childExponent+1 =>
    (CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient : ℝ)+localCoefficient shape basisConstant childExponent+
    if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
      (ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent

theorem path_coefficient_nonnegative (shape : Shape) (basisConstant : ℝ) (constantNonnegative : 0≤basisConstant)
    (childExponent : ℕ) : 0≤pathCoefficient shape basisConstant childExponent := by
  induction childExponent with
  | zero => exact le_rfl
  | succ childExponent inductionHypothesis =>
    unfold pathCoefficient localCoefficient
    split_ifs <;> positivity

/-- A budget invariant on static geometry alone; runtime banks, live
denominators and saved-call histories cannot occur in this predicate. -/
def RuntimeInvariant (shape : Shape) (ell precision : ℕ) (basisConstant : ℝ) : BudgetInvariant shape :=
  fun {_nodeLeft childExponent _levels _frames _returned rows} _path _rowsPadded _eventBudget pathBudget =>
    ∀ call,(pathBudget call : ℝ)≤pathCoefficient shape basisConstant childExponent*
      (volume (rows/roles) shape ell precision : ℝ)

private theorem nat_sum_real_le {α : Type*} (entries : List α) (cost : α → ℕ) (bound : ℝ)
    (entryBounds : ∀ entry ∈ entries,(cost entry : ℝ)≤bound) :
    ((entries.map cost).sum : ℝ)≤(entries.length : ℝ)*bound := by
  induction entries with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.cast_zero,zero_mul,le_refl]
  | cons entry entries inductionHypothesis =>
    have headBound := entryBounds entry (List.mem_cons_self ..)
    have tailBound := inductionHypothesis (fun tailEntry member => entryBounds tailEntry (List.mem_cons_of_mem _ member))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [headBound,tailBound]

private theorem real_child_volume (shape : Shape) (rows ell precision : ℕ) (rolesDivideRows : roles∣rows) :
    (volume (rows/roles) shape ell precision : ℝ)=(volume rows shape ell precision : ℝ)/(roles : ℝ) := by
  have rolesPositive : 0<roles := by unfold roles CompactComplexRolePhaseSite.roleCount; positivity
  have volumeEquation : volume (rows/roles) shape ell precision*roles=volume rows shape ell precision := by
    unfold volume
    rw [Nat.mul_right_comm,Nat.div_mul_cancel rolesDivideRows]
  apply (eq_div_iff (show (roles : ℝ)≠0 from by exact_mod_cast rolesPositive.ne')).2
  exact_mod_cast volumeEquation

section Node
variable {shape : Shape} {nodeLeft childExponent levels frames returned rows ell precision : ℕ}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : Path shape.active nodeLeft (childExponent+2) levels frames returned)
  (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
  (packingLimit : ℕ) (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
  (childRowsPositive : 0<rows/roles)
  (stageSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
  (stagePacked : ∀ operation,1<(parent phaseCoordinate entryPath.visit activeFits pair).f →
    ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rows/roles) ell precision guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)

/-- The exact actual schedule obeys the real successor recurrence. Every
nonstopped call occurrence is charged once at the genuine role-volume quotient. -/
theorem schedule_coefficient_bound (basisConstant : ℝ)
    (childPathBudget : ComplexRecursiveCallSchema.Call → ℕ) (rolesDivideRows : roles∣rows)
    (localBound : (CompactComplexSourceReadyActualScheduleBudget.localBudget phaseCoordinate entryPath activeFits pair
      packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked : ℝ)≤
      localCoefficient shape basisConstant childExponent*(volume rows shape ell precision : ℝ))
    (childBounds : ∀ call,(childPathBudget call : ℝ)≤pathCoefficient shape basisConstant childExponent*
      (volume (rows/roles) shape ell precision : ℝ)) :
    (CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
      packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked : ℝ)≤
    (localCoefficient shape basisConstant childExponent+
      if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
        (ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent)*
      (volume rows shape ell precision : ℝ) := by
  have childSumBound := nat_sum_real_le ComplexRecursiveCallSchema.calls childPathBudget
    (pathCoefficient shape basisConstant childExponent*(volume (rows/roles) shape ell precision : ℝ))
    (fun call _ => childBounds call)
  rw [ComplexRecursiveCallSchema.calls_rankSum,real_child_volume shape rows ell precision rolesDivideRows] at childSumBound
  have actualTotal := CompactComplexSourceReadyActualScheduleBudget.total_eq phaseCoordinate entryPath activeFits pair
    packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked childPathBudget
  rw [actualTotal,Nat.cast_add]
  split_ifs with childrenStopped
  · simpa only [Nat.cast_zero,add_zero] using localBound
  · have bound := add_le_add localBound childSumBound
    exact bound.trans_eq (by ring)

/-- The actual completed-child path, not merely its schedule, pays the
fixed corrected boundary and inherits the same successor coefficient. -/
theorem child_path_coefficient_bound (basisConstant : ℝ)
    (childPathBudget : ComplexRecursiveCallSchema.Call → ℕ) (rowsPositive : 0<rows) (rolesDivideRows : roles∣rows)
    (localBound : (CompactComplexSourceReadyActualScheduleBudget.localBudget phaseCoordinate entryPath activeFits pair
      packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked : ℝ)≤
      localCoefficient shape basisConstant childExponent*(volume rows shape ell precision : ℝ))
    (childBounds : ∀ call,(childPathBudget call : ℝ)≤pathCoefficient shape basisConstant childExponent*
      (volume (rows/roles) shape ell precision : ℝ)) :
    (CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.pathBudget shape rows ell precision
      (CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
        packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked) : ℝ)≤
    pathCoefficient shape basisConstant (childExponent+1)*(volume rows shape ell precision : ℝ) := by
  have scheduleBound := schedule_coefficient_bound phaseCoordinate entryPath activeFits pair packingLimit
    guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked basisConstant childPathBudget rolesDivideRows localBound childBounds
  have boundaryBound := CompactComplexRecursiveStageScaleBudget.child_path_budget_le shape rows ell precision
    (CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget phaseCoordinate entryPath activeFits pair
      packingLimit childPathBudget guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked) rowsPositive
  have boundaryReal := Nat.cast_le (α:=ℝ).mpr boundaryBound
  rw [Nat.cast_add,Nat.cast_mul] at boundaryReal
  unfold pathCoefficient
  exact boundaryReal.trans (by nlinarith only [scheduleBound])

end Node

/-- The certified machine coefficient is selected once from the physical
basis theorem, before all shapes, node exponents, banks and stack histories. -/
def uniformBasisConstant (packingLimit : ℕ) : ℝ :=
  Classical.choose (CompactComplexRecursiveStageScaleBudget.exists_local_depth_bound packingLimit)

theorem uniform_basis_constant_positive (packingLimit : ℕ) : 0<uniformBasisConstant packingLimit :=
  (Classical.choose_spec (CompactComplexRecursiveStageScaleBudget.exists_local_depth_bound packingLimit)).1

section Static
variable {shape : Shape}
  (phaseCoordinate : Fin shape.chunk) (activeFits : shape.active≤shape.axes)
  (pair : BinaryRowProgram.Op (Fin arity)) (ell inputPrecision packingLimit : ℕ)
  (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
  (chunkPositive : 0<shape.chunk)
  (packingFamily : PackingFamily phaseCoordinate activeFits pair ell inputPrecision packingLimit guardPositive guardFitsChunk)

/-- The previously proved per-depth local estimate, restricted to genuine
descendants and the inherited static packing family. It contains no dynamic
execution assumption or complete recursive-time bound. -/
def LocalBounds (basisConstant : ℝ) : Prop :=
  ∀ {nodeLeft childExponent levels frames returned rows : ℕ}
    (entryPath : Path shape.active nodeLeft (childExponent+2) levels frames returned)
    (rowsPadded : rows=rowsAt roles arity shape.axes shape.chunk levels),
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsPositive : 0<rows/roles := by rw [rowsPadded]; exact rowGuards.2.2.2.1
    let stageSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3 := rfl
    let stagePacked := packingFamily entryPath rows rowsPadded childRowsPositive
    (CompactComplexSourceReadyActualScheduleBudget.localBudget phaseCoordinate entryPath activeFits pair
      packingLimit guardPositive guardFitsChunk childRowsPositive stageSlots stagePacked : ℝ)≤
    localCoefficient shape basisConstant childExponent*
      (volume rows shape ell (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) : ℝ)

/-- The actual completed-child constructor closes the runtime invariant
under the exact budget choices used by the original exponent induction. -/
theorem successor_runtime_invariant (basisConstant : ℝ)
    (localBounds : LocalBounds phaseCoordinate activeFits pair ell inputPrecision packingLimit
      guardPositive guardFitsChunk chunkPositive packingFamily basisConstant) :
    SuccessorBudgetInvariant phaseCoordinate activeFits pair ell inputPrecision packingLimit guardPositive guardFitsChunk
      chunkPositive packingFamily
      (RuntimeInvariant shape ell (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) basisConstant) := by
  unfold SuccessorBudgetInvariant
  intro nodeLeft smallerExponent levels frames returned rows entryPath rowsPadded smallerEventBudget smallerPathBudget
  dsimp only
  intro smallerBounds
  unfold RuntimeInvariant
  intro call
  have rolesPositive : 0<roles := by unfold roles CompactComplexRolePhaseSite.roleCount; positivity
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
    rolesPositive chunkPositive (by omega)
  have childRowsPadded : rows/roles=rowsAt roles arity shape.axes shape.chunk (levels+1) := by
    rw [rowsPadded]
    exact rowGuards.2.2.2.2.2.1
  have childRowsPositive : 0<rows/roles := by rw [rowsPadded]; exact rowGuards.2.2.2.1
  have childRolesDivideRows : roles∣rows/roles := by rw [rowsPadded]; exact rowGuards.2.2.1
  have grandchildRowsPositive : 0<(rows/roles)/roles := by rw [rowsPadded]; exact rowGuards.2.2.2.2.1
  let childSlots : (parent phaseCoordinate (Path.child entryPath call).visit activeFits pair).slots=25^3 := rfl
  let childPacked := packingFamily (Path.child entryPath call) (rows/roles) childRowsPadded grandchildRowsPositive
  have localPaid := localBounds (Path.child entryPath call) childRowsPadded
  exact child_path_coefficient_bound phaseCoordinate (Path.child entryPath call) activeFits pair packingLimit
    guardPositive guardFitsChunk grandchildRowsPositive childSlots childPacked basisConstant (smallerPathBudget call)
    childRowsPositive childRolesDivideRows localPaid (smallerBounds call)

variable {stackCount basisStateCount : ℕ}
  (baselinePrecision growthConstant baselineLive : ℕ)
  (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount Shared50ModularControl.prime)
  (headerStack pcStack liveStack : Fin stackCount)

/-- Genuine providers exist at every depth with the proved runtime invariant
on the very same static event/path budgets. The machine coefficient precedes
all dynamic entry banks and stack histories; local bounds are derived from
the checked physical machine, not supplied as execution or runtime oracles. -/
theorem exists_runtime_provider
    (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (largeAxes : arity^1000 < shape.axes) (activePositive : 0 < shape.active)
    (axesPositive : 0 < shape.axes) (chunkPositive : 0 < shape.chunk) (unitPayload : shape.payload=1)
    (packingFamily : PackingFamily phaseCoordinate activeFits pair ell inputPrecision packingLimit
      guardPositive guardFitsChunk)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+guardBits ≤ shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits ≤ shape.chunk)
    (precisionReserve : baselinePrecision+2*shape.bits ≤ ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
    (baselineFits : baselineLive ≤ baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant ≤ growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows ≤ shape.chunk) :
    ∃ runtimeConstant : ℝ,0<runtimeConstant ∧ runtimeConstant=uniformBasisConstant packingLimit ∧
    LocalBounds phaseCoordinate activeFits pair ell inputPrecision packingLimit guardPositive guardFitsChunk
      chunkPositive packingFamily runtimeConstant ∧
    ∀ (childExponent : ℕ)
    {nodeLeft dependencyLevels frameVolume returnedVolume rowCount : ℕ}
    (path : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume returnedVolume)
    (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels),
    let rowGuards := CompactComplexRecursivePathRows.recursive_row_guards path activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    let childRowsDivisible : roles ∣ rowCount/roles := by
      rw [rowsPadded]
      exact rowGuards.2.2.1
    ∃ eventBudget pathBudget : ComplexRecursiveCallSchema.Call → ℕ,
      UniformProvider phaseCoordinate activeFits pair ell inputPrecision baselinePrecision growthConstant
        baselineLive basisProgram headerStack pcStack liveStack path childRowsDivisible eventBudget pathBudget ∧
      RuntimeInvariant shape ell (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
        runtimeConstant path rowsPadded eventBudget pathBudget := by
  let runtimeConstant := uniformBasisConstant packingLimit
  have constantPositive := uniform_basis_constant_positive packingLimit
  have localBounds : LocalBounds phaseCoordinate activeFits pair ell inputPrecision packingLimit
      guardPositive guardFitsChunk chunkPositive packingFamily runtimeConstant := by
    intro nodeLeft descendantExponent levels frames returned rows entryPath descendantRowsPadded
    dsimp only
    have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
      (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
    have rowsPositive : 0<rows := by rw [descendantRowsPadded]; exact rowGuards.2.1
    have childRowsPositive : 0<rows/roles := by rw [descendantRowsPadded]; exact rowGuards.2.2.2.1
    have rolesDivideRows : roles∣rows := by rw [descendantRowsPadded]; exact rowGuards.1
    exact (Classical.choose_spec (CompactComplexRecursiveStageScaleBudget.exists_local_depth_bound packingLimit)).2
      phaseCoordinate entryPath activeFits pair guardPositive guardFitsChunk rowsPositive childRowsPositive
      rolesDivideRows unitPayload rfl (packingFamily entryPath rows descendantRowsPadded childRowsPositive)
  let invariant : BudgetInvariant shape :=
    RuntimeInvariant shape ell (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) runtimeConstant
  have baseInvariant : ∀ {nodeLeft levels frames returned rows : ℕ}
      (entryPath : Path shape.active nodeLeft (0+2) levels frames returned)
      (descendantRowsPadded : rows=rowsAt roles arity shape.axes shape.chunk levels),
      invariant entryPath descendantRowsPadded (fun _ => 0) (fun _ => 0) := by
    intro nodeLeft levels frames returned rows entryPath descendantRowsPadded call
    simp only [pathCoefficient,Nat.cast_zero,zero_mul,le_refl]
  have successorInvariant : SuccessorBudgetInvariant phaseCoordinate activeFits pair ell inputPrecision packingLimit
      guardPositive guardFitsChunk chunkPositive packingFamily invariant :=
    successor_runtime_invariant phaseCoordinate activeFits pair ell inputPrecision packingLimit
      guardPositive guardFitsChunk chunkPositive packingFamily runtimeConstant localBounds
  refine ⟨runtimeConstant,constantPositive,rfl,localBounds,?_⟩
  intro childExponent nodeLeft dependencyLevels frameVolume returnedVolume rowCount path rowsPadded
  dsimp only
  obtain ⟨eventBudget,pathBudget,provider,runtimeCertificate⟩ :=
    CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.RecursiveInduction.exists_fixed_provider_with_budget_invariant
      phaseCoordinate activeFits pair ell inputPrecision baselinePrecision growthConstant baselineLive packingLimit
      guardPositive guardFitsChunk basisProgram headerStack pcStack liveStack basisConstant basisRuns
      largeAxes activePositive axesPositive chunkPositive unitPayload packingFamily childChunkRoom scalarChunkRoom
      precisionReserve baselineFits growthReserve denominatorRoom invariant baseInvariant successorInvariant childExponent path rowsPadded
  exact ⟨eventBudget,pathBudget,provider,runtimeCertificate⟩

end Static
end
end IntegerMultBounds.Machine.CompactComplexActualProviderRuntime
