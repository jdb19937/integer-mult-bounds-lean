import IntegerMultBounds.Machine.CompactComplexCorrectedStoppedRootBudget
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedEntryTablePath
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRootFinal
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinal
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedClassifierTablePath
import IntegerMultBounds.Machine.CompactComplexScheduleRuntimeBudget

/-! Complete corrected nonleaf boundary allowances charge classification,
source entry, sink corrections, contraction/rejoin, post-orientation and the
true root halt or saved-PC guard/pop. These are arithmetic budgets, not an
assertion that the interleaved recursive execution has been constructed. -/
namespace IntegerMultBounds.Machine.CompactComplexCorrectedNonleafBoundaryBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactComplexRolePhaseSite (roleCount)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexSourceReadyGuard (setupCost cleanupCost guardConstant)
open CompactComplexScheduleRuntimeBudget (scalarCoefficient groupCount eventAllowance)
variable {sh : Shape} {left e levels frames count : ℕ}
attribute [local irreducible] roleCount guardConstant
  CompactComplexSourceReadyOrientationInvariants.constant
  CompactComplexSourceReadyNonleafTargetSplit.constant
  NativeEndpointCharacterCanonicalRoles.constant NativeUniformPolynomialRotationRoles.constant
  CompactComplexEndpointRoleExchange.constant CompactComplexSourceReadyNonleafFinalPath.constant
  CompactComplexSourceReadyNonleafOrientedFinal.constant
  Networks.ComplexRank25.program Networks.ComplexRank25.rankSum
  Networks.ComplexRecursiveCallSchema.sites
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

def entryCost (V : ℕ) := CompactComplexSourceReadyNonleafTargetSplit.constant roleCount*V+1+
  NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*V+1

def sinkCost (V : ℕ) :=
  NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*V+1+
    (NativeUniformPolynomialRotationRoles.constant*V+1+
      (NativeUniformPolynomialRotationRoles.constant*V+1+CompactComplexEndpointRoleExchange.constant*V))

def rootFinalCost (V : ℕ) := sinkCost V+1+
  (CompactComplexSourceReadyNonleafFinalPath.constant roleCount*V+4)+1+2

def childFinalCost (V : ℕ) := sinkCost V+1+
  CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount*V+1+
  (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5)

private def rootExpression (_G S A B C D V setup cleanup : ℕ) :=
  (setup+cleanup+7+1)+(S*V+1+A*V+1)+
    ((A*V+1+(B*V+1+(B*V+1+C*V)))+1+(D*V+4)+1+2)
private def rootFactor (G S A B C D : ℕ) := (3*G+5)+(S+A+2)+(A+2*B+C+D+11)
private def childExpression (O G S A B C D W V : ℕ) :=
  ((O+4*G+1)*V+1)+(S*V+1+A*V+1)+
    ((A*V+1+(B*V+1+(B*V+1+C*V)))+1+D*V+1+(W+5))
private def childFactor (O G S A B C D W : ℕ) :=
  (O+4*G+2)+(S+A+2)+(A+2*B+C+D+W+10)

def rootCoefficient := rootFactor guardConstant
  (CompactComplexSourceReadyNonleafTargetSplit.constant roleCount)
  (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
  NativeUniformPolynomialRotationRoles.constant CompactComplexEndpointRoleExchange.constant
  (CompactComplexSourceReadyNonleafFinalPath.constant roleCount)

def childCoefficient := childFactor CompactComplexSourceReadyOrientationInvariants.constant guardConstant
  (CompactComplexSourceReadyNonleafTargetSplit.constant roleCount)
  (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
  NativeUniformPolynomialRotationRoles.constant CompactComplexEndpointRoleExchange.constant
  (CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount)
  (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3))

def rootCost (sh : Shape) (rows ell p exponent : ℕ) := rootExpression guardConstant
  (CompactComplexSourceReadyNonleafTargetSplit.constant roleCount)
  (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
  NativeUniformPolynomialRotationRoles.constant CompactComplexEndpointRoleExchange.constant
  (CompactComplexSourceReadyNonleafFinalPath.constant roleCount)
  (volume rows sh ell p) (setupCost sh.axes exponent) (cleanupCost sh.axes exponent)

def childCost (sh : Shape) (rows ell p : ℕ) := childExpression
  CompactComplexSourceReadyOrientationInvariants.constant guardConstant
  (CompactComplexSourceReadyNonleafTargetSplit.constant roleCount)
  (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
  NativeUniformPolynomialRotationRoles.constant CompactComplexEndpointRoleExchange.constant
  (CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount)
  (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3))
  (volume rows sh ell p)

/-- The budget is literally the checked root classifier and corrected
entry/final table costs, including the final two-transition empty guard. -/
theorem root_cost_eq (sh : Shape) (rows ell p exponent : ℕ) :
    rootCost sh rows ell p exponent=
      (setupCost sh.axes exponent+cleanupCost sh.axes exponent+7+1)+
      entryCost (volume rows sh ell p)+rootFinalCost (volume rows sh ell p) := rfl

/-- The child boundary pays the genuine complete saved-PC pop, after
corrected sink/contraction/rejoin and post-orientation. -/
theorem child_cost_eq (sh : Shape) (rows ell p : ℕ) :
    childCost sh rows ell p=
      ((CompactComplexSourceReadyOrientationInvariants.constant+4*guardConstant+1)*volume rows sh ell p+1)+
      entryCost (volume rows sh ell p)+childFinalCost (volume rows sh ell p) := rfl

private theorem root_algebra (G S A B C D V setup cleanup : ℕ)
    (hV : 0<V) (hg : setup+cleanup+3≤3*G*V) :
    rootExpression G S A B C D V setup cleanup≤rootFactor G S A B C D*V := by
  unfold rootExpression rootFactor
  nlinarith only [hV,hg]

private theorem child_algebra (O G S A B C D W V : ℕ) (hV : 0<V) :
    childExpression O G S A B C D W V≤childFactor O G S A B C D W*V := by
  have hw := Nat.le_mul_of_pos_right W hV
  unfold childExpression childFactor
  nlinarith only [hV,hw]

/-- A genuine Path pays the root's classifier, corrected source/sink blocks,
all metadata/contraction/rejoin, table joins and final empty-stack halt. -/
theorem root_linear (rows ell p : ℕ) (rho : Fin sh.chunk)
    (path : Path sh.active left e levels frames count) (hr : 0<rows) (hG : 0<sh.guard) :
    rootCost sh rows ell p e≤rootCoefficient*volume rows sh ell p := by
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hg := CompactComplexCorrectedStoppedRootBudget.classifier_native rows ell p rho path.visit hr hG
  have h := root_algebra guardConstant (CompactComplexSourceReadyNonleafTargetSplit.constant roleCount)
    (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
    NativeUniformPolynomialRotationRoles.constant CompactComplexEndpointRoleExchange.constant
    (CompactComplexSourceReadyNonleafFinalPath.constant roleCount)
    (volume rows sh ell p) (setupCost sh.axes e) (cleanupCost sh.axes e) hV hg
  exact h

/-- The actual child's oriented classifier and corrected final table path
include the original saved-PC width and its complete guarded pop. -/
theorem child_linear (rows ell p : ℕ) (hr : 0<rows) :
    childCost sh rows ell p≤childCoefficient*volume rows sh ell p := by
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have h := child_algebra CompactComplexSourceReadyOrientationInvariants.constant guardConstant
    (CompactComplexSourceReadyNonleafTargetSplit.constant roleCount)
    (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
    NativeUniformPolynomialRotationRoles.constant CompactComplexEndpointRoleExchange.constant
    (CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount)
    (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3))
    (volume rows sh ell p) hV
  exact h

/-- The child classifier's private precision parameter gives precisely the
original retained raw precision when its natural reservation is respected. -/
theorem classifier_precision (p : ℕ) (hp : 2*sh.bits≤p) :
    ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)=p := by
  unfold ButterflyIndependentGuardHeaders.reservation
  omega

private theorem sum_bound (boundary localCost V recursive actualBoundary actualEvents : ℕ)
    (hb : actualBoundary≤boundary*V) (he : actualEvents≤localCost*V+recursive) :
    actualBoundary+actualEvents≤(boundary+localCost)*V+recursive := by
  nlinarith only [hb,he]

/-- Root boundaries plus every genuine static event allowance fit the full
local-plus-children recurrence shape; no desired sum bound is supplied. -/
theorem root_schedule_bound (rows ell p leaf depth : ℕ) (localCost : ℕ → ℕ)
    (rho : Fin sh.chunk) (path : Path sh.active left e levels frames count)
    (hr : 0<rows) (hG : 0<sh.guard) :
    rootCost sh rows ell p e+
      (CompactComplexCompletedLiveLower.schedule.map (eventAllowance sh rows ell p leaf depth localCost)).sum≤
      (rootCoefficient+(scalarCoefficient+groupCount+
        Networks.ComplexRank25.rankSum*CompactComplexScheduleRuntimeBudget.childCoefficient))*volume rows sh ell p+
      Networks.ComplexRank25.rankSum*CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
        (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles) := by
  have hb := root_linear rows ell p rho path hr hG
  have he := CompactComplexScheduleRuntimeBudget.schedule_bound sh rows ell p leaf depth localCost hr
  have h := sum_bound rootCoefficient
    (scalarCoefficient+groupCount+Networks.ComplexRank25.rankSum*CompactComplexScheduleRuntimeBudget.childCoefficient)
    (volume rows sh ell p)
    (Networks.ComplexRank25.rankSum*CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
      (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles)) _ _ hb he
  exact h

/-- The same actual event allowance includes child pre/post orientation and
the saved-PC guard/pop in its complete nonleaf local coefficient. -/
theorem child_schedule_bound (rows ell p leaf depth : ℕ) (localCost : ℕ → ℕ) (hr : 0<rows) :
    childCost sh rows ell p+
      (CompactComplexCompletedLiveLower.schedule.map (eventAllowance sh rows ell p leaf depth localCost)).sum≤
      (childCoefficient+(scalarCoefficient+groupCount+
        Networks.ComplexRank25.rankSum*CompactComplexScheduleRuntimeBudget.childCoefficient))*volume rows sh ell p+
      Networks.ComplexRank25.rankSum*CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
        (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles) := by
  have hb := child_linear (sh:=sh) rows ell p hr
  have he := CompactComplexScheduleRuntimeBudget.schedule_bound sh rows ell p leaf depth localCost hr
  have h := sum_bound childCoefficient
    (scalarCoefficient+groupCount+Networks.ComplexRank25.rankSum*CompactComplexScheduleRuntimeBudget.childCoefficient)
    (volume rows sh ell p)
    (Networks.ComplexRank25.rankSum*CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
      (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles)) _ _ hb he
  exact h

private theorem choose_bound (root child localFactor V recursive rootCost childCost events : ℕ)
    (hr : rootCost≤root*V) (hc : childCost≤child*V)
    (he : events≤localFactor*V+recursive) (isRoot : Bool) :
    (if isRoot then rootCost else childCost)+events≤(root+child+localFactor)*V+recursive := by
  cases isRoot <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals nlinarith only [hr,hc,he,Nat.zero_le (root*V),Nat.zero_le (child*V)]

/-- One fixed full-local coefficient works at the root and every corrected
child node, leaving only the original recursive child budgets separate. -/
theorem boundary_schedule_bound (rows ell p leaf depth : ℕ) (localCost : ℕ → ℕ)
    (rho : Fin sh.chunk) (path : Path sh.active left e levels frames count)
    (hr : 0<rows) (hG : 0<sh.guard) (isRoot : Bool) :
    (if isRoot then rootCost sh rows ell p e else childCost sh rows ell p)+
      (CompactComplexCompletedLiveLower.schedule.map (eventAllowance sh rows ell p leaf depth localCost)).sum≤
      (rootCoefficient+childCoefficient+(scalarCoefficient+groupCount+
        Networks.ComplexRank25.rankSum*CompactComplexScheduleRuntimeBudget.childCoefficient))*volume rows sh ell p+
      Networks.ComplexRank25.rankSum*CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
        (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles) := by
  exact choose_bound rootCoefficient childCoefficient
    (scalarCoefficient+groupCount+Networks.ComplexRank25.rankSum*CompactComplexScheduleRuntimeBudget.childCoefficient)
    (volume rows sh ell p)
    (Networks.ComplexRank25.rankSum*CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
      (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles)) _ _ _
    (root_linear rows ell p rho path hr hG) (child_linear (sh:=sh) rows ell p hr)
    (CompactComplexScheduleRuntimeBudget.schedule_bound sh rows ell p leaf depth localCost hr) isRoot

end
end IntegerMultBounds.Machine.CompactComplexCorrectedNonleafBoundaryBudget
