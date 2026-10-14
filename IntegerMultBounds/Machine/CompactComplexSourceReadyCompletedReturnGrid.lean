module

public import IntegerMultBounds.Machine.CompactComplexAlignedCompletedReturnReadiness
public import IntegerMultBounds.Machine.CompactComplexCorrectedChildGridSemantics
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedReturnInvariant
public import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedStoppedReturnPrefix

/-! The recursive semantic result, rather than the child's internal numerical
budget, supplies the parent's returned grid. This retains the parent's actual
scalar prefix and charges the genuine child volume. The semantic equality is
an induction obligation about decoded arrays; it is not an execution callback. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedReturnGrid
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Grid decoded)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyReachedReturnInvariant (roleData)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  Networks.ComplexRank25.program CompactComplexCompletedLiveLower.schedule

section Parent
variable {stage : Stage sh} {rows ell precision e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell precision e p C axes baseline levels frames returned pref n pcStack origin calls v)

include h in
/-- Genuine parent and child readiness supply both upper ledgers and the
actual scalar row counts of return accounting. Coverage of the chosen return
target by the child's actual live denominator remains a recursive obligation. -/
def computed_progress {left childLeft gap : ℕ}
    (parentPath : CompactRecursiveDependencyBudget.Path sh.active left e levels frames returned)
    {childStage : Stage sh} {ce cp cC caxes cbaseline clevels cframes creturned cpref cn : ℕ}
    {childCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {cv : Tapes (nodeTapes s roles) 2}
    (hc : Reached childStage (rows/roles) ell precision ce cp cC caxes cbaseline
      clevels cframes creturned cpref cn pcStack origin childCalls cv)
    (childPath : CompactRecursiveDependencyBudget.Path sh.active childLeft ce clevels cframes creturned)
    (hbaseline : cbaseline=baseline) (hmetadata : 2*sh.bits≤precision)
    (hbase : baseline≤precision-2*sh.bits)
    (hroom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤sh.chunk)
    (hgap : gap≤2*arity^e) (hcompleted : n+gap≤cn) :
    CompactComplexChildAlignmentBudget.Progress sh precision n cn (n+gap) := by
  refine {
    R := CompactComplexDenominatorCapacity.scalarRows
    baseline := baseline
    parentLeft := left
    parentExponent := e
    parentLevels := levels
    parentFrames := frames
    parentReturned := returned
    parentUsed := (CompactFramedScalarGrid.rows pref).length
    childLeft := childLeft
    childExponent := ce
    childLevels := clevels
    childFrames := cframes
    childReturned := creturned
    childUsed := (CompactFramedScalarGrid.rows cpref).length
    parentPath := parentPath
    childPath := childPath
    metadata := hmetadata
    base := hbase
    room := hroom
    parentUsed_le := CompactComplexDenominatorCapacity.actual_prefix pref
    childUsed_le := CompactComplexDenominatorCapacity.actual_prefix cpref
    before_live := h.upper_ledger
    completed_live := ?_
    target_growth := by omega
    promote := by omega
    contract := hcompleted }
  simpa only [hbaseline] using hc.upper_ledger

/-- A corrected recursive tensor equality yields the exact selected-child grid
required by the completed return. No child-level scalar or frame overhead is
carried back into the parent budget. -/
theorem selected_grid {left k : ℕ} (call : Networks.ComplexRecursiveCallSchema.Call)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (hdiv : CompactComplexNonleafChildAddress.roles∣rows/roles)
    (hmetadata : 2*sh.bits≤precision) (result : Array sh (rows/roles) ell)
    (hsem : ∀ i,decoded sh (rows/roles) ell (precision-2*sh.bits)
      (n+2*arity^(k+1)) result i=
      CompactComplexCorrectedChildGridSemantics.tensor call
        (fun wire address => decoded sh (rows/roles) ell (precision-2*sh.bits) n
          (roleData h (CompactComplexRolePhaseSite.role call.site))
          (CompactComplexNonleafChildAddress.inputIndex sh (rows/roles) ell hdiv rho visit i wire address))
        (CompactComplexNonleafChildAddress.outputWire sh (rows/roles) ell hdiv i)
        (CompactComplexNonleafChildAddress.outputAddress sh (rows/roles) ell hdiv rho visit i)) :
    Grid sh (rows/roles) ell (precision-2*sh.bits) (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+arity^(k+1))+axes))) result := by
  have hg := CompactComplexCorrectedChildGridSemantics.corrected_selected_grid
    sh (rows/roles) ell (precision-2*sh.bits) n
    (CompactFramedScalarGrid.bound pref
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
    hdiv rho visit call (roleData h (CompactComplexRolePhaseSite.role call.site)) result
    (CompactComplexSourceReadyReachedReturnInvariant.role_grid h hmetadata _) hsem
  rw [CompactComplexNonleafEventProgress.prefix_bound] at hg
  exact hg

/-- The adapter applies to the literal computed, contracted, rejoined and
oriented child result. Its sole semantic premise is the recursive tensor
correctness equality for that result. The child's private prefix and ledger
parameters are deliberately unrestricted. -/
theorem computed_grid {left k : ℕ} (call : Networks.ComplexRecursiveCallSchema.Call)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (hdiv : CompactComplexNonleafChildAddress.roles∣rows/roles)
    (hmetadata : 2*sh.bits≤precision)
    {childStage : Stage sh} {ce cp cC caxes cbaseline clevels cframes creturned cpref cn : ℕ}
    {cv : Tapes (nodeTapes s roles) 2}
    (hc : Reached childStage (rows/roles) ell precision ce cp cC caxes cbaseline
      clevels cframes creturned cpref cn pcStack origin (call::calls) cv)
    (hslots : childStage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows/roles)
    (hsem : ∀ i,decoded sh (rows/roles) ell (precision-2*sh.bits)
      (n+2*arity^(k+1)) (CompactComplexSourceReadyCompletedChildBoundary.result hc hslots hd call) i=
      CompactComplexCorrectedChildGridSemantics.tensor call
        (fun wire address => decoded sh (rows/roles) ell (precision-2*sh.bits) n
          (roleData h (CompactComplexRolePhaseSite.role call.site))
          (CompactComplexNonleafChildAddress.inputIndex sh (rows/roles) ell hdiv rho visit i wire address))
        (CompactComplexNonleafChildAddress.outputWire sh (rows/roles) ell hdiv i)
        (CompactComplexNonleafChildAddress.outputAddress sh (rows/roles) ell hdiv rho visit i)) :
    Grid sh (rows/roles) ell (precision-2*sh.bits) (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+arity^(k+1))+axes)))
      (CompactComplexSourceReadyCompletedChildBoundary.result hc hslots hd call) :=
  selected_grid h call rho visit hdiv hmetadata _ hsem

/-- A stopped child uses its actual leaf result and one-volume denominator
advance. Original parent dependency guards justify both literal conjugations;
the output grid is charged at the same two-volume numerator reservation as a
recursive return. -/
theorem stopped_grid {left childLeft k : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left e levels frames returned)
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (rho : Fin sh.chunk) (visit : Visit sh.active childLeft (k+1))
    (result : Array sh (rows/roles) ell)
    (hresult : result=CompactComplexSourceReadyOrientationInvariants.oriented call
      (CompactSpectatorLeafGuardOriginal.result .forward sh (rows/roles) ell
        (precision-2*sh.bits) rho visit
        (CompactComplexSourceReadyOrientationInvariants.oriented call
          (roleData h (CompactComplexRolePhaseSite.role call.site)))))
    (ha : 0<sh.active) (hp : p+2*sh.bits≤precision)
    (haxes : axes+arity^(k+1)≤sh.bits) (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤sh.chunk) :
    Grid sh (rows/roles) ell (precision-2*sh.bits) (n+arity^(k+1))
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+arity^(k+1))+axes))) result := by
  let q := precision-2*sh.bits
  let gap := arity^(k+1)
  let M := CompactFramedScalarGrid.bound pref
    (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))
  let before := roleData h (CompactComplexRolePhaseSite.role call.site)
  let input := CompactComplexSourceReadyOrientationInvariants.oriented call before
  let leaf := CompactSpectatorLeafGuardOriginal.result .forward sh (rows/roles) ell q rho visit input
  have hmetadata : 2*sh.bits≤precision := by omega
  have hw := CompactComplexSourceReadyReachedReturnInvariant.role_width h hmetadata
    (CompactComplexRolePhaseSite.role call.site)
  have hg := CompactComplexSourceReadyReachedReturnInvariant.role_grid h hmetadata
    (CompactComplexRolePhaseSite.role call.site)
  have hguard := CompactComplexStoppedEventProgress.prefix_guard_from_path path
    pref p C axes gap precision ha hp haxes hC hroom
  change 4*(M*4^gap)<2^(CompactSpectatorInheritedGrid.half sh q) at hguard
  have hM : M≤M*4^gap := Nat.le_mul_of_pos_right M (pow_pos (by decide) gap)
  have hi := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid
    call sh (rows/roles) ell q n M before hw hg (by omega)
  have hiw := CompactComplexSourceReadyOrientationInvariants.oriented_width call sh (rows/roles) ell q before hw
  have hleaf : Grid sh (rows/roles) ell q (n+gap) (M*4^gap) leaf :=
    CompactSpectatorInheritedGrid.forward_grid sh (rows/roles) ell q rho visit gap n M
      le_rfl input hiw hi.1 hguard
  have hlw : CompactSpectatorInheritedGrid.Width sh (rows/roles) ell q leaf :=
    CompactSpectatorLeafLoop.width_run sh (rows/roles) ell
      (ButterflyIndependentGuardHeaders.reservation sh.bits q) rho visit gap input hiw
  have hout := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid
    call sh (rows/roles) ell q (n+gap) (M*4^gap) leaf hlw hleaf (by omega)
  rw [hresult]
  intro i
  exact Networks.GaussianPrecision.bound_mono
    (CompactComplexStoppedEventProgress.prefix_return_bound pref p C levels frames returned axes gap)
    (hout.1 i)

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedReturnGrid
