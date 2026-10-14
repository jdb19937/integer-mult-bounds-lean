module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyRecursiveRootExecution
public import IntegerMultBounds.Machine.CompactComplexRecursiveRuntimeSum

/-! Geometric summation of the actual provider recurrence above the original
stopping cutoff. All forcing coefficients come from paid physical local work;
the exact cutoff coefficient is retained separately. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexActualProviderRuntimeSum
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexActualProviderRuntime (pathCoefficient localCoefficient)
attribute [local irreducible] ComplexRank25.program ComplexRank25.rankSum
  ComplexRecursiveCallSchema.sites CompactComplexRolePhaseSite.roleCount
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth
  CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient
  CompactComplexNonleafRolePreparationBudget.constant CompactComplexSourceReadyChildReturnPath.timeConstant

/-- Symbolic fixed-work sum, preventing expansion of physical coefficients. -/
def fixedFactor (boundary scalar groups calls entry restoration : ℕ) :=
  boundary+(scalar+groups+calls*(entry+restoration+4))

/-- Complete nonstopped physical boundary and fixed local work. -/
def fixedCoefficient : ℕ := fixedFactor
  CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient
  CompactComplexScheduleRuntimeBudget.scalarCoefficient CompactComplexScheduleRuntimeBudget.groupCount
  ComplexRank25.rankSum
  (CompactComplexNonleafRolePreparationBudget.constant roles ComplexRecursiveCallSchema.sites.length)
  (CompactComplexSourceReadyChildReturnPath.timeConstant roles)

/-- One depth-independent forcing coefficient, with the original guard power. -/
def forcingCoefficient (shape : Shape) (basisConstant : ℝ) : ℝ :=
  fixedCoefficient+6*(ComplexRank25.rankSum : ℝ)*basisConstant*(shape.guard : ℝ)^Parameters.tau

theorem forcing_nonnegative (shape : Shape) (basisConstant : ℝ) (constantNonnegative : 0≤basisConstant) :
    0≤forcingCoefficient shape basisConstant := by
  exact add_nonneg (Nat.cast_nonneg _)
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤6) (Nat.cast_nonneg _)) constantNonnegative)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

private theorem absorb_fixed (fixed basis width recursive : ℝ)
    (fixedNonnegative : 0≤fixed) (widthAtLeastOne : 1≤width) :
    fixed+basis*width+recursive≤recursive+(fixed+basis)*width := by
  have fixedBound := mul_le_mul_of_nonneg_left widthAtLeastOne fixedNonnegative
  nlinarith only [fixedBound]

private theorem stopped_local_algebra (entry restoration stoppedCost : ℕ) (stopped : Bool)
    (nonstopped : stopped=false) :
    entry+restoration+4+(if stopped then stoppedCost else 0)=entry+restoration+4 := by
  rw [nonstopped]
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero]

private theorem coefficient_algebra (boundary scalar groups calls entry restoration childConstant : ℕ)
    (basis width : ℝ) (childConstantEq : childConstant=entry+restoration+4) :
    (boundary : ℝ)+(((scalar+groups+calls*childConstant : ℕ) : ℝ)+basis*width)=
      (fixedFactor boundary scalar groups calls entry restoration : ℝ)+basis*width := by
  rw [childConstantEq]
  unfold fixedFactor
  push_cast
  ring

private theorem nonstopped_coefficient_eq (shape : Shape) (basisConstant : ℝ) (childExponent : ℕ)
    (childrenNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false) :
    (CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient : ℝ)+localCoefficient shape basisConstant childExponent=
      (fixedCoefficient : ℝ)+
        (6*(ComplexRank25.rankSum : ℝ)*basisConstant*(shape.guard : ℝ)^Parameters.tau)*
          ((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.tau := by
  have childConstantEq : CompactComplexSourceReadyActualScheduleBudget.childLocalCoefficient shape childExponent=
      CompactComplexNonleafRolePreparationBudget.constant roles ComplexRecursiveCallSchema.sites.length+
        CompactComplexSourceReadyChildReturnPath.timeConstant roles+4 :=
    stopped_local_algebra
      (CompactComplexNonleafRolePreparationBudget.constant roles ComplexRecursiveCallSchema.sites.length)
      (CompactComplexSourceReadyChildReturnPath.timeConstant roles)
      (CompactComplexSourceReadyActualScheduleBudget.stoppedPrefixCoefficient childExponent)
      (ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)) childrenNonstopped
  exact coefficient_algebra
    CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient
    CompactComplexScheduleRuntimeBudget.scalarCoefficient CompactComplexScheduleRuntimeBudget.groupCount
    ComplexRank25.rankSum
    (CompactComplexNonleafRolePreparationBudget.constant roles ComplexRecursiveCallSchema.sites.length)
    (CompactComplexSourceReadyChildReturnPath.timeConstant roles)
    (CompactComplexSourceReadyActualScheduleBudget.childLocalCoefficient shape childExponent)
    (6*(ComplexRank25.rankSum : ℝ)*basisConstant*(shape.guard : ℝ)^Parameters.tau)
    (((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.tau) childConstantEq

/-- At a genuine nonstopped level the actual recurrence has only the original
width-to-tau forcing, including its complete fixed boundary. -/
theorem nonstopped_step (shape : Shape) (basisConstant : ℝ) (childExponent : ℕ)
    (childrenNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=false) :
    pathCoefficient shape basisConstant (childExponent+1)≤
      (ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent+
      forcingCoefficient shape basisConstant*((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.tau := by
  have widthAtLeastOne : 1≤((arity^(childExponent+1) : ℕ) : ℝ)^Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast (Nat.one_le_pow (childExponent+1) arity (by decide)))
      CompactComplexRecursiveRuntimeSum.exponents.1.le
  have fixedNonnegative : (0 : ℝ)≤fixedCoefficient := Nat.cast_nonneg _
  have coefficientEquation := nonstopped_coefficient_eq shape basisConstant childExponent childrenNonstopped
  rw [pathCoefficient,childrenNonstopped]
  simp only [Bool.false_eq_true,ite_false]
  rw [coefficientEquation]
  exact absorb_fixed _ _ _ _ fixedNonnegative widthAtLeastOne

/-- The original integer classifier never stops again above a nonstopped
exponent; this discharges every level of the analytic suffix. -/
theorem nonstopped_above (axes baseExponent exponent : ℕ)
    (baseNonstopped : ComplexRecursiveCallSchema.stopped axes baseExponent=false)
    (exponentAbove : baseExponent≤exponent) :
    ComplexRecursiveCallSchema.stopped axes exponent=false := by
  have baseConditions : ¬(baseExponent=0 ∨ (arity^baseExponent)^1000<axes) :=
    of_decide_eq_false baseNonstopped
  have exponentPositive : exponent≠0 := by
    intro exponentZero
    have baseZero : baseExponent=0 := by omega
    exact baseConditions (Or.inl baseZero)
  have widthMonotone : (arity^baseExponent)^1000≤(arity^exponent)^1000 :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide : 0<arity) exponentAbove) 1000
  have noStop : ¬(exponent=0 ∨ (arity^exponent)^1000<axes) := by
    rintro (exponentZero | stoppedWidth)
    · exact exponentPositive exponentZero
    · exact baseConditions (Or.inr (lt_of_le_of_lt widthMonotone stoppedWidth))
  exact decide_eq_false_iff_not.mpr noStop

/-- The actual real provider recurrence has a closed geometric estimate above
any original stopping cutoff. The same selected budgets retain their exact
cutoff charge; no supplied local-work or total-runtime bound occurs here. -/
theorem path_coefficient_bound (shape : Shape) (basisConstant : ℝ)
    (constantNonnegative : 0≤basisConstant) (leafExponent depth : ℕ)
    (aboveCutoff : ComplexRecursiveCallSchema.stopped shape.axes (leafExponent+1)=false) :
    pathCoefficient shape basisConstant (leafExponent+depth)≤
      (pathCoefficient shape basisConstant leafExponent+
        forcingCoefficient shape basisConstant*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*
          CompactComplexRecursiveRuntimeSum.localConstant)*
        ((arity^depth : ℕ) : ℝ)^Parameters.sigma := by
  have widthBound (level : ℕ) :
      ((arity^(leafExponent+level+1) : ℕ) : ℝ)^Parameters.tau≤
        ((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*
          ((arity : ℝ)^Parameters.sigma)^(level+1) := by
    rw [show leafExponent+level+1=leafExponent+(level+1) by omega,pow_add,Nat.cast_mul,
      Real.mul_rpow (by positivity) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Swap.Recurrence.rpow_pow_eq]
    apply pow_le_pow_left₀ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num [arity])
      CompactComplexRecursiveRuntimeSum.exponents.2.1
  have forcingNonnegative := forcing_nonnegative shape basisConstant constantNonnegative
  have bound := CompactComplexRecursiveRuntimeSum.geometric_forcing
    (F:=fun level => pathCoefficient shape basisConstant (leafExponent+level))
    (a:=(ComplexRank25.rankSum : ℝ)/roles) (x:=(arity : ℝ)^Parameters.sigma)
    (B:=pathCoefficient shape basisConstant leafExponent)
    (C:=forcingCoefficient shape basisConstant*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (by simpa only [show (roles : ℝ)=58645352620000 by norm_num [roles,CompactComplexRolePhaseSite.roleCount],
      show (arity : ℝ)=15625 by norm_num [arity]] using ComplexRank25.branching_bound)
    (CompactComplexActualProviderRuntime.path_coefficient_nonnegative shape basisConstant constantNonnegative leafExponent)
    (mul_nonneg forcingNonnegative (by positivity)) le_rfl
    (fun level => by
      have step := nonstopped_step shape basisConstant (leafExponent+level)
        (nonstopped_above shape.axes (leafExponent+1) (leafExponent+level+1) aboveCutoff (by omega))
      have forcingBound := mul_le_mul_of_nonneg_left (widthBound level) forcingNonnegative
      exact step.trans (by simpa only [mul_assoc,Nat.add_assoc] using
        (add_le_add (le_refl ((ComplexRank25.rankSum : ℝ)/roles*
          pathCoefficient shape basisConstant (leafExponent+level))) forcingBound))) depth
  rw [Swap.Recurrence.rpow_pow_eq] at bound
  simpa only [CompactComplexRecursiveRuntimeSum.localConstant,CompactComplexRecursiveRuntimeSum.roles,
    CompactComplexRecursiveRuntimeSum.children,roles,CompactComplexRolePhaseSite.roleCount,mul_div_assoc] using bound

private theorem add_boundary_algebra (root boundary localWork recursive : ℝ) (boundaryNonnegative : 0≤boundary) :
    root+localWork+recursive≤root+(boundary+localWork+recursive) := by
  linarith only [boundaryNonnegative]

private theorem absorb_root (root total width : ℝ) (rootNonnegative : 0≤root) (widthAtLeastOne : 1≤width) :
    root+total*width≤(root+total)*width := by
  have rootBound := mul_le_mul_of_nonneg_left widthAtLeastOne rootNonnegative
  nlinarith only [rootBound]

private theorem reorder_sum_product (root leaf localWork width nativeVolume : ℝ) :
    ((root+(leaf+localWork))*width)*nativeVolume=((root+leaf+localWork)*nativeVolume)*width := by
  ring

/-- The coefficient bounding the very same halted root trace has the closed
geometric estimate. Complete root boundary charges and the exact stopped
cutoff coefficient remain explicit, while every recursive level is summed. -/
theorem root_coefficient_bound (shape : Shape) (basisConstant : ℝ)
    (constantNonnegative : 0≤basisConstant) (childExponent leafExponent depth nativeVolume : ℕ)
    (nodeExponent : childExponent+1=leafExponent+depth)
    (aboveCutoff : ComplexRecursiveCallSchema.stopped shape.axes (leafExponent+1)=false) :
    ((CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
      localCoefficient shape basisConstant childExponent+
      if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
        (ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent)*
        (nativeVolume : ℝ)≤
      ((CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
        pathCoefficient shape basisConstant leafExponent+
        forcingCoefficient shape basisConstant*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*
          CompactComplexRecursiveRuntimeSum.localConstant)*
        (nativeVolume : ℝ)*((arity^depth : ℕ) : ℝ)^Parameters.sigma := by
  have recurrenceBound :
      (CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
        localCoefficient shape basisConstant childExponent+
        (if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
          (ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent)≤
      (CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)+
        pathCoefficient shape basisConstant (childExponent+1) :=
    add_boundary_algebra
      (CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)
      (CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient : ℝ)
      (localCoefficient shape basisConstant childExponent)
      (if ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1) then 0 else
        (ComplexRank25.rankSum : ℝ)/roles*pathCoefficient shape basisConstant childExponent)
      (Nat.cast_nonneg _)
  have geometricBound := path_coefficient_bound shape basisConstant constantNonnegative leafExponent depth aboveCutoff
  rw [←nodeExponent] at geometricBound
  have widthAtLeastOne : 1≤((arity^depth : ℕ) : ℝ)^Parameters.sigma :=
    Real.one_le_rpow (by exact_mod_cast (Nat.one_le_pow depth arity (by decide)))
      (le_trans CompactComplexRecursiveRuntimeSum.exponents.1.le CompactComplexRecursiveRuntimeSum.exponents.2.1)
  have rootBound := absorb_root
    (CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)
    (pathCoefficient shape basisConstant leafExponent+
      forcingCoefficient shape basisConstant*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*
        CompactComplexRecursiveRuntimeSum.localConstant)
    (((arity^depth : ℕ) : ℝ)^Parameters.sigma) (Nat.cast_nonneg _) widthAtLeastOne
  have coefficientBound := recurrenceBound.trans ((add_le_add le_rfl geometricBound).trans rootBound)
  have volumeBound := mul_le_mul_of_nonneg_right coefficientBound (Nat.cast_nonneg nativeVolume)
  exact volumeBound.trans_eq (reorder_sum_product
    (CompactComplexSourceReadyRecursiveRootExecution.rootBoundaryCoefficient : ℝ)
    (pathCoefficient shape basisConstant leafExponent)
    (forcingCoefficient shape basisConstant*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*
      CompactComplexRecursiveRuntimeSum.localConstant)
    (((arity^depth : ℕ) : ℝ)^Parameters.sigma) (nativeVolume : ℝ))

end
end IntegerMultBounds.Machine.CompactComplexActualProviderRuntimeSum
