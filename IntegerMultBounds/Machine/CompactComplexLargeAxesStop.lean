module

public import IntegerMultBounds.Machine.CompactComplexRecursiveGeometry
public import IntegerMultBounds.Networks.ComplexRecursiveCallSchema

/-! Under an explicit large-global-axis hypothesis, exponent-one nodes satisfy
the published stopping test. Thus an unstopped node has exponent at least two.
This does not establish an eventual input-size threshold or cover small axes. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexLargeAxesStop
open CompactComplexRecursiveGeometry (arity)
open Networks.ComplexRecursiveCallSchema (stopped stopped_iff)

/-- Exponent zero is a leaf for every global dimension. -/
theorem zero_stopped (globalAxes : ℕ) : stopped globalAxes 0=true :=
  (stopped_iff globalAxes 0).mpr (Or.inl rfl)

/-- The strict global-axis threshold makes exponent-one nodes actual leaves.
Only the symbolic power-one identity is simplified. -/
theorem one_stopped (globalAxes : ℕ) (largeGlobalAxes : arity^1000<globalAxes) :
    stopped globalAxes 1=true := by
  apply (stopped_iff globalAxes 1).mpr
  right
  simpa only [arity,pow_one] using largeGlobalAxes

attribute [local irreducible] arity

/-- An actual false classifier cannot select a node of exponent zero or one
under the stated large-dimension threshold. -/
theorem nonstopped_exponent_ge_two (globalAxes nodeExponent : ℕ)
    (largeGlobalAxes : arity^1000<globalAxes)
    (nonstopped : stopped globalAxes nodeExponent=false) : 2≤nodeExponent := by
  by_contra exponentTooSmall
  have possibleExponents : nodeExponent=0 ∨ nodeExponent=1 := by
    clear largeGlobalAxes nonstopped
    omega
  rcases possibleExponents with rfl | rfl
  · have contradiction : true=false := (zero_stopped globalAxes).symm.trans nonstopped
    cases contradiction
  · have contradiction : true=false := (one_stopped globalAxes largeGlobalAxes).symm.trans nonstopped
    cases contradiction

/-- The immediate child exponent of an unstopped node is positive, so the
positive-exponent child geometry applies without a zero-exponent exception. -/
theorem nonstopped_child_exponent_positive (globalAxes childExponent : ℕ)
    (largeGlobalAxes : arity^1000<globalAxes)
    (nonstopped : stopped globalAxes (childExponent+1)=false) : 0<childExponent := by
  have parentExponentBound := nonstopped_exponent_ge_two globalAxes (childExponent+1)
    largeGlobalAxes nonstopped
  clear largeGlobalAxes nonstopped
  omega

end IntegerMultBounds.Machine.CompactComplexLargeAxesStop
