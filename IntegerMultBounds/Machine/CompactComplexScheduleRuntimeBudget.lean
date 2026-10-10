import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarGeometryLifecycle
import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEntryPath
import IntegerMultBounds.Machine.CompactComplexSourceReadyChildReturnPath
import IntegerMultBounds.Machine.CompactComplexRecursiveRuntimeSum

/-! Actual interleaved scalar groups and original child occurrences have a
concrete weighted runtime allowance. Every table join is charged; recursive
child budgets remain separate. This does not assert recursive execution. -/
namespace IntegerMultBounds.Machine.CompactComplexScheduleRuntimeBudget
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexScalarIntegerRows (GroupIndex)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarCountLifecycle (roleTimeConstant)
open CompactComplexCompletedLiveLower (Event groups schedule assembleWith)
open CompactNativeRoleTransferBudget (volume)
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  ComplexRank25.program ComplexRank25.rankSum ComplexRecursiveCallSchema.calls groups schedule

private def weight (scalar : GroupIndex → ℕ) (child : ComplexRecursiveCallSchema.Call → ℕ) : Event → ℕ
  | .scalar g => scalar g
  | .child c => child c

/-- Weighted sums preserve every actual scalar group and repeated call site,
independently of the interleaving boundaries. -/
theorem assemble_sum (count : GroupIndex → ℕ) (scalar : GroupIndex → ℕ)
    (child : ComplexRecursiveCallSchema.Call → ℕ) (gs : List GroupIndex)
    (cs : List ComplexRecursiveCallSchema.Call) :
    ((assembleWith count gs cs).map (weight scalar child)).sum=
      (gs.map scalar).sum+(cs.map child).sum := by
  induction gs generalizing cs with
  | nil => simp only [assembleWith,List.map_map,Function.comp_def,weight,List.map_nil,List.sum_nil,zero_add]
  | cons g gs ih =>
    have hs : ((cs.take (count g)).map child).sum+((cs.drop (count g)).map child).sum=
        (cs.map child).sum := by
      rw [←List.sum_append,←List.map_append,List.take_append_drop]
    simp only [assembleWith,List.map_append,List.sum_append,List.map_map,Function.comp_def,weight,
      List.map_cons,List.sum_cons,ih]
    change ((cs.take (count g)).map child).sum+
      (scalar g+((gs.map scalar).sum+((cs.drop (count g)).map child).sum))=
      (scalar g+(gs.map scalar).sum)+(cs.map child).sum
    omega

/-- The original controller schedule has exactly one weighted scalar term per
named group and one weighted child term per original recursive occurrence. -/
theorem schedule_sum (scalar : GroupIndex → ℕ) (child : ComplexRecursiveCallSchema.Call → ℕ) :
    (schedule.map (weight scalar child)).sum=
      (∑ g : GroupIndex,scalar g)+(ComplexRecursiveCallSchema.calls.map child).sum := by
  unfold schedule CompactComplexCompletedLiveLower.assemble
  rw [assemble_sum]
  unfold groups
  rw [List.map_ofFn]
  simp only [Function.comp_def,id_eq,List.sum_ofFn]

/-- Constants of the actual scalar programs, including generated count setup,
scalar rows, live increments and complete count erasure. -/
@[irreducible] def scalarCoefficient := ∑ g : GroupIndex,roleTimeConstant (block g)
private theorem scalarCoefficient_eq : scalarCoefficient=∑ g : GroupIndex,roleTimeConstant (block g) := by
  unfold scalarCoefficient
  rfl

@[irreducible] def groupCount := Fintype.card GroupIndex
private theorem groupCount_eq : groupCount=Fintype.card GroupIndex := by
  unfold groupCount
  rfl

/-- Entry and return programs' certified coefficients, plus both literal
controller transitions. Child execution is not included in this coefficient. -/
@[irreducible] def childCoefficient :=
  CompactComplexNonleafRolePreparationBudget.constant CompactComplexRolePhaseSite.roleCount
    ComplexRecursiveCallSchema.sites.length+
  CompactComplexSourceReadyChildReturnPath.timeConstant CompactComplexRolePhaseSite.roleCount+2

def scalarAllowance (sh : Shape) (rows ell p : ℕ) (g : GroupIndex) :=
  roleTimeConstant (block g)*(rows*2^sh.bits*2^ell)*(CompactNativeRoleHeaders.recordWidth sh p+1)+1

def eventAllowance (sh : Shape) (rows ell p leaf depth : ℕ) (localCost : ℕ → ℕ) : Event → ℕ :=
  weight (scalarAllowance sh rows ell p)
    (fun _ => childCoefficient*volume rows sh ell p+
      CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
        (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles))

private theorem scalar_measure (sh : Shape) (rows ell p : ℕ) :
    (rows*2^sh.bits*2^ell)*(CompactNativeRoleHeaders.recordWidth sh p+1)≤volume rows sh ell p := by
  have he : volume rows sh ell p=
      2*((rows*2^sh.bits*2^ell)*(CompactNativeRoleHeaders.recordWidth sh p+1)) := by
    unfold volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner
    ring
  rw [he]
  omega

private theorem weighted_sum_le {α : Type*} [Fintype α] (f : α → ℕ)
    (coefficient cardinality count width V : ℕ)
    (hf : coefficient=∑ a,f a) (hcard : cardinality=Fintype.card α)
    (hm : count*width≤V) (hV : 0<V) :
    (∑ a,(f a*count*width+1))≤(coefficient+cardinality)*V := by
  have h := Nat.mul_le_mul_left coefficient hm
  have hc := Nat.le_mul_of_pos_right cardinality hV
  rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul]
  simp only [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,mul_one]
  rw [←hf,←hcard]
  nlinarith only [h,hc]

theorem scalar_sum (sh : Shape) (rows ell p : ℕ) (hr : 0<rows) :
    (∑ g : GroupIndex,scalarAllowance sh rows ell p g)≤
      (scalarCoefficient+groupCount)*volume rows sh ell p := by
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  exact weighted_sum_le (fun g : GroupIndex => roleTimeConstant (block g)) scalarCoefficient groupCount
    (rows*2^sh.bits*2^ell) (CompactNativeRoleHeaders.recordWidth sh p+1)
    (volume rows sh ell p) scalarCoefficient_eq groupCount_eq (scalar_measure sh rows ell p) hV

private theorem constant_sum {α : Type*} (xs : List α) (n : ℕ) :
    (xs.map (fun _ => n)).sum=xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih];ring

private theorem aggregate_le (scalar groups child branches V recurse actualScalar : ℕ)
    (hs : actualScalar≤(scalar+groups)*V) :
    actualScalar+branches*(child*V+recurse)≤
      (scalar+groups+branches*child)*V+branches*recurse := by
  nlinarith only [hs]

/-- Actual static event allowances fit the RuntimeSum successor shape, with
all scalar groups, original repeated children and two child table joins paid.
No summed cost or recursive execution hypothesis is supplied. -/
theorem schedule_bound (sh : Shape) (rows ell p leaf depth : ℕ) (localCost : ℕ → ℕ)
    (hr : 0<rows) :
    (schedule.map (eventAllowance sh rows ell p leaf depth localCost)).sum≤
      (scalarCoefficient+groupCount+ComplexRank25.rankSum*childCoefficient)*volume rows sh ell p+
      ComplexRank25.rankSum*
        CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
          (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles) := by
  unfold eventAllowance
  rw [schedule_sum,constant_sum,ComplexRecursiveCallSchema.calls_rankSum]
  have hs := scalar_sum sh rows ell p hr
  have h := aggregate_le scalarCoefficient groupCount childCoefficient ComplexRank25.rankSum
    (volume rows sh ell p)
    (CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
      (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles)) _ hs
  exact h

end
end IntegerMultBounds.Machine.CompactComplexScheduleRuntimeBudget
