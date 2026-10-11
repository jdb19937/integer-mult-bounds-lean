module

public import IntegerMultBounds.Machine.CompactComplexCorrectedNonleafBoundaryBudget
public import IntegerMultBounds.Machine.CompactComplexActualCallAlignment

/-! The actual aligned event schedule pays a forward and reverse basis pass
and both new sequencing joins at every original recursive occurrence. The
basis stage scale remains explicit, separate from linear native volume. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedScheduleRuntimeBudget
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexScheduleRuntimeBudget (scalarCoefficient groupCount)
open CompactNativeRoleTransferBudget (volume)
open CompactRecursiveDependencyBudget (Path)
attribute [local irreducible] ComplexRank25.program ComplexRank25.rankSum
  ComplexRecursiveCallSchema.calls CompactComplexCompletedLiveLower.groups schedule
  CompactComplexRolePhaseSite.roleCount
variable {sh : Shape} {left e levels frames count : ℕ}

def basisAllowance (basisCost : ℕ) : Event → ℕ
  | .scalar _ => 0
  | .child _ => 2*basisCost+2

def eventAllowance (basisCost : ℕ) (sh : Shape) (rows ell p leaf depth : ℕ)
    (localCost : ℕ → ℕ) (event : Event) :=
  CompactComplexScheduleRuntimeBudget.eventAllowance sh rows ell p leaf depth localCost event+
    basisAllowance basisCost event

private theorem constant_sum {α : Type*} (xs : List α) (n : ℕ) :
    (xs.map (fun _ => n)).sum=xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih];ring

/-- Every original call is counted, including repeated equal labels. -/
theorem basis_sum (basisCost : ℕ) :
    (schedule.map (basisAllowance basisCost)).sum=ComplexRank25.rankSum*(2*basisCost+2) := by
  have h := CompactComplexScheduleRuntimeBudget.schedule_sum (fun _ => 0) (fun _ => 2*basisCost+2)
  change (schedule.map (basisAllowance basisCost)).sum=_ at h
  rw [Finset.sum_const_zero,zero_add,constant_sum,ComplexRecursiveCallSchema.calls_rankSum] at h
  exact h

private theorem map_add_sum {α : Type*} (xs : List α) (f g : α → ℕ) :
    (xs.map (fun a => f a+g a)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih];omega

/-- Exact extra cost of the concrete forward-entry and return-reverse wrappers. -/
theorem schedule_eq (basisCost : ℕ) (sh : Shape) (rows ell p leaf depth : ℕ)
    (localCost : ℕ → ℕ) :
    (schedule.map (eventAllowance basisCost sh rows ell p leaf depth localCost)).sum=
      (schedule.map (CompactComplexScheduleRuntimeBudget.eventAllowance sh rows ell p leaf depth localCost)).sum+
      ComplexRank25.rankSum*(2*basisCost+2) := by
  exact (map_add_sum schedule _ (basisAllowance basisCost)).trans
    (congrArg (fun n =>
      (schedule.map (CompactComplexScheduleRuntimeBudget.eventAllowance sh rows ell p leaf depth localCost)).sum+n)
      (basis_sum basisCost))

/-- Original scalar/native entry/return allowances and recursive budgets are
retained exactly; both extra physical basis passes are paid separately. -/
theorem schedule_bound (basisCost : ℕ) (sh : Shape) (rows ell p leaf depth : ℕ)
    (localCost : ℕ → ℕ) (hr : 0<rows) :
    (schedule.map (eventAllowance basisCost sh rows ell p leaf depth localCost)).sum≤
      (scalarCoefficient+groupCount+ComplexRank25.rankSum*CompactComplexScheduleRuntimeBudget.childCoefficient)*volume rows sh ell p+
      ComplexRank25.rankSum*CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
        (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles)+
      ComplexRank25.rankSum*(2*basisCost+2) := by
  rw [schedule_eq]
  exact Nat.add_le_add_right (CompactComplexScheduleRuntimeBudget.schedule_bound sh rows ell p leaf depth localCost hr) _

/-- Complete corrected root/child boundary plus aligned interleaved schedule;
recursive child work and physical basis work remain distinct paid terms. -/
theorem boundary_schedule_bound (basisCost rows ell p leaf depth : ℕ) (localCost : ℕ → ℕ)
    (rho : Fin sh.chunk) (path : Path sh.active left e levels frames count)
    (hr : 0<rows) (hG : 0<sh.guard) (isRoot : Bool) :
    (if isRoot then CompactComplexCorrectedNonleafBoundaryBudget.rootCost sh rows ell p e
      else CompactComplexCorrectedNonleafBoundaryBudget.childCost sh rows ell p)+
      (schedule.map (eventAllowance basisCost sh rows ell p leaf depth localCost)).sum≤
      (CompactComplexCorrectedNonleafBoundaryBudget.rootCoefficient+
        CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient+
        (scalarCoefficient+groupCount+ComplexRank25.rankSum*CompactComplexScheduleRuntimeBudget.childCoefficient))*volume rows sh ell p+
      ComplexRank25.rankSum*CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
        (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles)+
      ComplexRank25.rankSum*(2*basisCost+2) := by
  rw [schedule_eq,←Nat.add_assoc]
  exact Nat.add_le_add_right
    (CompactComplexCorrectedNonleafBoundaryBudget.boundary_schedule_bound rows ell p leaf depth localCost rho path hr hG isRoot) _

/-- Round the actual physical wrapper's certified real allowance up once,
without changing its width exponent. -/
def roundedBasisCost {s : Shape} (C : ℝ) (d : ActivePrefixStageFullData.Inputs s) : ℕ :=
  ⌈C*ActivePrefixStageInverseBudget.scale d⌉₊

theorem runtime_le_rounded {s : Shape} (C : ℝ) (d : ActivePrefixStageFullData.Inputs s)
    (time : ℕ) (h : (time : ℝ)≤C*ActivePrefixStageInverseBudget.scale d) :
    time≤roundedBasisCost C d := by
  exact_mod_cast h.trans (Nat.le_ceil (C*ActivePrefixStageInverseBudget.scale d))

private theorem rounded_allowance_bound (C S : ℝ) (hC : 0≤C) (hS : 1≤S) :
    (2*(⌈C*S⌉₊ : ℝ)+2)≤(2*C+4)*S := by
  have hn := (Nat.ceil_lt_add_one (mul_nonneg hC (by linarith : 0≤S))).le
  nlinarith only [hn,hS]

/-- The real basis allowance is a fixed coefficient times the actual expanded
parent stage scale. Rounding and both joins are included in the coefficient. -/
theorem basis_sum_scale {s : Shape} (C : ℝ) (hC : 0≤C)
    (d : ActivePrefixStageFullData.Inputs s) :
    ((schedule.map (basisAllowance (roundedBasisCost C d))).sum : ℝ)≤
      (ComplexRank25.rankSum : ℝ)*(2*C+4)*ActivePrefixStageInverseBudget.scale d := by
  have h := rounded_allowance_bound C (ActivePrefixStageInverseBudget.scale d) hC
    (ActivePrefixStageInverseBudget.one_le_scale d)
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg ComplexRank25.rankSum : (0 : ℝ)≤ComplexRank25.rankSum)
  rw [basis_sum]
  dsimp only [roundedBasisCost]
  push_cast
  exact hm.trans_eq (by ring)


private theorem real_bound (A L V branches recurse extra : ℕ) (F S : ℝ)
    (hn : A≤L*V+branches*recurse+extra)
    (he : (extra : ℝ)≤(branches : ℝ)*F*S) :
    (A : ℝ)≤(L : ℝ)*(V : ℝ)+(branches : ℝ)*(recurse : ℝ)+(branches : ℝ)*F*S := by
  have h := Nat.cast_le (α:=ℝ).mpr hn
  push_cast at h
  linarith only [h,he]

/-- Instantiate both real physical passes by their uniform expanded-stage
allowance while preserving the complete original native boundary coefficient
and the exact recursive child budget. -/
theorem boundary_schedule_scale {s : Shape} (C : ℝ) (hC : 0≤C)
    (d : ActivePrefixStageFullData.Inputs s) (rows ell p leaf depth : ℕ) (localCost : ℕ → ℕ)
    (rho : Fin sh.chunk) (path : Path sh.active left e levels frames count)
    (hr : 0<rows) (hG : 0<sh.guard) (isRoot : Bool) :
    (((if isRoot then CompactComplexCorrectedNonleafBoundaryBudget.rootCost sh rows ell p e
      else CompactComplexCorrectedNonleafBoundaryBudget.childCost sh rows ell p)+
      (schedule.map (eventAllowance (roundedBasisCost C d) sh rows ell p leaf depth localCost)).sum : ℕ) : ℝ)≤
      ((CompactComplexCorrectedNonleafBoundaryBudget.rootCoefficient+
        CompactComplexCorrectedNonleafBoundaryBudget.childCoefficient+
        (scalarCoefficient+groupCount+ComplexRank25.rankSum*CompactComplexScheduleRuntimeBudget.childCoefficient) : ℕ) : ℝ)*
        (volume rows sh ell p : ℝ)+
      (ComplexRank25.rankSum : ℝ)*
        (CompactComplexRecursiveRuntimeSum.budget leaf localCost depth
          (volume rows sh ell p/CompactComplexRecursiveRuntimeSum.roles) : ℝ)+
      (ComplexRank25.rankSum : ℝ)*(2*C+4)*ActivePrefixStageInverseBudget.scale d := by
  have he := basis_sum_scale C hC d
  rw [basis_sum] at he
  exact real_bound _ _ _ _ _ _ (2*C+4) (ActivePrefixStageInverseBudget.scale d)
    (boundary_schedule_bound (roundedBasisCost C d) rows ell p leaf depth localCost rho path hr hG isRoot) he

end
end IntegerMultBounds.Machine.CompactComplexAlignedScheduleRuntimeBudget
