module

public import IntegerMultBounds.MathlibTM2.Cost.CompactStageExec
public import IntegerMultBounds.MathlibTM2.Node.CompactRotRuntime
public import IntegerMultBounds.Machine.ActivePrefixStageRuntimeBudget

/-! # Uniform host cost of the runtime-selected compact stage

Both order branches and singleton widths execute in the same fixed host program.
The compact-width envelope includes selectors, complete native execution and
host-bank normalization. Reserved layout and the packed-case density conditions
remain explicit input obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData ActiveRepairLayoutRecordsData
noncomputable section

theorem compactStageBankSize_le_unordered {s : Shape} (d : Inputs s) :
    compactStageBankSize d ≤ 40 * (d.rows * s.recordWidth) := by
  have hne : d.stage.source.val ≠ d.stage.target.val := fun h => d.stage.distinct (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact compactStageBankSize_le d .early h
  · exact compactStageBankSize_le d .late h

theorem compactRuntimeHost_uniform (T D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Shape) (d : Inputs s)
      (hp : 1 < d.stage.f → ActivePrefixStageRuntimeData.Packed d D),
      (compactStageHostCost T ActivePrefixStageRuntimeProgram.count 13
        (ActivePrefixStageRuntimeData.cost D d hp) (compactStageBankSize d) : ℝ) ≤
        C * (d.rows * s.recordWidth : ℕ) *
          ((max 1 ((d.stage.f - 1) * s.guard) : ℕ) : ℝ) ^ Parameters.tau := by
  obtain ⟨C, hC, hbound⟩ := ActivePrefixStageRuntimeBudget.uniform_bound D
  refine ⟨(T + 12*ActivePrefixStageRuntimeProgram.count + 5 : ℕ) * C +
    (240 + 2*T + 6*ActivePrefixStageRuntimeProgram.count + 13 + 10 : ℕ), by positivity, ?_⟩
  intro s d hp
  have hV : 1 ≤ d.rows * s.recordWidth := by
    have hpay : 0 < s.payload := by have := d.hrecord; omega
    exact Nat.mul_pos d.hr (by unfold Shape.recordWidth; positivity)
  exact compactStageHostCost_le hV (compactStageBankSize_le_unordered d) (hbound s d hp)

noncomputable def compactRuntimeHostConst (T D : ℕ) : ℝ :=
  Classical.choose (compactRuntimeHost_uniform T D)

theorem compactRuntimeHostConst_pos (T D : ℕ) : 0 < compactRuntimeHostConst T D :=
  (Classical.choose_spec (compactRuntimeHost_uniform T D)).1

theorem compactRawWords_length_sum {s : Shape} {A N : ℕ} (hN : 66 ≤ N)
    (d : Inputs s) (x : Array s d.rows) :
    (∑ j : Fin N, (compactRawWords (K := A) d x j).length) = compactStageBankSize d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  simpa only [compactRawWords, compactStageWords] using
    (compactStageWords_length_sum (A := A) (k := k) d x)

variable {s : Shape} {T Q K : ℕ} {U F : Type}

/-- Actual runtime selection, complete compact execution and host cleanup share one bound. -/
theorem compactRuntimeProg_exec_le (body : F → Pr F T Q (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K) U)
    (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (D : ℕ) (d : Inputs s) (x : Array s d.rows)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D)
    (v : HS T Q (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K) U) (S : Stacks T (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K))
    (hL : ∀ j, S.L (ι j)=[])
    (hR : ∀ j, S.R (ι j)=compactRawWords d x j) :
    ∃ (v' : HS T Q (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K) U) (m : ℕ), v'.user=v.user ∧
      (m : ℝ) ≤ compactRuntimeHostConst T D * (d.rows * s.recordWidth : ℕ) *
        ((max 1 ((d.stage.f - 1) * s.guard) : ℕ) : ℝ) ^ Parameters.tau ∧
      Exec body (compactRuntimeProg hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun z => if z ∈ Set.range ι then [] else S.L z
          R := fun z => if h : z ∈ Set.range ι then
            compactRawWords d
              (ActivePrefixStageRuntimeData.result d x) (Classical.choose h) else S.R z }) := by
  obtain ⟨v', steps, hu, hm, he⟩ := compactRuntimeProg_exec body hQ ι hι hT D d x hp v S hL hR
  refine ⟨v', steps, hu, ?_, he⟩
  rw [compactRawWords_length_sum compactRuntimeCount] at hm
  have hsteps : steps ≤ compactStageHostCost T ActivePrefixStageRuntimeProgram.count 13
      (ActivePrefixStageRuntimeData.cost D d hp) (compactStageBankSize d) := by
    simpa only [compactStageHostCost, Nat.add_assoc] using hm
  have hb := (Classical.choose_spec (compactRuntimeHost_uniform T D)).2 s d hp
  exact (Nat.cast_le.mpr hsteps).trans hb

end
end IntegerMultBounds.MathlibTM2.Cost
