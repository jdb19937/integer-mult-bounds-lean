module

public import IntegerMultBounds.MathlibTM2.Cost.CompactStage
public import IntegerMultBounds.MathlibTM2.Node.CompactRotStage
import Mathlib.Tactic.Positivity.Finset

/-! Connect the actual normalized compact-stage bank to its linear size budget. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Node
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData ActiveRepairLayoutRecordsData

noncomputable section

theorem compactStageWords_length_sum {s : Shape} {A k : ℕ} (d : Inputs s)
    (x : Array s d.rows) :
    (∑ j : Fin (66+k), (compactStageWords (A := A) d x j).length) = compactStageBankSize d := by
  have hprivate (j : Fin k) : compactStageWords (A := A) d x (Fin.natAdd 66 j) = [] := by
    have hj := j.isLt
    simp [compactStageWords, Fin.val_natAdd, show ¬66+j.val<13 by omega,
      show 66+j.val≠65 by omega]
  rw [Fin.sum_univ_add]
  simp only [hprivate, List.length_nil, Finset.sum_const_zero, add_zero]
  have hheader (j : Fin 13) :
      (compactStageWords (A := A) d x (Fin.castAdd k (Fin.castAdd 53 j))).length =
        1 + (RecursiveChildQuotientsConstant.bits
          (ActivePrefixStageHeadersData.originalValues d.stage d.rows j)).length := by
    simp [compactStageWords, j.isLt, Nat.add_comm]
  have hblank (j : Fin 52) :
      compactStageWords (A := A) d x
        (Fin.castAdd k (Fin.castAdd 1 (Fin.natAdd 13 j))) = [] := by
    have hj := j.isLt
    simp [compactStageWords, Fin.val_natAdd, show ¬13+j.val<13 by omega,
      show 13+j.val≠65 by omega]
  have hraw : (compactStageWords (A := A) d x (Fin.castAdd k (65 : Fin 66))).length =
      d.rows * s.recordWidth := by
    simp [compactStageWords]
  change (∑ j : Fin (65+1), (compactStageWords (A := A) d x (Fin.castAdd k j)).length) = _
  rw [Fin.sum_univ_add]
  change (∑ j : Fin (13+52), (compactStageWords (A := A) d x
    (Fin.castAdd k (Fin.castAdd 1 j))).length) + _ = _
  rw [Fin.sum_univ_add]
  simp only [hblank, List.length_nil, Finset.sum_const_zero, add_zero, Fin.sum_univ_one]
  have hc (j : Fin 13) : Fin.castAdd 1 (Fin.castAdd 52 j) = Fin.castAdd 53 j := Fin.ext rfl
  simp only [hc, hheader]
  change _ + (compactStageWords (A := A) d x (Fin.castAdd k (65 : Fin 66))).length = _
  rw [hraw]
  rfl

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host
variable {s : Shape} {T Q K : ℕ} {U F : Type}

/-- Fixed host coefficient for the complete early compact stage. -/
noncomputable def compactEarlyHostConst (T D : ℕ) : ℝ :=
  Classical.choose (compactStageEarlyHost_uniform T ActivePrefixStageFullEarlyRun.count D)

theorem compactEarlyProg_exec_le (body : F → Pr F T Q (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K) U)
    (hQ : compactEarlyStates ≤ Q)
    (ι : Fin ActivePrefixStageFullEarlyRun.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageFullEarlyRun.count ≤ T)
    (d : Inputs s) (x : Array s d.rows) (horder : d.stage.source.val<d.stage.target.val)
    
    (hq3 : s.guard+3≤s.chunk)
    (hRbits : (ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1≤s.payload)
    (D : ℕ) (hdensity : VaryingControlRepairDensity.earlyDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1)≤D)
    (v : HS T Q (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K) U) (S : Stacks T (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K))
    (hL : ∀ j, S.L (ι j)=[])
    (hR : ∀ j, S.R (ι j)=compactStageWords d x j) :
    ∃ (v' : HS T Q (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K) U) (m : ℕ), v'.user=v.user ∧
      (m : ℝ) ≤ compactEarlyHostConst T D * (d.rows * s.recordWidth : ℕ) *
        ((max 1 ((d.stage.f - 1) * s.guard) : ℕ) : ℝ) ^ Parameters.tau ∧
      Exec body (compactEarlyProg hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun z => if z ∈ Set.range ι then [] else S.L z
          R := fun z => if h : z ∈ Set.range ι then
            compactStageWords d (earlyResult d horder x) (Classical.choose h) else S.R z }) := by
  obtain ⟨v', steps, hu, hm, he⟩ := compactEarlyProg_exec body hQ ι hι hT d x horder
    hq3 hRbits D hdensity v S hL hR
  refine ⟨v', steps, hu, ?_, he⟩
  rw [compactStageWords_length_sum] at hm
  have hsteps : steps ≤ compactStageHostCost T ActivePrefixStageFullEarlyRun.count 13
      (ActivePrefixStageFullEarlyRun.cost D d horder) (compactStageBankSize d) := by
    simpa only [compactStageHostCost, Nat.add_assoc] using hm
  have hb := (Classical.choose_spec
    (compactStageEarlyHost_uniform T ActivePrefixStageFullEarlyRun.count D)).2 s d horder
  exact (Nat.cast_le.mpr hsteps).trans hb

/-- Fixed host coefficient for the complete late compact stage. -/
noncomputable def compactLateHostConst (T D : ℕ) : ℝ :=
  Classical.choose (compactStageLateHost_uniform T ActivePrefixStageFullLateRun.count D)

theorem compactLateProg_exec_le (body : F → Pr F T Q (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K) U)
    (hQ : compactLateStates ≤ Q)
    (ι : Fin ActivePrefixStageFullLateRun.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageFullLateRun.count ≤ T)
    (d : Inputs s) (x : Array s d.rows) (horder : d.stage.target.val<d.stage.source.val)
    (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (hq3 : s.guard+3≤s.chunk)
    (hRbits : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1≤s.payload)
    (D : ℕ) (hdensity : VaryingControlRepairDensity.lateDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1)≤D)
    (v : HS T Q (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K) U) (S : Stacks T (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K))
    (hL : ∀ j, S.L (ι j)=[])
    (hR : ∀ j, S.R (ι j)=compactStageWords d x j) :
    ∃ (v' : HS T Q (_root_.IntegerMultBounds.Networks.Shared50ModularControl.prime+K) U) (m : ℕ), v'.user=v.user ∧
      (m : ℝ) ≤ compactLateHostConst T D * (d.rows * s.recordWidth : ℕ) *
        ((max 1 ((d.stage.f - 1) * s.guard) : ℕ) : ℝ) ^ Parameters.tau ∧
      Exec body (compactLateProg hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun z => if z ∈ Set.range ι then [] else S.L z
          R := fun z => if h : z ∈ Set.range ι then
            compactStageWords d (lateResult d horder x) (Classical.choose h) else S.R z }) := by
  obtain ⟨v', steps, hu, hm, he⟩ := compactLateProg_exec body hQ ι hι hT d x horder hn hb
    hq3 hRbits D hdensity v S hL hR
  refine ⟨v', steps, hu, ?_, he⟩
  rw [compactStageWords_length_sum] at hm
  have hsteps : steps ≤ compactStageHostCost T ActivePrefixStageFullLateRun.count 13
      (ActivePrefixStageFullLateRun.cost D d horder hn hb) (compactStageBankSize d) := by
    simpa only [compactStageHostCost, Nat.add_assoc] using hm
  have hb := (Classical.choose_spec
    (compactStageLateHost_uniform T ActivePrefixStageFullLateRun.count D)).2 s d horder hn hb
  exact (Nat.cast_le.mpr hsteps).trans hb

end
end IntegerMultBounds.MathlibTM2.Cost
