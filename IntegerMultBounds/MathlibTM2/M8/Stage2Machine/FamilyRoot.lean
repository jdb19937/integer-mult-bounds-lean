module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget

/-!
# The reversed family as a halting machine

`FamilySpec` is the data semantics of the reversed family (`RevSemantics.rev97_family_spec`):
every frame of `n ≥ 1` atoms that satisfies `Ok` runs from its entry bank, holding the bits `x`
on the `io` role, to its exit bank at its return address, holding a `y` with `RevT x y`, within
the family bound. A frame whose return address is the halt block then halts (`halt_entry`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyRoot

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open RecursiveInterchangeLayout (Descriptor volume)
open RevMachine
open RevMachine.Family (Frame)
open RevMachine.RevHalf (pcs Ok)

/-- A bit array extended by zeros. -/
def ext {V : ℕ} (x : Fin V → ZMod 2) : ℕ → ZMod 2 := fun i => if h : i < V then x ⟨i, h⟩ else 0

/-- The role tapes holding the bits `x` on `io` and blank elsewhere. -/
def rolesOf {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :=
  NodePark.childRoles rev97m (RecursiveShiftRoleBank.source (Shared50RecursiveNodeSemantics.encoded x))

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k)

/-- The blocks of the family. -/
abbrev impl := Family.impl (LeafCore.core (NodeBank.io rev97m)) (RevNode.blocks rev97m k)

/-- **The family's machine.** -/
abbrev machine := Graph.program (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos (impl (k := k))

/-- The configuration entering block `pc`. -/
abbrev entry (pc : Graph.PC (pcs rev97m).length) (x : Tapes (Family.count (NodeBank.tapes rev97m)) prime) :=
  Graph.entryConfig (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos (impl (k := k)) pc x

/-- The family bound. -/
def bound (C L : ℝ) (n : ℕ) : ℝ :=
  C / (1 - Stage2Moments.q₁) * n + C / (1 - Stage2Moments.qτ) * ((n : ℝ) ^ (1 - (Stage2Moments.saving : ℝ)) * L)

/-- **The data semantics of the reversed family**, with one constant for every atom width `b₀`. -/
def FamilySpec : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ b₀ : ℕ, ∀ L : ℝ, 1 ≤ L → ((bits b₀).length : ℝ) ≤ L →
    ((max 1 b₀ : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
    ∀ σ : Frame (pcs rev97m) capacity, Ok rev97m b₀ σ → 1 ≤ σ.n →
    ∀ x : Fin (volume prime σ.v) → ZMod 2, ∃ y : Fin (volume prime σ.v) → ZMod 2,
      RevT prime b₀ σ.n σ.v (ext x) (ext y) ∧
      ∃ s : ℕ, (s : ℝ) ≤ bound C L σ.n * volume prime σ.v ∧
        run (machine capacity) s (entry capacity .prepare (σ.at (rolesOf x) (Prepare.rest b₀ 529))) =
          some (entry capacity σ.ret (σ.exitAt (rolesOf y) 529))

/-- The program starts at the preparation block. -/
theorem start_entry (x : Tapes (Family.count (NodeBank.tapes rev97m)) prime) :
    (SharedBankStageInput.raw x (Graph.tapeCount (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos
      (impl (k := k)))).start (machine capacity) = entry capacity .prepare x := rfl

/-- The halt block halts. -/
theorem halt_entry (x : Tapes (Family.count (NodeBank.tapes rev97m)) prime) :
    step (machine capacity) (entry capacity .halt x) = none := by
  have hh : step (Graph.family (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos (impl (k := k))
      (Graph.encoding (pcs rev97m) .halt))
      ((SharedBankStageInput.raw x (Graph.tapeCount (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos
        (impl (k := k)))).start (Graph.family (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos
          (impl (k := k)) (Graph.encoding (pcs rev97m) .halt))) = none := by
    unfold Graph.family Graph.states Graph.tapeCount
    rw [(Graph.encoding (pcs rev97m)).symm_apply_apply]
    exact SharedBankFamilyExact.pad_halt (skip _ prime Family.pcSlot_pos)
      (SharedBankFamily.common_le_tapeCount (Graph.block (pcs rev97m) capacity Family.pcSlot
        Family.pcSlot_pos (impl (k := k)))) (le_refl _) x 0
      (by simp [step, skip, SharedBankFamilyExact.atState])
  have he : Graph.next (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos (impl (k := k))
      (Graph.encoding (pcs rev97m) .halt)
      (((SharedBankStageInput.raw x (Graph.tapeCount (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos
        (impl (k := k)))).start (Graph.family (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos
          (impl (k := k)) (Graph.encoding (pcs rev97m) .halt))).state) = none := by
    unfold Graph.next Graph.states Graph.family Graph.tapeCount
    rw [(Graph.encoding (pcs rev97m)).symm_apply_apply]
    rfl
  exact FiniteFlow.halt _ _ _ _ _ hh he

/-- The bank of a frame, padded to the machine's tapes. -/
abbrev padded (x : Tapes (Family.count (NodeBank.tapes rev97m)) prime) :=
  SharedBankStageInput.raw x (Graph.tapeCount (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos
    (impl (k := k)))

/-- **A root frame halts**: a frame returning to the halt block runs from its entry bank to its
exit bank, holding the reversed interchange of its bits, and halts there. -/
theorem root_hoare (hspec : FamilySpec capacity) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b₀ : ℕ, ∀ L : ℝ, 1 ≤ L → ((bits b₀).length : ℝ) ≤ L →
      ((max 1 b₀ : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
      ∀ σ : Frame (pcs rev97m) capacity, Ok rev97m b₀ σ → 1 ≤ σ.n → σ.ret = .halt →
      ∀ x : Fin (volume prime σ.v) → ZMod 2,
        HoareTime (machine capacity) (fun w => w = padded capacity (σ.at (rolesOf x) (Prepare.rest b₀ 529)))
          (fun w => ∃ y : Fin (volume prime σ.v) → ZMod 2, RevT prime b₀ σ.n σ.v (ext x) (ext y) ∧
            w = padded capacity (σ.exitAt (rolesOf y) 529))
          ⌊bound C L σ.n * volume prime σ.v⌋₊ := by
  obtain ⟨C, hC, h⟩ := hspec
  refine ⟨C, hC, fun b₀ L hL hℓ hτ σ hok hn hret x w hw => ?_⟩
  subst hw
  obtain ⟨y, hy, s, hs, hr⟩ := h b₀ L hL hℓ hτ σ hok hn x
  rw [hret] at hr
  exact ⟨s, _, Nat.le_floor hs, hr, halt_entry capacity _, y, hy, rfl⟩

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyRoot
