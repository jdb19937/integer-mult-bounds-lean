module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Assembly

/-!
# The stage-2 core as one machine

The nine pieces of the core are fixed programs on the core's tapes: the header switches
(`Switch`), the shears (`ShearRun`), the family runs and the leaf. With the width `e` of the view
kept on the scalar tape (`Place.memo`) and one caller stack, `core_run`: given the family's data
semantics, the core transposes the array of every positive view of width `e ≥ 2` whose rows split
over the family's depth, within a constant times `V e^τ₂`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreRun

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankFamily (padProgram)
open Stage2Wrapper (top low)
open Stage2Width (tau2)
open RevMachine
open FamilyRoot (ext FamilySpec)
open Assembly (tW bank wOf nOf rOf famP leafP switch_le shear_le)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

/-- The switch to the top digits. -/
def toTop := padProgram (Switch.placed Switch.topList Switch.topRoute Switch.topRoute_inj).program (switch_le capacity)

/-- The switch to the low digits. -/
def toLow := padProgram (Switch.placed Switch.lowList Switch.lowRoute Switch.lowRoute_inj).program (switch_le capacity)

/-- The switch back. -/
def back := padProgram (Switch.placed Switch.backList Switch.backRoute Switch.backRoute_inj).program (switch_le capacity)

/-- `d ← d - h`. -/
def shear₁ := ShearRun.program (switch_le capacity) (shear_le capacity) ShearSem.ops₁ ShearRun.fits₁

/-- `d ← d + h`. -/
def shear₂ := ShearRun.program (switch_le capacity) (shear_le capacity) ShearSem.ops₂ ShearRun.fits₂

/-- `d ← h - d`. -/
def shear₃ := ShearRun.program (switch_le capacity) (shear_le capacity) ShearSem.ops₃ ShearRun.fits₃

/-- **The stage-2 core**: one fixed program. -/
def program :=
  Core.core (toTop capacity) (shear₁ capacity) (famP capacity) (shear₂ capacity) (famP capacity) (shear₃ capacity)
    (toLow capacity) (leafP capacity) (back capacity)

/-- The constant of the switches and shears. -/
def D : ℕ := 10001 * 171 + 3 * (AtomRoleSegment.chainConst ShearRun.io ShearSem.ops₁ +
  AtomRoleSegment.chainConst ShearRun.io ShearSem.ops₂ + AtomRoleSegment.chainConst ShearRun.io ShearSem.ops₃ + 200000)

omit [M8.Machine.Net] in
theorem switches_le {a b c V : ℕ} {s : ℕ} (hs : 1 ≤ s) (ha : a ≤ 10001 * 51 * V) (hb : b ≤ 10001 * 72 * V)
    (hc : c ≤ 10001 * 48 * V) {D : ℕ} (hD : 10001 * 171 ≤ D) :
    ((a : ℝ) + b + c) ≤ (D : ℝ) * s * V := by
  have h : a + b + c ≤ D * s * V := by
    have : 10001 * 171 * V ≤ D * s * V := Nat.mul_le_mul_right _ (by nlinarith)
    omega
  exact_mod_cast h

omit [M8.Machine.Net] in
theorem shears_le {a b c x y z n V : ℕ} (ha : a ≤ (x + 200000) * (n + 1) * V)
    (hb : b ≤ (y + 200000) * (n + 1) * V) (hc : c ≤ (z + 200000) * (n + 1) * V) :
    ((a : ℝ) + b + c) ≤ ((10001 * 171 + 3 * (x + y + z + 200000) : ℕ) : ℝ) * ((n : ℝ) + 1) * V := by
  have h : a + b + c ≤ (10001 * 171 + 3 * (x + y + z + 200000)) * (n + 1) * V := by
    have e : (10001 * 171 + 3 * (x + y + z + 200000)) * (n + 1) * V =
      10001 * 171 * ((n + 1) * V) + 3 * ((x + 200000) * (n + 1) * V + (y + 200000) * (n + 1) * V +
        (z + 200000) * (n + 1) * V) - 3 * 400000 * ((n + 1) * V) := by
      rw [Nat.sub_eq_of_eq_add]; ring
    nlinarith
  exact_mod_cast h

local instance (w : ℕ) : NeZero (prime ^ w) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

/-- **The stage-2 core.** Given the family's data semantics, the core transposes the array of
every positive view of width `e ≥ 2` whose rows split over the family's depth, within a constant
times `V e^τ₂`. -/
theorem core_run (hspec : FamilySpec capacity) {K : ℕ} (hK : 2 ≤ K)
    (hs1 : Cost.tauS ≤ M8.Machine.BudgetBound.tau) (hτ₁ : M8.Machine.BudgetBound.tau ≤ 1)
    (hhalf : 1 / 2 ≤ M8.Machine.BudgetBound.tau)
    (h2 : 1 / 2 ≤ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau)
    (hlin : 1 - (K : ℝ)⁻¹ ≤ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau) :
    ∃ C' : ℝ, ∀ v : Descriptor, v.Positive → 2 ≤ v.width →
      rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) (nOf K v) ∣ v.rows →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ), (∀ z, p ≤ z → f z = blank) →
      ∀ (node : Tapes 1 prime), Family.NodeFree node → ∀ st : Tapes 2 prime,
      RecursiveStackAllocation.Available 0 st → RecursiveStackAllocation.Available 1 st →
      ∀ x : Fin (volume prime v) → ZMod 2, ∃ c : ℕ,
        (c : ℝ) ≤ C' * volume prime v * (v.width : ℝ) ^ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau ∧
        HoareTime (program capacity)
          (· = bank capacity f p node (Place.memo v.width) (fun _ => st) (wOf K v) v (ext x))
          (· = bank capacity f p node (Place.memo v.width) (fun _ => st) (wOf K v) v
            (ext (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))) c := by
  obtain ⟨C', hC'⟩ := Assembly.core_phase capacity hspec hK hs1 hτ₁ hhalf h2 hlin (D := D) (Nat.cast_nonneg _)
    (toTop capacity) (shear₁ capacity) (shear₂ capacity) (shear₃ capacity) (toLow capacity) (back capacity)
  refine ⟨C', fun v hp he hrows f p hpay node hfree st hdesc hpc x => ?_⟩
  have hq : 0 < prime := Networks.Shared50ModularControl.prime_prime.pos
  have hw : 0 < wOf K v := Stage2Width.atomWidth_pos K _
  have hr := Assembly.rOf_le K v
  have hn := Assembly.nOf_pos hK he
  have htp := Assembly.top_positive (r := rOf K v) hq hp
  have htw := Assembly.top_width K v
  have hvt : volume prime (top prime (rOf K v) v) = volume prime v := Switch.top_volume hr
  have hV := RecursiveAffinePrepare.volume_positive (Nat.Prime.two_le Networks.Shared50ModularControl.prime_prime) v hp
  have c₁ := Switch.toTop_cost hp (w := wOf K v) (Stage2Width.atomWidth_le_self hK he)
  have c₇ := Switch.toLow_cost hp hr
  have c₉ := Switch.back_cost hp hr
  have c₂ := ShearRun.cost_le ShearSem.ops₁ htp hw htw hn
  have c₄ := ShearRun.cost_le ShearSem.ops₂ htp hw htw hn
  have c₆ := ShearRun.cost_le ShearSem.ops₃ htp hw htw hn
  rw [hvt] at c₂ c₄ c₆
  refine hC' v hp he hrows f p hpay node hfree (Place.memo v.width) (fun _ => st) hdesc hpc
    (Switch.toTop_phase (switch_le capacity) v hw)
    (ShearRun.shear_phase (switch_le capacity) (shear_le capacity) htp hw htw hn _ ShearRun.fits₁ ShearSem.lin₁
      (ShearRun.hs₁ _ _))
    (ShearRun.shear_phase (switch_le capacity) (shear_le capacity) htp hw htw hn _ ShearRun.fits₂ ShearSem.lin₂
      (ShearRun.hs₂ _ _))
    (ShearRun.shear_phase (switch_le capacity) (shear_le capacity) htp hw htw hn _ ShearRun.fits₃ ShearSem.lin₃
      (ShearRun.hs₃ _ _))
    (Switch.toLow_phase (switch_le capacity) v hr) (Switch.back_phase (switch_le capacity) v hr) ?_ ?_ x
  · exact switches_le (Nat.lt_size.mpr (by simpa using (show 1 ≤ v.width by omega))) c₁ c₇ c₉ (by unfold D; omega)
  · exact shears_le c₂ c₄ c₆

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreRun
