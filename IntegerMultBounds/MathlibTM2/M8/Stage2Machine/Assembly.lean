module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Leaf
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Pad
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Cost
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearRun

/-!
# The stage-2 core with its family runs and leaf

The core's bank (`bank`) is the common bank at the view, with the array on the I/O role, the
family's resting counters at the atom width `w = atomWidth K e` and a PC stack per view, padded
to the tapes of both the family's machine and the leaf core (`tW`). The two family runs are
`FamilyStep.program` on the top view and the leaf is `LeafCore.core` on the low view, both
padded (`famP`, `leafP`). `core_phase`: given the header switches and the shears with their
contracts, the core transposes the array of every positive view of width `e ≥ 2` whose rows split
over the family's depth, within a constant times `V e^τ₂`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Assembly

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
open SharedBankFamily (padProgram)
open Stage2Wrapper (Moves shear top low)
open Stage2Width (atomWidth tau2)
open RevMachine
open FamilyRoot (ext FamilySpec bound)
open Core (Phase)

/-! ### Views -/

theorem top_volume {q r : ℕ} {v : Descriptor} (hr : r ≤ v.width) : volume q (top q r v) = volume q v := by
  have he : q ^ v.width = q ^ (v.width - r) * q ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
  simp only [volume, top, he]
  ring

theorem low_volume {q r : ℕ} {v : Descriptor} (hr : r ≤ v.width) : volume q (low q r v) = volume q v := by
  have he : q ^ v.width = q ^ (v.width - r) * q ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
  simp only [volume, low, he]
  ring

theorem top_positive {q r : ℕ} (hq : 0 < q) {v : Descriptor} (hp : v.Positive) : (top q r v).Positive :=
  ⟨hp.1, hp.2.1, hp.2.2.1, Nat.mul_pos (pow_pos hq r) hp.2.2.2.1, Nat.mul_pos (pow_pos hq r) hp.2.2.2.2⟩

theorem low_positive {q r : ℕ} (hq : 0 < q) {v : Descriptor} (hp : v.Positive) : (low q r v).Positive :=
  ⟨hp.1, hp.2.1, Nat.mul_pos hp.2.2.1 (pow_pos hq _), Nat.mul_pos hp.2.2.2.1 (pow_pos hq _), hp.2.2.2.2⟩

theorem bits_le_size {w : ℕ} (hw : 1 ≤ w) : (bits w).length ≤ Nat.size w := by
  have h := GrowingCounterData.empty_width w
  have hs : w.log2 < Nat.size w := Nat.lt_size.mpr (Nat.log2_self_le (by omega))
  exact h.trans hs

/-! ### The atom width -/

local instance (w : ℕ) : NeZero (prime ^ w) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

/-- The atom width of a view. -/
def wOf (K : ℕ) (v : Descriptor) : ℕ := atomWidth K v.width

/-- The atom count of a view. -/
def nOf (K : ℕ) (v : Descriptor) : ℕ := v.width / wOf K v

/-- The residual digits of a view. -/
def rOf (K : ℕ) (v : Descriptor) : ℕ := v.width % wOf K v

theorem rOf_le (K : ℕ) (v : Descriptor) : rOf K v ≤ v.width := Nat.mod_le _ _

theorem rOf_lt (K : ℕ) (v : Descriptor) : rOf K v < wOf K v := Nat.mod_lt _ (Stage2Width.atomWidth_pos K _)

theorem top_width (K : ℕ) (v : Descriptor) : (top prime (rOf K v) v).width = nOf K v * wOf K v := by
  have := Nat.div_add_mod v.width (wOf K v)
  simp only [top, rOf, nOf]
  rw [Nat.mul_comm]
  omega

theorem nOf_pos {K : ℕ} (hK : 2 ≤ K) {v : Descriptor} (he : 2 ≤ v.width) : 1 ≤ nOf K v :=
  Nat.div_pos (Stage2Width.atomWidth_le_self hK he) (Stage2Width.atomWidth_pos K _)

/-! ### The bank -/

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

/-- The core's tapes: the family's, the leaf's and room for the switches and shears. -/
abbrev tW := FamilyStep.tF capacity + (LeafCore.core (NodeBank.io rev97m)).tapes + (ShearRun.T' + 24)

theorem tF_le : FamilyStep.tF capacity ≤ tW capacity := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

theorem core_le : (LeafCore.core (NodeBank.io rev97m)).tapes ≤ tW capacity :=
  (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)

theorem count_le : CommonBank.count (NodeBank.tapes rev97m) ≤ FamilyStep.tF capacity :=
  SharedBankFamily.common_le_tapeCount _

theorem switch_le : CommonBank.count (NodeBank.tapes rev97m) + 22 ≤ tW capacity := by
  have := count_le capacity; unfold tW; omega

theorem shear_le : CommonBank.count (NodeBank.tapes rev97m) + (ShearRun.T' + 2) ≤ tW capacity := by
  have := count_le capacity; unfold tW; omega

/-- **The core's bank** at the view `u`, atom width `w` and PC stacks `S`. -/
def bank (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (S : Descriptor → Tapes 2 prime)
    (w : ℕ) (u : Descriptor) (X : ℕ → ZMod 2) : Tapes (tW capacity) prime :=
  raw (Leaf.leafBank f p node scalar (Prepare.rest w 529) (S u) u X) (tW capacity)

theorem bank_local (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (S : Descriptor → Tapes 2 prime) (w : ℕ) : Core.Local (bank capacity f p node scalar S w) := by
  intro u X Y h
  unfold bank Leaf.leafBank FamilyStep.rolesAt
  congr 3
  funext i
  exact h i i.isLt

/-- The family run on the core's tapes. -/
def famP := padProgram (FamilyStep.program capacity) (tF_le capacity)

/-- The leaf on the core's tapes. -/
def leafP := padProgram (LeafCore.core (NodeBank.io rev97m)).program (core_le capacity)

/-- **The family run** on the core's bank. -/
theorem fam_phase (hspec : FamilySpec capacity) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℕ, ∀ L : ℝ, 1 ≤ L → ((bits w).length : ℝ) ≤ L →
      ((max 1 w : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
      ∀ (u : Descriptor) (n : ℕ), u.Positive → 0 < w → u.width = n * w → 1 ≤ n →
      rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) n ∣ u.rows →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ), (∀ z, p ≤ z → f z = blank) →
      ∀ (node : Tapes 1 prime), Family.NodeFree node → ∀ (scalar : Tapes 1 prime) (S : Descriptor → Tapes 2 prime),
      RecursiveStackAllocation.Available 0 (S u) → RecursiveStackAllocation.Available 1 (S u) →
      Phase (famP capacity) (bank capacity f p node scalar S w) u u (RevT prime w n u)
        (k + 1 + ⌊bound C L n * volume prime u⌋₊) := by
  obtain ⟨C, hC, hF⟩ := FamilyStep.family_step capacity hspec
  refine ⟨C, hC, fun w L hL hℓ hτ u n hpos hw hwn hn hrows f p hpay node hfree scalar S hdesc hpc => ?_⟩
  have h := hF w L hL hℓ hτ u n hpos hw hwn hn hrows f p hpay node hfree scalar (S u) hdesc hpc
  have h' : Phase (FamilyStep.program capacity)
      (fun u' X => raw (Leaf.leafBank f p node scalar (Prepare.rest w 529) (S u) u' X) (FamilyStep.tF capacity))
      u u (RevT prime w n u) _ := h
  exact (Pad.pad_step (tF_le capacity) (SharedBankFamily.common_le_tapeCount _) h').congr
    (fun _ => rfl) (fun _ => rfl)

/-- **The leaf** on the core's bank. -/
theorem leaf_phase (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (S : Descriptor → Tapes 2 prime) (w : ℕ) {u : Descriptor} (hpos : u.Positive) :
    Phase (leafP capacity) (bank capacity f p node scalar S w) u u (Moves prime u Prod.swap)
      (M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (Routines.hdr u)) :=
  (Pad.pad_step (core_le capacity) (SharedBankFamily.common_le _)
    (Leaf.leaf_phase f p node scalar (Prepare.rest w 529) (S u) hpos)).congr (fun _ => rfl) (fun _ => rfl)

omit [M8.Machine.Net] in
/-- The core's cost, from the costs of its pieces. -/
theorem core_cost {K : ℕ} (hK : 2 ≤ K) {τ : ℝ} (hs1 : Cost.tauS ≤ τ) (hτ₁ : τ ≤ 1) (hhalf : 1 / 2 ≤ τ)
    (h2 : 1 / 2 ≤ tau2 (K : ℝ)⁻¹ Cost.tauS τ) (hlin : 1 - (K : ℝ)⁻¹ ≤ tau2 (K : ℝ)⁻¹ Cost.tauS τ)
    {C D C₁ V : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hC₁ : 0 ≤ C₁) (j : ℕ) (hV : 1 ≤ V) {e : ℕ} (he : 2 ≤ e)
    {c₁ c₂ c₄ c₆ c₇ c₈ c₉ F : ℕ}
    (hh : (c₁ + c₇ + c₉ : ℝ) ≤ D * Nat.size e * V)
    (hs : (c₂ + c₄ + c₆ : ℝ) ≤ D * ((e / atomWidth K e : ℕ) + 1) * V)
    (hF : (F : ℝ) ≤ bound C ((atomWidth K e : ℝ) ^ τ + Nat.size (atomWidth K e)) (e / atomWidth K e) * V)
    (hl : (c₈ : ℝ) ≤ C₁ * V * (atomWidth K e : ℝ) ^ τ) :
    ((c₁ + 1 + c₂ + 1 + (j + 1 + F) + 1 + c₄ + 1 + (j + 1 + F) + 1 + c₆ + 1 + c₇ + 1 + c₈ + 1 + c₉ : ℕ) : ℝ) ≤
      Cost.constant C (D + 2 * (j + 1) + C₁) * V * (e : ℝ) ^ tau2 (K : ℝ)⁻¹ Cost.tauS τ := by
  have hse : (1 : ℝ) ≤ Nat.size e := by
    exact_mod_cast Nat.lt_size.mpr (by simpa using (show 1 ≤ e by omega))
  have hj : (0 : ℝ) ≤ 2 * (j + 1) := by positivity
  have hsV : 1 ≤ Nat.size e * V := by nlinarith
  have hnV : 0 ≤ (((e / atomWidth K e : ℕ) : ℝ) + 1) * V := by positivity
  have hwV : 0 ≤ (atomWidth K e : ℝ) ^ τ * V := by
    have := Real.rpow_nonneg (Nat.cast_nonneg (atomWidth K e)) τ; positivity
  have hbound := Cost.core_le hK hs1 hτ₁ hhalf h2 hlin hC (D := D + 2 * (j + 1) + C₁) (by positivity) hV he
    (c₁ := c₁ + (j + 1) + (j + 1)) (c₂ := c₂) (c₃ := F) (c₄ := c₄) (c₅ := F) (c₆ := c₆) (c₇ := c₇) (c₈ := c₈) (c₉ := c₉)
    (by push_cast; nlinarith) (by nlinarith) (by linarith) (by nlinarith)
  refine le_trans (le_of_eq ?_) hbound
  push_cast
  ring

/-- **The stage-2 core.** Given the header switches and the shears, with their contracts and
costs, the core interchanges the array of every positive view of width `e ≥ 2` whose rows split
over the family's depth, within a constant times `V e^τ₂`. -/
theorem core_phase (hspec : FamilySpec capacity) {K : ℕ} (hK : 2 ≤ K)
    (hs1 : Cost.tauS ≤ M8.Machine.BudgetBound.tau) (hτ₁ : M8.Machine.BudgetBound.tau ≤ 1)
    (hhalf : 1 / 2 ≤ M8.Machine.BudgetBound.tau)
    (h2 : 1 / 2 ≤ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau)
    (hlin : 1 - (K : ℝ)⁻¹ ≤ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau)
    {D : ℝ} (hD : 0 ≤ D) {s₁ s₂ s₄ s₆ s₇ s₉ : ℕ} (toTop : Program (tW capacity) s₁ prime)
    (shear₁ : Program (tW capacity) s₂ prime) (shear₂ : Program (tW capacity) s₄ prime)
    (shear₃ : Program (tW capacity) s₆ prime) (toLow : Program (tW capacity) s₇ prime)
    (back : Program (tW capacity) s₉ prime) :
    ∃ C' : ℝ, ∀ v : Descriptor, v.Positive → 2 ≤ v.width →
      rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) (nOf K v) ∣ v.rows →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ), (∀ z, p ≤ z → f z = blank) →
      ∀ (node : Tapes 1 prime), Family.NodeFree node → ∀ (scalar : Tapes 1 prime) (S : Descriptor → Tapes 2 prime),
      RecursiveStackAllocation.Available 0 (S (top prime (rOf K v) v)) →
      RecursiveStackAllocation.Available 1 (S (top prime (rOf K v) v)) →
      ∀ {c₁ c₂ c₄ c₆ c₇ c₉ : ℕ},
      Phase toTop (bank capacity f p node scalar S (wOf K v)) v (top prime (rOf K v) v) Eq c₁ →
      Phase shear₁ (bank capacity f p node scalar S (wOf K v)) (top prime (rOf K v) v) (top prime (rOf K v) v)
        (Moves prime (top prime (rOf K v) v) (shear (prime ^ wOf K v) (nOf K v) fun h d => d - h)) c₂ →
      Phase shear₂ (bank capacity f p node scalar S (wOf K v)) (top prime (rOf K v) v) (top prime (rOf K v) v)
        (Moves prime (top prime (rOf K v) v) (shear (prime ^ wOf K v) (nOf K v) fun h d => d + h)) c₄ →
      Phase shear₃ (bank capacity f p node scalar S (wOf K v)) (top prime (rOf K v) v) (top prime (rOf K v) v)
        (Moves prime (top prime (rOf K v) v) (shear (prime ^ wOf K v) (nOf K v) fun h d => h - d)) c₆ →
      Phase toLow (bank capacity f p node scalar S (wOf K v)) (top prime (rOf K v) v) (low prime (rOf K v) v) Eq c₇ →
      Phase back (bank capacity f p node scalar S (wOf K v)) (low prime (rOf K v) v) v Eq c₉ →
      (c₁ + c₇ + c₉ : ℝ) ≤ D * Nat.size v.width * volume prime v →
      (c₂ + c₄ + c₆ : ℝ) ≤ D * ((nOf K v : ℝ) + 1) * volume prime v →
      ∀ x : Fin (volume prime v) → ZMod 2, ∃ c : ℕ,
        (c : ℝ) ≤ C' * volume prime v * (v.width : ℝ) ^ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau ∧
        HoareTime (Core.core toTop shear₁ (famP capacity) shear₂ (famP capacity) shear₃ toLow (leafP capacity) back)
          (· = bank capacity f p node scalar S (wOf K v) v (ext x))
          (· = bank capacity f p node scalar S (wOf K v) v
            (ext (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))) c := by
  obtain ⟨C, hC, hF⟩ := fam_phase capacity hspec
  obtain ⟨C₁, hC₁, hU⟩ := M8.Machine.ArbitraryWidthOriginalTotalRun.uniform_bound
  refine ⟨Cost.constant C (D + 2 * (k + 1) + C₁), fun v hp he hrows f p hpay node hfree scalar S hdesc hpc
    c₁ c₂ c₄ c₆ c₇ c₉ h₁ h₂ h₄ h₆ h₇ h₉ hh hs x => ?_⟩
  have hq : 0 < prime := Networks.Shared50ModularControl.prime_prime.pos
  have hw1 : 1 ≤ wOf K v := Stage2Width.atomWidth_pos K _
  obtain ⟨hL1, hLs, hLτ, -⟩ := Stage2Width.wrapped_le hK Cost.tauS_nonneg hs1 hτ₁ hhalf h2 hlin
    (A := 0) (B := 0) (D := 0) le_rfl le_rfl le_rfl he
  have hbits : ((bits (wOf K v)).length : ℝ) ≤ (wOf K v : ℝ) ^ M8.Machine.BudgetBound.tau + Nat.size (wOf K v) :=
    (by exact_mod_cast bits_le_size hw1 : ((bits (wOf K v)).length : ℝ) ≤ Nat.size (wOf K v)).trans hLs
  have hmax : ((max 1 (wOf K v) : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤
      (wOf K v : ℝ) ^ M8.Machine.BudgetBound.tau + Nat.size (wOf K v) := by
    rw [max_eq_right hw1]; exact hLτ
  have hfam := hF (wOf K v) _ hL1 hbits hmax (top prime (rOf K v) v) (nOf K v) (top_positive hq hp) hw1
    (top_width K v) (nOf_pos hK he) hrows f p hpay node hfree scalar S hdesc hpc
  have hleaf := leaf_phase capacity f p node scalar S (wOf K v) (low_positive (r := rOf K v) hq hp)
  have hcore := Core.core_hoare (rOf_le K v) (top_width K v) h₁ h₂ hfam h₄ hfam h₆ h₇ hleaf h₉
  refine ⟨_, ?_, Core.transpose_hoare (bank_local capacity f p node scalar S (wOf K v)) hcore x⟩
  have hV : (1 : ℝ) ≤ volume prime v := by
    exact_mod_cast RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le v hp
  have htop : volume prime (top prime (rOf K v) v) = volume prime v := top_volume (rOf_le K v)
  have hlow : volume prime (low prime (rOf K v) v) = volume prime v := low_volume (rOf_le K v)
  have hbnd : 0 ≤ bound C ((wOf K v : ℝ) ^ M8.Machine.BudgetBound.tau + Nat.size (wOf K v)) (nOf K v) := by
    unfold bound
    have := Cost.one_sub_q₁; have := Cost.one_sub_qτ
    have : 0 ≤ ((nOf K v : ℕ) : ℝ) ^ (1 - (Stage2Moments.savingB : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hF' := (Nat.floor_le (mul_nonneg hbnd (Nat.cast_nonneg (volume prime (top prime (rOf K v) v))))).trans
    (le_of_eq (by rw [htop]))
  have hcl := hU (low prime (rOf K v) v) (Routines.hdr (low prime (rOf K v) v)) (low_positive hq hp)
    (Routines.hdr_headers _)
  rw [hlow] at hcl
  have hrw : ((max 1 (low prime (rOf K v) v).width : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤
      (wOf K v : ℝ) ^ M8.Machine.BudgetBound.tau :=
    Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (show max 1 (low prime (rOf K v) v).width ≤ wOf K v from max_le hw1 (rOf_lt K v).le))
      M8.Machine.BudgetBound.exponent_range.1.le
  have hl : ((M8.Machine.ArbitraryWidthOriginalTotalRun.cost (low prime (rOf K v) v)
      (Routines.hdr (low prime (rOf K v) v)) : ℕ) : ℝ) ≤
      C₁ * volume prime v * (wOf K v : ℝ) ^ M8.Machine.BudgetBound.tau :=
    hcl.trans (mul_le_mul_of_nonneg_left hrw (by positivity))
  exact core_cost hK hs1 hτ₁ hhalf h2 hlin hC hD hC₁.le k hV he hh hs hF' hl

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Assembly
