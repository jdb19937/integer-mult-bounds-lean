module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlTarget
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlExposeRotation
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlRouting
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateLayout
public import IntegerMultBounds.MathlibTM2.Cost.CRTControlAllFibers
public import IntegerMultBounds.MathlibTM2.Cost.CRTControlProducer
public import IntegerMultBounds.MathlibTM2.Cost.CRTReverse
public import IntegerMultBounds.MathlibTM2.Cost.DirectScale

/-! # Cost matching for a complete runtime CRT target step -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
  IntegerMultBounds.MathlibTM2.Fast TableVM

noncomputable section

/-- Actual distant exposure includes header construction and destruction and
fits the full-volume interchange budget at the full address width. -/
theorem crtControlDistantCost_le {Tm u g h w c L am : ℕ}
    (hL : u + h + g + w = L) (hh : h ≤ am) (hw : w ≤ am) :
    crtControlDistantCost Tm u g h w c ≤ crtStepBound Tm L c (2 ^ L * c) am := by
  have hpair := crtReversePairCost_le (T := Tm) (B := c)
    (pre := u) (gap := g) (post := 0) (aj := h) (ak := w) (by omega) hh hw
  apply le_trans ?_ hpair
  unfold crtControlDistantCost crtReversePairCost
  simp only [Nat.add_zero]
  rw [show u + (h + (g + w)) = u + h + g + w by omega]
  omega

/-- A target's exposure and unexposure are exactly two distant interchange
budgets, independent of the number of axes between the endpoint pair. -/
theorem crtControlDistantPairCost_le {Tm u g h w c L am : ℕ}
    (hL : u + h + g + w = L) (hh : h ≤ am) (hw : w ≤ am) :
    crtControlDistantCost Tm u g h w c + crtControlDistantCost Tm u g w h c ≤
      2 * crtStepBound Tm L c (2 ^ L * c) am := by
  have h₁ := crtControlDistantCost_le (Tm := Tm) (c := c) hL hh hw
  have h₂ := crtControlDistantCost_le (Tm := Tm) (c := c) (u := u) (g := g)
    (show u + w + g + h = L by omega) hw hh
  omega

/-- All target exposure pairs use only a linear number of interchanges. -/
theorem crtControlDistantPairs_total {N : ℕ} (Tm c L am : ℕ)
    (u g h w : Fin N → ℕ) (hL : ∀ i, u i + h i + g i + w i = L)
    (hh : ∀ i, h i ≤ am) (hw : ∀ i, w i ≤ am) :
    (∑ i, (crtControlDistantCost Tm (u i) (g i) (h i) (w i) c +
      crtControlDistantCost Tm (u i) (g i) (w i) (h i) c)) ≤
      2 * N * crtStepBound Tm L c (2 ^ L * c) am := by
  calc
    _ ≤ ∑ _ : Fin N, 2 * crtStepBound Tm L c (2 ^ L * c) am :=
      Finset.sum_le_sum fun i _ => crtControlDistantPairCost_le (hL i) (hh i) (hw i)
    _ = _ := by simp; ring

/-- Match the executable paired exposures to the linear-axis pipeline scale. -/
theorem crtControlDistantPairs_pipeline_le (Tm cw : ℕ) {n : ℕ} (hb : Big n)
    (c : ℕ) (hc : c ≤ cw * p n) (u g h w : Fin (d n) → ℕ)
    (hL : ∀ i, u i + h i + g i + w i = logT n)
    (hh : ∀ i, h i ≤ ℓ n) (hw : ∀ i, w i ≤ ℓ n) :
    ((∑ i, (crtControlDistantCost Tm (u i) (g i) (h i) (w i) c +
      crtControlDistantCost Tm (u i) (g i) (w i) (h i) c)) : ℝ) ≤
      2 * mtCrtReverseC Tm cw *
        ((T n : ℝ) * p n * d n * (1 + (ℓ n : ℝ) ^ Parameters.tau)) := by
  have hn := crtControlDistantPairs_total Tm c (logT n) (ℓ n) u g h w hL hh hw
  have hbudget : 2 * d n * crtStepBound Tm (logT n) c (2 ^ logT n * c) (ℓ n) ≤
      2 * crtReverseBudget Tm (logT n) c (d n) (ℓ n) := by
    unfold crtReverseBudget
    nlinarith
  have hcast := (Nat.cast_le (α := ℝ)).2 (hn.trans hbudget)
  have hrev := mt_crt_reverse_le Tm cw hb c (ℓ n) hc le_rfl
  push_cast at hcast
  linarith
/-- The exposed rotation's exact cost is the checked all-fibers cost plus
its actual ten-variable workspace initialization and restoration. -/
theorem crtControlExposedCost_eq (D B w L ai S c : ℕ) :
    crtControlExposedCost D B w (L - ai) ai S c =
      crtControlAllFibersCost D (3 * B + 1) w S L ai c +
        crtControlWorkspaceOverhead (3 * B + 1) w := by
  unfold crtControlExposedCost crtControlAllFibersCost crtControlWorkspaceOverhead
  omega

/-- The complete exposed rotations use a linear number of coefficient passes,
including initialization and restoration of the arithmetic workspace. -/
theorem crtControlExposedCost_pipeline_le (cw : ℕ) :
    ∀ᶠ n in atTop, ∀ a D B w S : Fin (d n) → ℕ, ∀ c : ℕ,
      (∀ i, a i ≤ logT n) → (∀ i, a i = ℓ n ∨ a i = ℓ n - 1) →
      (∀ i, D i ≤ logT n) → (∀ i, B i ≤ logT n) →
      (∀ i, w i ≤ 3 * B i + 1) → (∀ i, S i ≤ 2 ^ a i) → c ≤ cw * p n →
      (∑ i, crtControlExposedCost (D i) (B i) (w i) (logT n - a i) (a i) (S i) c) ≤
        2 ^ 21 * (cw + 1) * d n * T n * p n := by
  filter_upwards [crtControlAllWorkspace_pipeline_le cw] with n h a D B w S c ha hwidth hD hB hw hS hc
  have hb := h a D (fun i => 3 * B i + 1) w S (fun _ => c) ha hwidth hD
    (fun i => by have := hB i; omega) hw hS (fun _ => hc)
  apply le_trans ?_ hb
  apply Finset.sum_le_sum
  intro i _
  rw [crtControlExposedCost_eq]
  omega

/-- Full original address width, without a list representation conversion. -/
theorem crtControl_fullWidth {d : ℕ} (a : Fin d → ℕ) :
    crtPre a d = ∑ j, a j := by simp [crtPre, crtLow]

/-- Exposing one target removes exactly its width from the physical prefix. -/
theorem crtControl_exposeWidth {d : ℕ} (a : Fin (d + 1) → ℕ) (i : Fin (d + 1)) :
    crtW a (crtExposePrefix i) = (∑ j, a j) - a i := by
  have h := crtControlGeneratedAxes_width a i (d + 1) le_rfl
  rw [crtControlGeneratedAxes_full, crtControl_fullWidth] at h
  simpa [show ¬d + 1 ≤ i.val by omega] using h

/-- Distant exposure traverses the full original box volume. -/
theorem crtControl_routingWidth {d : ℕ} (a : Fin (d + 1) → ℕ) (i : Fin (d + 1)) (hi : i ≠ 0) :
    crtW a (crtControlRoutingPre i) + a i + crtW a (crtControlRoutingGap i) + a 0 = ∑ j, a j := by
  have h := crtW_revAx a (d + 1) le_rfl
  rw [crtRevAx_eq_outer, crtControlRouting_split i hi, crtControl_fullWidth] at h
  simpa [crtW_append, crtW_cons, Nat.add_assoc] using h

/-- One descriptor per spectator, with four fixed-width words per descriptor. -/
theorem crtControl_descriptorLength {d A : ℕ} (W : ℕ) (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) :
    (crtControlTape (A := A) W (crtControlFields a s i.val (crtExposePrefix i))).length = d * (4 * W) := by
  have hfields : ∀ o : List (Fin (d + 1)), (crtControlFields a s i.val o).length = o.length := by
    intro o
    induction o with
    | nil => rfl
    | cons j o ih => simpa only [crtControlFields, List.length_cons] using congrArg Nat.succ ih
  rw [crtControlTape_length, hfields]
  simp [crtExposePrefix, crtAxisExchange, crtOuterAxes]

/-- Every non-data operation in the actual target step: parameters, descriptor
production, unary gap creation, and the actual six-tape cleanup. -/
def crtControlTargetAuxCost {d K : ℕ} (B w : ℕ) (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (μ : ℕ) : ℕ :=
  crtControlParametersSetupCost (3 * B + 1) w (s i) μ (a i) (crtPre a (d + 1)) +
  crtControlProducerCost (3 * B + 1) w i.val (a i) (a 0) (crtPre a i.val)
    (crtEnts (A := IntegerMultBounds.Networks.Shared50ModularControl.prime + K) (List.ofFn a)).length
    (crtEnts (A := IntegerMultBounds.Networks.Shared50ModularControl.prime + K) (List.ofFn s)).length
    (List.ofFn a).sum (d + 1) (crtControlProducerAxisBudget (3 * B + 1) w a s) +
  (4 * crtPre a i.val + 4 * a 0 + 8) +
  (6 * (2 * crtControlTargetClearBound (K := K) B a s i + 2) + 1)

/-- Exact separation of target routing/rotation from bounded auxiliary work. -/
theorem crtControlTargetCost_eq {d K : ℕ} (Tm B w c : ℕ) (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (μ : ℕ) :
    crtControlTargetCost (K := K) Tm B w c a s i μ =
      crtControlTargetAuxCost (K := K) B w a s i μ +
      (crtControlDistantCost Tm (crtW a (crtControlRoutingPre i)) (crtW a (crtControlRoutingGap i)) (a i) (a 0) c +
        crtControlDistantCost Tm (crtW a (crtControlRoutingPre i)) (crtW a (crtControlRoutingGap i)) (a 0) (a i) c) +
      crtControlExposedCost (crtControlFields a s i.val (crtExposePrefix i)).length B w
        (crtW a (crtExposePrefix i)) (a i) (s i) c := by
  unfold crtControlTargetCost crtControlTargetAuxCost
  omega

/-- Match all actual target auxiliaries, including the coarse shared cleanup
bound, to one radix times cubic address-width polynomial. -/
theorem crtControlTargetAuxCost_le {d K L w radix : ℕ} (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (μ : ℕ) (hL : (∑ j, a j) = L) (hd : d + 1 ≤ L)
    (hw : w ≤ 3 * L + 1) (hs : ∀ j, s j ≤ radix)
    (hμ : μ ≤ radix) (hr : 2 ^ a i ≤ radix) (hrad : 1 ≤ radix) :
    crtControlTargetAuxCost (K := K) L w a s i μ ≤ 2 ^ 22 * radix * (L + 1) ^ 3 := by
  have ha : ∀ j, a j ≤ L := fun j =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hL.le
  have hp : crtPre a i.val ≤ L := (crtControl_pre_le_sum a i.val).trans hL.le
  have hfull : crtPre a (d + 1) = L := (crtControl_fullWidth a).trans hL
  have hparams := crtControlParametersCost_le le_rfl hw (ha i) (hs i) hμ hr
  have hproducer := crtControlProducer_actualCost_le (A := IntegerMultBounds.Networks.Shared50ModularControl.prime + K)
    a s i le_rfl hw hL.le hd hs hrad
  have hclear : crtControlTargetClearBound (K := K) L a s i ≤
      12 * (L + 1) ^ 2 + 4 * (L + 1) + radix := by
    unfold crtControlTargetClearBound
    rw [crtControl_descriptorLength, hfull]
    have hm := Nat.mul_le_mul_right (4 * (3 * L + 1)) (show d ≤ L by omega)
    nlinarith
  have hsq : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hcube : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by nlinarith [Nat.mul_le_mul_left (L + 1) hsq]
  have hradcube : (L + 1) ^ 3 ≤ radix * (L + 1) ^ 3 := Nat.le_mul_of_pos_left _ hrad
  have hradsmall : radix ≤ radix * (L + 1) ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
  have hradpow : radix * (L + 1) ^ 2 ≤ radix * (L + 1) ^ 3 := Nat.mul_le_mul_left _ hcube
  unfold crtControlParametersCost at hparams
  unfold crtControlTargetAuxCost
  rw [hfull]
  norm_num at hparams hproducer ⊢
  have ha0 := ha 0
  nlinarith

/-- Number of descriptor packets in the exposed prefix. -/
theorem crtControl_descriptorCount {d : ℕ} (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1)) :
    (crtControlFields a s i.val (crtExposePrefix i)).length = d := by
  have h := crtControl_descriptorLength (A := 0) 1 a s i
  rw [crtControlTape_length] at h
  omega

/-- A polynomial auxiliary budget per target is absorbed after summing every
actual runtime target, including unary routing-gap construction and clearing. -/
theorem crtControlTargetAuxBudget_pipeline_le :
    ∀ᶠ n in atTop, ∀ C : Fin (d n) → ℕ,
      (∀ j, C j ≤ 2 ^ 22 * r n * (logT n + 1) ^ 3) → (∑ j, C j) ≤ T n := by
  filter_upwards [mt_poly_r_le_T (2 ^ 25) 4, eventually_big] with n hpoly hb C hC
  have hL : logT n + 1 ≤ 2 * b n := by
    have := mt_logT_le_b hb
    have := hb.sixteen_le_b
    omega
  have hd := d_le_b n
  have hpoint : ∀ j, C j ≤ 2 ^ 25 * b n ^ 3 * r n := by
    intro j
    calc
      _ ≤ 2 ^ 22 * r n * (logT n + 1) ^ 3 := hC j
      _ ≤ 2 ^ 22 * r n * (2 * b n) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 3)
      _ = _ := by ring
  calc
    _ ≤ ∑ _ : Fin (d n), 2 ^ 25 * b n ^ 3 * r n := Finset.sum_le_sum fun j _ => hpoint j
    _ = d n * (2 ^ 25 * b n ^ 3 * r n) := by simp
    _ ≤ b n * (2 ^ 25 * b n ^ 3 * r n) := Nat.mul_le_mul_right _ hd
    _ = 2 ^ 25 * b n ^ 4 * r n := by ring
    _ ≤ T n := hpoly

/-- Explicit coefficient for all nonzero target steps. -/
def mtCrtControlTargetC (Tm cw : ℕ) : ℝ :=
  2 * mtCrtReverseC Tm cw + 2 ^ 21 * (cw + 1)

/-- Actual complete unary-input target programs have one axis factor. Every
parameter, descriptor, routing-gap and cleanup charge is included in the
separate one-volume auxiliary term. -/
theorem crtControlTarget_pipeline_le (Tm cw K : ℕ) :
    ∀ᶠ n in atTop, ∀ m w c : ℕ, ∀ a s μ : Fin (m + 1) → ℕ,
      m + 1 = d n → (∑ j, a j) = logT n →
      (∀ j, a j = ℓ n ∨ a j = ℓ n - 1) →
      (∀ j, s j ≤ 2 ^ a j) → (∀ j, μ j ≤ s j) →
      w ≤ 3 * logT n + 1 → c ≤ cw * p n →
      (((∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1))),
        crtControlTargetCost (K := K) Tm (logT n) w c a s i (μ i)) : ℕ) : ℝ) ≤
      mtCrtControlTargetC Tm cw * totDirectCRT n + T n := by
  filter_upwards [crtControlTargetAuxBudget_pipeline_le, crtControlExposedCost_pipeline_le cw,
    eventually_big] with n haux hrotation hb m w c a s μ hdim hL hwidth hs hμ hw hc
  have hapos : ∀ i, 1 ≤ a i := by
    intro i
    have := hb.two_le_ℓ
    rcases hwidth i with h | h <;> omega
  have hcount : m + 1 ≤ logT n := by
    calc
      _ = ∑ _ : Fin (m + 1), 1 := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => hapos i
      _ = _ := hL
  have ha : ∀ i, a i ≤ logT n := fun i =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hL.le
  have ham : ∀ i, a i ≤ ℓ n := by intro i; rcases hwidth i with h | h <;> omega
  have hrad : ∀ i, 2 ^ a i ≤ r n := fun i => Nat.pow_le_pow_right (by decide) (ham i)
  have hsrad : ∀ i, s i ≤ r n := fun i => (hs i).trans (hrad i)
  have hμrad : ∀ i, μ i ≤ r n := fun i => (hμ i).trans (hsrad i)
  rw [← hdim] at haux hrotation
  let I := Finset.univ.erase (0 : Fin (m + 1))
  let aux := fun i => crtControlTargetAuxCost (K := K) (logT n) w a s i (μ i)
  let pair := fun i =>
    crtControlDistantCost Tm (crtW a (crtControlRoutingPre i)) (crtW a (crtControlRoutingGap i)) (a i) (a 0) c +
    crtControlDistantCost Tm (crtW a (crtControlRoutingPre i)) (crtW a (crtControlRoutingGap i)) (a 0) (a i) c
  let rot := fun i => crtControlExposedCost (crtControlFields a s i.val (crtExposePrefix i)).length
    (logT n) w (crtW a (crtExposePrefix i)) (a i) (s i) c
  have hauxAll : (∑ i, aux i) ≤ T n := haux aux (fun i =>
    crtControlTargetAuxCost_le a s i (μ i) hL hcount hw hsrad (hμrad i) (hrad i) Nat.one_le_two_pow)
  have hauxI : (∑ i ∈ I, aux i) ≤ T n :=
    (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)).trans hauxAll
  have hrotAll : (∑ i, rot i) ≤ 2 ^ 21 * (cw + 1) * d n * T n * p n := by
    have hr := hrotation a (fun _ => m) (fun _ => logT n) (fun _ => w) s c ha hwidth
      (fun _ => by omega) (fun _ => le_rfl) (fun _ => hw) hs hc
    simpa only [rot, crtControl_descriptorCount, crtControl_exposeWidth, hL, hdim] using hr
  have hrotI : (∑ i ∈ I, rot i) ≤ 2 ^ 21 * (cw + 1) * d n * T n * p n :=
    (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)).trans hrotAll
  have hpair : (∑ i ∈ I, pair i) ≤ 2 * crtReverseBudget Tm (logT n) c (d n) (ℓ n) := by
    have hpoint : ∀ i ∈ I, pair i ≤ 2 * crtStepBound Tm (logT n) c (2 ^ logT n * c) (ℓ n) := by
      intro i hi
      have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
      exact crtControlDistantPairCost_le ((crtControl_routingWidth a i hi0).trans hL) (ham i) (ham 0)
    calc
      _ ≤ ∑ _ ∈ I, 2 * crtStepBound Tm (logT n) c (2 ^ logT n * c) (ℓ n) :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ _ : Fin (m + 1), 2 * crtStepBound Tm (logT n) c (2 ^ logT n * c) (ℓ n) :=
        Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      _ = 2 * d n * crtStepBound Tm (logT n) c (2 ^ logT n * c) (ℓ n) := by simp [hdim]; ring
      _ ≤ _ := by unfold crtReverseBudget; nlinarith
  have hrev := mt_crt_reverse_le Tm cw hb c (ℓ n) hc le_rfl
  have hA := (Nat.cast_le (α := ℝ)).2 hauxI
  have hR := (Nat.cast_le (α := ℝ)).2 hrotI
  have hP := (Nat.cast_le (α := ℝ)).2 hpair
  push_cast at hA hR hP
  have hscale : (d n : ℝ) * T n * p n ≤
      (T n : ℝ) * p n * d n * (1 + (ℓ n : ℝ) ^ Parameters.tau) := by
    have hpos := Real.rpow_nonneg (Nat.cast_nonneg (ℓ n)) Parameters.tau
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (T n : ℝ) * p n * d n by positivity) hpos]
  have hscaled := mul_le_mul_of_nonneg_left hscale (show (0 : ℝ) ≤ 2 ^ 21 * (cw + 1) by positivity)
  have hsum : (∑ i ∈ I, crtControlTargetCost (K := K) Tm (logT n) w c a s i (μ i)) =
      (∑ i ∈ I, aux i) + (∑ i ∈ I, pair i) + (∑ i ∈ I, rot i) := by
    simp only [crtControlTargetCost_eq, Finset.sum_add_distrib, aux, pair, rot]
  change ((_ : ℕ) : ℝ) ≤ _
  rw [hsum]
  push_cast
  unfold mtCrtControlTargetC totDirectCRT
  nlinarith


end
end IntegerMultBounds.MathlibTM2.Cost
