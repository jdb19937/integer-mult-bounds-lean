module

public import IntegerMultBounds.MathlibTM2.Cost.CRTControlGenerate
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlProducer

/-! # Cost matching for the complete runtime descriptor producer -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
  IntegerMultBounds.MathlibTM2.Fast TableVM

/-- Unary entry restoration includes both separators on every runtime entry. -/
theorem crtControlEntries_length {A : ℕ} (a : List ℕ) :
    (crtEnts (A := A) a).length = a.sum + 2 * a.length := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    simp [crtEnts_cons, crtEnt, ih]
    omega

/-- The actual finite maximum of per-axis costs has the common radix-polynomial bound. -/
theorem crtControlProducerAxisBudget_le {N W w L radix : ℕ}
    (a s e : Fin N → ℕ) (hW : W ≤ 3 * L + 1) (hw : w ≤ W)
    (ha : ∀ j, a j ≤ L) (hs : ∀ j, s j ≤ radix) (he : ∀ j, e j ≤ L) :
    Finset.univ.sup (fun j => crtControlGenerateAxisCost W w (a j) (s j) (e j) (4 * W)) ≤
      2 ^ 14 * (radix + 1) * (L + 1) ^ 2 := by
  apply Finset.sup_le
  intro j _
  exact (crtControlGenerateAxisCost_le hW hw (ha j) (he j) le_rfl).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hs j) 1)))

/-- All charged producer operations, including bank restoration and eventual
descriptor disposal, fit a radix times cubic address-width polynomial. -/
theorem crtControlProducerBudget_le {W w N i ai a0 pre widthsLen moduliLen widthSum axisBudget L radix : ℕ}
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W) (hN : N ≤ L)
    (hi : i ≤ L) (hai : ai ≤ L) (ha0 : a0 ≤ L) (hpre : pre ≤ L)
    (hwidths : widthsLen ≤ L + 2 * N) (hmoduli : moduliLen ≤ N * (radix + 2))
    (hsum : widthSum ≤ L) (hrad : 1 ≤ radix)
    (haxis : axisBudget ≤ 2 ^ 14 * (radix + 1) * (L + 1) ^ 2) :
    crtControlGenerateSetupCost W w i ai a0 pre + (4 * i + 4) +
      (N * (axisBudget + 2) + 2 + (2 * widthsLen + 2) + (2 * moduliLen + 2) +
        (2 * widthSum + 2) + 4) + (10 * (2 * W + 2) + 1) +
      (2 * (4 * W * (N - 1)) + 2) ≤ 2 ^ 20 * radix * (L + 1) ^ 3 := by
  have hsetup := crtControlGenerateSetupCost_le hW hw hi hai ha0 hpre
  let K := L + 1
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hNK : N ≤ K := by dsimp [K]; omega
  have hLK : L ≤ K := by dsimp [K]; omega
  have hWK : W ≤ 3 * K := by dsimp [K]; omega
  have hsq : K ≤ K ^ 2 := by nlinarith
  have hcube : K ^ 2 ≤ K ^ 3 := by nlinarith [Nat.mul_le_mul_left K hsq]
  have hradcube : K ^ 3 ≤ radix * K ^ 3 := Nat.le_mul_of_pos_left _ hrad
  have hradK : radix * K ≤ radix * K ^ 3 := Nat.mul_le_mul_left _ (hsq.trans hcube)
  have hwidthsK : widthsLen ≤ 3 * K := by omega
  have hmoduliK : moduliLen ≤ 3 * radix * K := by
    calc
      _ ≤ N * (radix + 2) := hmoduli
      _ ≤ K * (3 * radix) := Nat.mul_le_mul hNK (by omega)
      _ = _ := by ring
  have haxisK : axisBudget ≤ 2 ^ 15 * radix * K ^ 2 := by
    calc
      _ ≤ 2 ^ 14 * (radix + 1) * K ^ 2 := haxis
      _ ≤ 2 ^ 14 * (2 * radix) * K ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring
  have hloop : N * (axisBudget + 2) ≤ 2 ^ 16 * radix * K ^ 3 := by
    calc
      _ ≤ K * (2 ^ 15 * radix * K ^ 2 + 2) :=
        Nat.mul_le_mul hNK (Nat.add_le_add_right haxisK 2)
      _ ≤ _ := by norm_num; nlinarith
  have hdispose : W * (N - 1) ≤ 3 * K ^ 2 := by
    calc
      _ ≤ (3 * K) * K := Nat.mul_le_mul hWK (by omega)
      _ = _ := by ring
  change _ ≤ 2 ^ 20 * radix * K ^ 3
  change crtControlGenerateSetupCost W w i ai a0 pre ≤ 2 ^ 14 * K ^ 3 at hsetup
  norm_num at hsetup hloop ⊢
  nlinarith

/-- Summing the complete per-target producer/disposal budget is eventually
absorbed by one padded volume, with no data-volume scan hidden in the cost. -/
theorem crtControlProducerBudget_pipeline_le :
    ∀ᶠ n in atTop, ∀ C : Fin (d n) → ℕ,
      (∀ j, C j ≤ 2 ^ 20 * r n * (logT n + 1) ^ 3) → (∑ j, C j) ≤ T n := by
  filter_upwards [mt_poly_r_le_T (2 ^ 23) 4, eventually_big] with n hpoly hb C hC
  have hL : logT n + 1 ≤ 2 * b n := by
    have := mt_logT_le_b hb
    have := hb.sixteen_le_b
    omega
  have hd := d_le_b n
  have hpoint : ∀ j, C j ≤ 2 ^ 23 * b n ^ 3 * r n := by
    intro j
    calc
      _ ≤ 2 ^ 20 * r n * (logT n + 1) ^ 3 := hC j
      _ ≤ 2 ^ 20 * r n * (2 * b n) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 3)
      _ = _ := by ring
  calc
    _ ≤ ∑ _ : Fin (d n), 2 ^ 23 * b n ^ 3 * r n := Finset.sum_le_sum fun j _ => hpoint j
    _ = d n * (2 ^ 23 * b n ^ 3 * r n) := by simp
    _ ≤ b n * (2 ^ 23 * b n ^ 3 * r n) := Nat.mul_le_mul_right _ hd
    _ = 2 ^ 23 * b n ^ 4 * r n := by ring
    _ ≤ T n := hpoly

/-- Match the budget of the checked complete producer program, with disposal
of its descriptor tape when the destination was initially empty. -/
theorem crtControlProducerCost_le {W w N i ai a0 pre widthsLen moduliLen widthSum axisBudget L radix : ℕ}
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W) (hN : N ≤ L)
    (hi : i ≤ L) (hai : ai ≤ L) (ha0 : a0 ≤ L) (hpre : pre ≤ L)
    (hwidths : widthsLen ≤ L + 2 * N) (hmoduli : moduliLen ≤ N * (radix + 2))
    (hsum : widthSum ≤ L) (hrad : 1 ≤ radix)
    (haxis : axisBudget ≤ 2 ^ 14 * (radix + 1) * (L + 1) ^ 2) :
    crtControlProducerCost W w i ai a0 pre widthsLen moduliLen widthSum N axisBudget +
      (2 * (4 * W * (N - 1)) + 2) ≤ 2 ^ 20 * radix * (L + 1) ^ 3 := by
  exact crtControlProducerBudget_le hW hw hN hi hai ha0 hpre hwidths hmoduli hsum hrad haxis

/-- The cost in the full executable producer theorem, with its actual unary
stream lengths and actual finite maximum, has the claimed cubic budget. -/
theorem crtControlProducer_actualCost_le {d W w L radix A : ℕ}
    (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1))
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W)
    (hL : (∑ j, a j) ≤ L) (hd : d + 1 ≤ L)
    (hs : ∀ j, s j ≤ radix) (hrad : 1 ≤ radix) :
    crtControlProducerCost W w i.val (a i) (a 0) (crtPre a i.val)
      (crtEnts (A := A) (List.ofFn a)).length (crtEnts (A := A) (List.ofFn s)).length
      (List.ofFn a).sum (d + 1) (crtControlProducerAxisBudget W w a s) +
      (2 * (4 * W * d) + 2) ≤ 2 ^ 20 * radix * (L + 1) ^ 3 := by
  have ha : ∀ j, a j ≤ L := fun j =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hL
  have hpre : ∀ j, crtPre a j ≤ L := fun j => (crtControl_pre_le_sum a j).trans hL
  have hsumS : (∑ j, s j) ≤ (d + 1) * radix := by
    calc
      _ ≤ ∑ _ : Fin (d + 1), radix := Finset.sum_le_sum fun j _ => hs j
      _ = _ := by simp
  apply crtControlProducerCost_le hW hw hd (by have := i.isLt; omega)
    (ha i) (ha 0) (hpre i.val)
  · rw [crtControlEntries_length]
    simpa only [List.sum_ofFn, List.length_ofFn] using Nat.add_le_add_right hL (2 * (d + 1))
  · rw [crtControlEntries_length]
    simp only [List.sum_ofFn, List.length_ofFn]
    nlinarith
  · simpa only [List.sum_ofFn] using hL
  · exact hrad
  · exact crtControlProducerAxisBudget_le a s (fun j => crtPre a j.val) hW hw ha hs (fun j => hpre j.val)

/-- All checked complete producers, including descriptor disposal, cost at
most one padded volume eventually. The producer is repeated once per target. -/
theorem crtControlProducer_pipeline_le :
    ∀ᶠ n in atTop, ∀ W w target ai a0 pre widthsLen moduliLen widthSum axisBudget : Fin (d n) → ℕ,
      d n ≤ logT n →
      (∀ j, W j ≤ 3 * logT n + 1) → (∀ j, w j ≤ W j) →
      (∀ j, target j ≤ logT n) → (∀ j, ai j ≤ logT n) →
      (∀ j, a0 j ≤ logT n) → (∀ j, pre j ≤ logT n) →
      (∀ j, widthsLen j ≤ logT n + 2 * d n) →
      (∀ j, moduliLen j ≤ d n * (r n + 2)) → (∀ j, widthSum j ≤ logT n) →
      (∀ j, axisBudget j ≤ 2 ^ 14 * (r n + 1) * (logT n + 1) ^ 2) →
      (∑ j : Fin (d n), (crtControlProducerCost (W j) (w j) (target j) (ai j) (a0 j) (pre j)
        (widthsLen j) (moduliLen j) (widthSum j) (d n) (axisBudget j) +
          (2 * (4 * W j * (d n - 1)) + 2))) ≤ T n := by
  filter_upwards [crtControlProducerBudget_pipeline_le] with n hbudget W w target ai a0 pre widthsLen
    moduliLen widthSum axisBudget hd hW hw ht hai ha0 hp hwidths hmoduli hsum haxis
  apply hbudget
  intro j
  exact crtControlProducerCost_le (hW j) (hw j) hd (ht j) (hai j) (ha0 j) (hp j)
    (hwidths j) (hmoduli j) (hsum j) Nat.one_le_two_pow (haxis j)

end IntegerMultBounds.MathlibTM2.Cost
