module

public import IntegerMultBounds.MathlibTM2.Cost.MatchSynLay

/-!
# Cost matching: the synthetic round loops, pipeline facts

Growth facts and the bookkeeping of the round loops `synLoopFCost`, `synLoopOCost`
(`Fast/SynFwd.lean`) at the pipeline parameters, used by `Cost/MatchSynLoop.lean`.

* `mr_b_pow_le_r`: `b^k ≤ r = 2^ℓ` eventually (`b < (d+1)^{2^75}`, `(d+1)^E ≤ 2^d`, `d ≤ ℓ`).
* `mr_p_pow_le_two_pow_K`: `p^k ≤ 2^K` eventually (`eventually_logb_p_le_K`).
* `mr_small_le`: every `x ≤ A (b + 1)^k` is eventually at most `T p`.
* `mr_loops_le`: both loops cost at most `∑_{h < A} synRoundCost h + 6 A² + 14 A + 4`.
* `mr_rounds_split`: a sum over `A ≤ ℓ` rounds of `X + [not a chunk round] Y` is at most
  `A X + (b + 1) Y`, `b = layB ℓ K`: the rounds that are not chunk rounds are `h < b` and
  `h = ℓ - 1`.
* The round parameters: `mr_chunk_facts`, `mr_top_facts`, `mr_low_facts` collect the bounds on
  `synAR`, `synOS`, `synAT`, `synQ`, `synR2` that the `topCost` bound needs.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.Main

/-! ### Growth -/

/-- `b^k ≤ r` eventually. -/
theorem mr_b_pow_le_r (k : ℕ) : ∀ᶠ n in atTop, b n ^ k ≤ r n := by
  have h := tendsto_d.eventually (eventually_mul_pow_le_two_pow (2 ^ (epsExp * k)) (epsExp * k))
  filter_upwards [eventually_big, h] with n hb hd
  have h1 : b n ^ k ≤ (d n + 1) ^ (epsExp * k) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (b_lt_d_succ_pow n).le k
  have h2 : (d n + 1) ^ (epsExp * k) ≤ 2 ^ (epsExp * k) * d n ^ (epsExp * k) := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by have := hb.one_le_d; omega) _
  have h3 : 2 ^ d n ≤ r n := by
    unfold r
    exact Nat.pow_le_pow_right (by norm_num) (by have := hb.d_le_ℓ; omega)
  omega

/-- `p^k ≤ 2^K` eventually. -/
theorem mr_p_pow_le_two_pow_K (k : ℕ) : ∀ᶠ n in atTop, p n ^ k ≤ 2 ^ K n := by
  filter_upwards [eventually_logb_p_le_K k, eventually_big] with n hn hb
  have hp : (0 : ℝ) < p n := mt_p_pos hb
  have e : ((p n : ℕ) : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 (p n)) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hp,
      Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 (p n)) ≤ (2 : ℝ) ^ ((K n : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hn
  rw [Real.rpow_natCast] at h2
  rw [← e] at h2
  exact_mod_cast h2

/-- Every `x ≤ A (b + 1)^k` is eventually at most `T p`. -/
theorem mr_small_le (A k : ℕ) :
    ∀ᶠ n in atTop, ∀ x : ℕ, x ≤ A * (b n + 1) ^ k → (x : ℝ) ≤ (T n : ℝ) * p n := by
  filter_upwards [mt_small_le (A * 2 ^ k) k, eventually_big] with n h hb x hx
  apply h
  have h1 : b n + 1 ≤ 2 * b n := by have := hb.sixteen_le_b; omega
  have h2 : (b n + 1) ^ k ≤ 2 ^ k * b n ^ k := by rw [← mul_pow]; exact Nat.pow_le_pow_left h1 k
  have h3 : A * (b n + 1) ^ k ≤ A * 2 ^ k * b n ^ k := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ h2
  have h4 : A * 2 ^ k * b n ^ k ≤ A * 2 ^ k * b n ^ k * r n :=
    Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
  omega

/-! ### The loops -/

/-- Both loops cost at most the sum of the round costs plus `6 A² + 14 A + 4`. -/
theorem mr_loops_le (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ℓ K w l A stk : ℕ) :
    synLoopFCost ds es ℓ K w l A stk ≤
        (∑ h ∈ Finset.range A, synRoundCost ds es ℓ K w l h stk) + 6 * A ^ 2 + 16 * A + 4 ∧
      synLoopOCost ds es ℓ K w l A stk ≤
        (∑ h ∈ Finset.range A, synRoundCost ds es ℓ K w l h stk) + 6 * A ^ 2 + 16 * A + 4 := by
  have hS : ∀ f : ℕ → ℕ, (∀ j < A, f j ≤ 6 * A + 14) →
      ∑ j ∈ Finset.range A, f j ≤ 6 * A ^ 2 + 14 * A := by
    intro f hf
    calc ∑ j ∈ Finset.range A, f j ≤ ∑ j ∈ Finset.range A, (6 * A + 14) :=
          Finset.sum_le_sum fun j hj => hf j (Finset.mem_range.1 hj)
      _ = 6 * A ^ 2 + 14 * A := by simp; ring
  constructor
  · unfold synLoopFCost
    have e : ∑ j ∈ Finset.range A, ((4 * (A - 1 - j) + 4) +
        synRoundCost ds es ℓ K w l (A - 1 - j) stk + (2 * (A - 1 - j) + 2) + 3) =
        (∑ j ∈ Finset.range A, synRoundCost ds es ℓ K w l (A - 1 - j) stk) +
          ∑ j ∈ Finset.range A, ((4 * (A - 1 - j) + 4) + (2 * (A - 1 - j) + 2) + 3) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have hr : ∑ j ∈ Finset.range A, synRoundCost ds es ℓ K w l (A - 1 - j) stk =
        ∑ h ∈ Finset.range A, synRoundCost ds es ℓ K w l h stk :=
      Finset.sum_range_reflect (fun h => synRoundCost ds es ℓ K w l h stk) A
    have := hS (fun j => (4 * (A - 1 - j) + 4) + (2 * (A - 1 - j) + 2) + 3)
      (fun j hj => by omega)
    omega
  · unfold synLoopOCost
    have e : ∑ j ∈ Finset.range A, ((4 * (j + 1) + 4) + 1 +
        (synTwCost es l w j + synLayerStepCost ds es ℓ K w l j stk) + (2 * j + 2) + 3) =
        (∑ j ∈ Finset.range A, synRoundCost ds es ℓ K w l j stk) +
          ∑ j ∈ Finset.range A, ((4 * (j + 1) + 4) + 1 + (2 * j + 2) + 3) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by unfold synRoundCost; ring
    rw [e]
    have := hS (fun j => (4 * (j + 1) + 4) + 1 + (2 * j + 2) + 3) (fun j hj => by omega)
    omega

/-- The rounds `h < A ≤ ℓ` that are not chunk rounds number at most `layB ℓ K + 1`. -/
theorem mr_card_not_chunk (ℓ K A : ℕ) (hA : A ≤ ℓ) :
    ((Finset.range A).filter fun h => ¬ synChunk ℓ K h).card ≤ layB ℓ K + 1 := by
  calc ((Finset.range A).filter fun h => ¬ synChunk ℓ K h).card
      ≤ (Finset.range (layB ℓ K) ∪ {ℓ - 1}).card := by
        apply Finset.card_le_card
        intro h hh
        rw [Finset.mem_filter, Finset.mem_range] at hh
        rw [Finset.mem_union, Finset.mem_range, Finset.mem_singleton]
        unfold synChunk at hh
        omega
    _ ≤ (Finset.range (layB ℓ K)).card + ({ℓ - 1} : Finset ℕ).card := Finset.card_union_le _ _
    _ = layB ℓ K + 1 := by simp

/-- A sum over `A ≤ ℓ` rounds of `X + [not a chunk round] Y` is at most `A X + (b + 1) Y`. -/
theorem mr_rounds_split {ℓ K A : ℕ} (hA : A ≤ ℓ) (f : ℕ → ℝ) {X Y : ℝ} (hY : 0 ≤ Y) (hf : ∀ h < A, f h ≤ X + if synChunk ℓ K h then 0 else Y) :
    ∑ h ∈ Finset.range A, f h ≤ A * X + (layB ℓ K + 1) * Y := by
  calc ∑ h ∈ Finset.range A, f h
      ≤ ∑ h ∈ Finset.range A, (X + if synChunk ℓ K h then 0 else Y) :=
        Finset.sum_le_sum fun h hh => hf h (Finset.mem_range.1 hh)
    _ = A * X + ∑ h ∈ Finset.range A, (if synChunk ℓ K h then 0 else Y) := by
        rw [Finset.sum_add_distrib]; simp
    _ = A * X + (((Finset.range A).filter fun h => ¬ synChunk ℓ K h).card : ℝ) * Y := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    _ ≤ A * X + (layB ℓ K + 1) * Y := by
        have := mr_card_not_chunk ℓ K A hA
        have h' : (((Finset.range A).filter fun h => ¬ synChunk ℓ K h).card : ℝ) ≤
            layB ℓ K + 1 := by exact_mod_cast this
        nlinarith

/-! ### The round parameters -/

section Params

variable {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K)
include H

theorem mr_length_le_sum : es.length ≤ es.sum := by
  have h2 := H.ℓ_ge
  have : ∀ l : List ℕ, (∀ e ∈ l, 1 ≤ e) → l.length ≤ l.sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        intro h
        simp only [List.length_cons, List.sum_cons]
        have := ih fun e he => h e (by simp [he])
        have := h a (by simp)
        omega
  exact this es fun e he => by rcases H.widths e he with h | h <;> omega

omit H in
theorem mr_synLg_le : synLg es ℓ ≤ es.length := by
  unfold synLg layLongs
  exact (List.length_filter_le _ _).trans (by simp)

/-- The parameters of a chunk round. -/
theorem mr_chunk_facts {h : ℕ} (hc : synChunk ℓ K h) :
    synKh ℓ K h = K ∧ synRh ℓ K h < K ∧ synAR es ℓ K h = synAc es ℓ K ∧
      synAc es ℓ K ≤ es.sum ∧ synQ es ℓ K h = synQK es ∧ synDp es ℓ h = es.length ∧
      synAT es ℓ K h = synOS es ℓ K h + K * synDpp es ∧
      synOS es ℓ K h + K * synDpp es + synAc es ℓ K ≤ es.sum ∧
      synOS es ℓ K h + K * es.length ≤ es.sum ∧
      synR2 es ℓ K h = synR2c es ℓ K ∧ 2 ^ synAc es ℓ K ≤ synR2c es ℓ K ∧
      synR2c es ℓ K < 2 * 2 ^ synAc es ℓ K ∧
      synPcsR es ℓ K h = synPcs K (synX es ℓ K) (synDpp es) (synOS es ℓ K h) (synJp es) (synDpp es) ∧
      synER es ℓ K (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) h =
        synE (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) (synDpp es)
          (synDpp es) := by
  have hK := H.K_pos
  have hfit := synChunk_fit H hc
  have hsplit := synK_mul_split es K
  have hρ : synRh ℓ K h < K := by
    have := synRh_lt (ℓ := ℓ) (h := h) hK
    rwa [show synKh ℓ K h = K by simp [synKh, hc]] at this
  refine ⟨by simp [synKh, hc], hρ, by simp [synAR, hc], ?_, by simp [synQ, hc],
    by simp [synDp, hc.1], by simp [synAT, hc], ?_, by omega, by simp [synR2, hc],
    synR2c_ge es ℓ K hK,
    synR2c_lt es ℓ K hK, by simp [synPcsR, hc], by simp [synER, hc]⟩
  · have := synAR_le H h
    simp [synAR, hc] at this
    exact this
  · unfold synAc; omega

/-- The parameters of a top or low round (not a chunk round). -/
theorem mr_prefix_facts {h : ℕ} (hc : ¬ synChunk ℓ K h) :
    synKh ℓ K h = 1 ∧ synRh ℓ K h = 0 ∧ synAR es ℓ K h = synA es ℓ K ∧
      synA es ℓ K ≤ es.sum ∧ synQ es ℓ K h = synDp es ℓ h ∧ synDp es ℓ h ≤ es.length ∧
      synAT es ℓ K h = synOS es ℓ K h ∧ synOS es ℓ K h + synDp es ℓ h ≤ es.sum ∧
      synR2 es ℓ K h = 2 ^ synA es ℓ K ∧ synPcsR es ℓ K h = [] ∧
      synER es ℓ K (gateCount (program Cost.brDirs)) (factorCount (program Cost.brDirs)) h = 0 := by
  have hA := synA_le H
  have hLg := mr_synLg_le (es := es) (ℓ := ℓ)
  refine ⟨by simp [synKh, hc], by simp [synRh, hc], by simp [synAR, hc], hA, by simp [synQ, hc],
    ?_, by simp [synAT, hc], ?_, by simp [synR2, hc], by simp [synPcsR, hc], by simp [synER, hc]⟩
  · unfold synDp; split_ifs <;> omega
  · unfold synChunk at hc
    unfold synOS synDp
    unfold synA at hA
    by_cases h1 : h + 1 < ℓ
    · have hb : h < layB ℓ K := by omega
      simp only [h1, hb, if_true]
      have h2 : (layB ℓ K - h) * es.length ≤ layB ℓ K * es.length :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have h3 : 1 * es.length ≤ (layB ℓ K - h) * es.length :=
        Nat.mul_le_mul_right _ (by omega)
      generalize (layB ℓ K - h) * es.length = j at h2 h3 ⊢
      generalize layB ℓ K * es.length = f at h2 hA ⊢
      omega
    · simp only [h1, if_false]
      omega

end Params

end IntegerMultBounds.MathlibTM2.Cost
