module

public import IntegerMultBounds.MathlibTM2.M8.Global.Lift

/-! The two gauged side exits are single exchange projectors of rank `506 + rank σ`. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical

/-- Complementing a small global projector stays within the existing frame limit. -/
theorem isFrame_compl_of_bounded {d : Nat} {C : Mat d} (hC : C * C = C)
    (hb : Height.Bounded C (10 ^ 3000)) : IsFrame (1 - C) where
  idem := by simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hC]; abel
  bound i j := by
    have h1 : Height.ht ((1 : Mat d) i j) = 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.sub_apply]
    refine (Height.ht_sub _ _).trans ?_
    rw [h1, mul_one]
    exact (Nat.mul_le_mul_left 2 (hb i j)).trans
      ((two_mul_ten_pow 3000).trans (ten_pow_mono (by norm_num)))

/-- The stage-one terminal frame minus its entrance gauge. -/
theorem lift1_gauge_difference (Q K : LMat) :
    lift1 Q 1 - lift1 Q K = lift1 Q (1 - K) := (kron_sub_left 1 K Q).symm

/-- The stage-two terminal frame minus its entrance gauge. -/
theorem lift2_gauge_difference (P K : LMat) :
    lift2 P (1 - K) - lift2 P 0 = kron P (1 - K) := by
  simp only [lift2, kron_zero_right, add_zero]
  abel

/-- The first side exit is valid without splitting its exchange projector. -/
theorem gauged_exit1_ok {ι : Type} [DecidableEq ι] (i : ι) (fr : ι → Mat 529) (z : ι → Prop)
    {Q K : LMat} (hQ : LFrame Q) (hK : LFrame K) (hcK : LFrame (1 - K))
    (hi : fr i = lift1 Q 1) : (FStep.exit i (lift1 Q 1) (lift1 Q K)).Ok fr z := by
  have hC := isFrame_lift1 hQ hK
  have hb : Height.Bounded (lift1 Q K) (10 ^ 3000) :=
    (kron_bounded hK.bound hQ.bound).mono (by rw [← pow_add]; exact ten_pow_mono (by norm_num))
  have hd : IsFrame (lift1 Q 1 - lift1 Q K) := by
    rw [lift1_gauge_difference]
    exact isFrame_lift1 hQ hcK
  have hn := le_lift1 hQ.idem (show Le K 1 from ⟨by simp, by simp⟩)
  exact ⟨hi, hC, hd, isFrame_compl_of_bounded hC.idem hb, hn.2, hn.1⟩

/-- The reflected side exit has the same single-exchange implementation. -/
theorem gauged_exit2_ok {ι : Type} [DecidableEq ι] (i : ι) (fr : ι → Mat 529) (z : ι → Prop)
    {P K : LMat} (hP : LFrame P) (hcP : LFrame (1 - P)) (hcK : LFrame (1 - K))
    (hi : fr i = lift2 P (1 - K)) : (FStep.exit i (lift2 P (1 - K)) (lift2 P 0)).Ok fr z := by
  have hC := isFrame_lift2 hP lframe_zero
  have hb : Height.Bounded (lift2 P 0) (10 ^ 3000) := by
    rw [lift2_zero]
    exact (kron_bounded hcP.bound lframe_one.bound).mono
      (by rw [← pow_add]; exact ten_pow_mono (by norm_num))
  have hd : IsFrame (lift2 P (1 - K) - lift2 P 0) := by
    rw [lift2_gauge_difference]
    exact isFrame_lift1 hcK hP
  have hn := le_lift2 hP.idem (show Le 0 (1 - K) from ⟨by simp, by simp⟩)
  exact ⟨hi, hC, hd, isFrame_compl_of_bounded hC.idem hb, hn.2, hn.1⟩

/-- Complementary projector ranks add to the local dimension. -/
theorem local_rank_compl {K : LMat} (hK : K * K = K) : (1 - K).rank + K.rank = 23 := by
  simpa only [rank_one, Fintype.card_fin] using
    Exchange.rank_sub_add K 1 hK (Matrix.one_mul 1) (by simp) (by simp)

/-- Complementary lifted projector ranks add to the node width. -/
theorem kron_rank_compl {A B : LMat} (hA : A * A = A) (hB : B * B = B) :
    (1 - kron A B).rank + A.rank * B.rank = 529 := by
  have hi : kron A B * kron A B = kron A B := by rw [kron_mul, hA, hB]
  have h := Exchange.rank_sub_add (kron A B) 1 hi (Matrix.one_mul 1) (by simp) (by simp)
  simpa only [rank_one, Fintype.card_fin, kron_rank hA hB] using h

theorem gauged_exit1_rank {Q K : LMat} (hQ : Q * Q = Q) (hK : K * K = K) (hr : Q.rank = 1) :
    (1 - (lift1 Q 1 - lift1 Q K)).rank = 506 + K.rank := by
  rw [lift1_gauge_difference]
  have hc : (1 - K) * (1 - K) = 1 - K := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hK]; abel
  have h := kron_rank_compl hc hQ
  rw [hr, Nat.mul_one] at h
  have hk := local_rank_compl hK
  change (1 - kron (1 - K) Q).rank = _
  omega

theorem gauged_exit2_rank {P K : LMat} (hP : P * P = P) (hK : K * K = K) (hr : P.rank = 1) :
    (1 - (lift2 P (1 - K) - lift2 P 0)).rank = 506 + K.rank := by
  rw [lift2_gauge_difference]
  have hc : (1 - K) * (1 - K) = 1 - K := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hK]; abel
  have h := kron_rank_compl hP hc
  rw [hr, Nat.one_mul] at h
  have hk := local_rank_compl hK
  omega

/-- An entrance gauge followed by its complementary exit reads the transposed address. -/
theorem swapAt_complement {d p : Nat} (hp : p.Prime) (hpb : coefficientBound < p) (b : Nat)
    {C : Mat d} (hC : IsFrame C) (a : Address d (p ^ b)) :
    swapAt (p ^ b) C (swapAt (p ^ b) (1 - C) a) = swapAt (p ^ b) 1 a := by
  have hc := frame_admissible hp hpb b hC
  have h1 := frame_admissible hp hpb b (isFrame_one (d := d))
  simp only [swapAt]
  rw [exchange_exchange, reduce_sub _ h1 hc, Swap.Modular.reduce_one, Matrix.mul_sub,
    Matrix.mul_one, reduce_idem hp hpb b hC, sub_self, smul_zero, sub_zero, add_sub_cancel]

end
end IntegerMultBounds.MathlibTM2.M8.Global
