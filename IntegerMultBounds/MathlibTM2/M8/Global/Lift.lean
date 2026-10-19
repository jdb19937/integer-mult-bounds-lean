module

public import IntegerMultBounds.MathlibTM2.M8.Global.Auto
public import IntegerMultBounds.MathlibTM2.M8.Exchange

/-!
# Lifting local frames to the node

The node's `529 = 23 · 23` address coordinates are the tensor product of two local factors
(`kron`). Stage one lifts a local frame `K` of invocation `T` to `K ⊗ Q` (`lift1 Q K`), with `Q`
the line of `T` on the second factor; stage two lifts `K` of invocation `S` to
`(1 − P) ⊗ 1 + P ⊗ K` (`lift2 P K`), with `P` the line of `S` on the first factor. A local frame
is an idempotent of height at most `10 ^ 300` (`LFrame`). Both lifts send local frames to frames
(`isFrame_lift1`, `isFrame_lift2`), keep nesting (`le_lift1`, `le_lift2`) and keep the ranks of
nested differences when `Q` and `P` have rank one (`rank_lift1_sub`, `rank_lift2_sub`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open Matrix
open scoped Kronecker

/-- Local matrices: one factor of the node's coordinates. -/
abbrev LMat := Matrix (Fin 23) (Fin 23) ℚ

/-- The node's coordinates as pairs of local coordinates. -/
abbrev e529 : Fin 23 × Fin 23 ≃ Fin 529 := finProdFinEquiv

/-- The tensor product of two local matrices. -/
def kron (A B : LMat) : Mat 529 := Matrix.reindexAlgEquiv ℚ ℚ e529 (A ⊗ₖ B)

theorem kron_apply (A B : LMat) (i j : Fin 529) :
    kron A B i j = A (e529.symm i).1 (e529.symm j).1 * B (e529.symm i).2 (e529.symm j).2 := rfl

theorem kron_mul (A B C D : LMat) : kron A B * kron C D = kron (A * C) (B * D) := by
  rw [kron, kron, kron, ← map_mul, mul_kronecker_mul]

theorem kron_sub_left (A A' B : LMat) : kron (A - A') B = kron A B - kron A' B := by
  ext i j; simp only [kron_apply, Matrix.sub_apply, sub_mul]

theorem kron_sub_right (A B B' : LMat) : kron A (B - B') = kron A B - kron A B' := by
  ext i j; simp only [kron_apply, Matrix.sub_apply, mul_sub]

theorem kron_add_right (A B B' : LMat) : kron A (B + B') = kron A B + kron A B' := by
  ext i j; simp only [kron_apply, Matrix.add_apply, mul_add]

theorem kron_add_left (A A' B : LMat) : kron (A + A') B = kron A B + kron A' B := by
  ext i j; simp only [kron_apply, Matrix.add_apply, add_mul]

theorem kron_zero_left (B : LMat) : kron 0 B = 0 := by
  ext i j; simp [kron_apply]

theorem kron_zero_right (A : LMat) : kron A 0 = 0 := by
  ext i j; simp [kron_apply]

theorem kron_one_one : kron 1 1 = 1 := by
  rw [kron, one_kronecker_one, map_one]

theorem kron_rank {A B : LMat} (hA : A * A = A) (hB : B * B = B) :
    (kron A B).rank = A.rank * B.rank := by
  rw [kron, coe_reindexAlgEquiv, rank_reindex]
  exact (Exchange.rank_kronecker A B hA hB).2

theorem kron_bounded {A B : LMat} {a b : ℕ} (hA : Height.Bounded A a) (hB : Height.Bounded B b) :
    Height.Bounded (kron A B) (a * b) := fun i j => by
  rw [kron_apply]
  exact (Height.ht_mul _ _).trans (Nat.mul_le_mul (hA _ _) (hB _ _))

/-! ### Local frames -/

theorem ten_pow_mono {a b : ℕ} (h : a ≤ b) : (10 : ℕ) ^ a ≤ 10 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem two_mul_ten_pow (a : ℕ) : 2 * (10 : ℕ) ^ a ≤ 10 ^ (a + 1) := by
  rw [pow_succ]; omega

/-- A local frame: an idempotent with entries of height at most `10 ^ 300`. -/
structure LFrame (K : LMat) : Prop where
  idem : K * K = K
  bound : Height.Bounded K (10 ^ 300)

theorem ht_one_apply (i j : Fin 23) : Height.ht ((1 : LMat) i j) = 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem bounded_one_sub {K : LMat} {b : ℕ} (hb : Height.Bounded K b) :
    Height.Bounded (1 - K) (2 * b) := fun i j => by
  rw [Matrix.sub_apply]
  refine (Height.ht_sub _ _).trans ?_
  rw [ht_one_apply, mul_one]
  exact Nat.mul_le_mul_left 2 (hb i j)

theorem lframe_zero : LFrame (0 : LMat) :=
  ⟨by simp, fun i j => by simp only [Matrix.zero_apply, Height.ht_zero]; exact Nat.one_le_pow _ _ (by norm_num)⟩

theorem lframe_one : LFrame (1 : LMat) :=
  ⟨by simp, fun i j => by rw [ht_one_apply]; exact Nat.one_le_pow _ _ (by norm_num)⟩

theorem lframe_compl {K : LMat} (hK : K * K = K) (hb : Height.Bounded K (10 ^ 200)) :
    LFrame (1 - K) := by
  refine ⟨by simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hK]; abel,
    fun i j => ?_⟩
  exact ((bounded_one_sub hb) i j).trans ((two_mul_ten_pow 200).trans (ten_pow_mono (by norm_num)))

theorem lframe_of {K : LMat} (hK : K * K = K) (hb : Height.Bounded K (10 ^ 200)) : LFrame K :=
  ⟨hK, hb.mono (ten_pow_mono (by norm_num))⟩

/-! ### The two lifts -/

/-- Stage one: `K ⊗ Q`. -/
def lift1 (Q K : LMat) : Mat 529 := kron K Q

/-- Stage two: `(1 − P) ⊗ 1 + P ⊗ K`. -/
def lift2 (P K : LMat) : Mat 529 := kron (1 - P) 1 + kron P K

theorem isFrame_lift1 {Q K : LMat} (hQ : LFrame Q) (hK : LFrame K) : IsFrame (lift1 Q K) where
  idem := by rw [lift1, kron_mul, hK.idem, hQ.idem]
  bound := (kron_bounded hK.bound hQ.bound).mono (by rw [← pow_add]; exact ten_pow_mono (by norm_num))

theorem lift2_mul {P : LMat} (hP : P * P = P) (A B : LMat) :
    lift2 P A * lift2 P B = lift2 P (A * B) := by
  have h1 : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP]; abel
  have h2 : (1 - P) * P = 0 := by simp [Matrix.sub_mul, hP]
  have h3 : P * (1 - P) = 0 := by simp [Matrix.mul_sub, hP]
  simp only [lift2, Matrix.add_mul, Matrix.mul_add, kron_mul, h1, h2, h3, hP, kron_zero_left,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]

theorem isFrame_lift2 {P K : LMat} (hP : LFrame P) (hK : LFrame K) : IsFrame (lift2 P K) where
  idem := by rw [lift2_mul hP.idem, hK.idem]
  bound := fun i j => by
    rw [lift2, Matrix.add_apply]
    refine (Height.ht_add _ _).trans ?_
    have h1 := kron_bounded (bounded_one_sub hP.bound) lframe_one.bound i j
    have h2 := kron_bounded hP.bound hK.bound i j
    calc 2 * Height.ht (kron (1 - P) 1 i j) * Height.ht (kron P K i j)
        ≤ 2 * (2 * 10 ^ 300 * 10 ^ 300) * (10 ^ 300 * 10 ^ 300) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
      _ = 4 * 10 ^ 1200 := by rw [← pow_add, Nat.mul_assoc 2 (10 ^ 300), ← pow_add]; ring
      _ ≤ 10 * 10 ^ 1200 := Nat.mul_le_mul_right _ (by norm_num)
      _ = 10 ^ 1201 := (pow_succ' 10 1200).symm
      _ ≤ 10 ^ 4000 := ten_pow_mono (by norm_num)

theorem le_lift1 {Q : LMat} (hQ : Q * Q = Q) {A B : LMat} (h : Le A B) :
    Le (lift1 Q A) (lift1 Q B) :=
  ⟨by rw [lift1, lift1, kron_mul, h.1, hQ], by rw [lift1, lift1, kron_mul, h.2, hQ]⟩

theorem le_lift2 {P : LMat} (hP : P * P = P) {A B : LMat} (h : Le A B) :
    Le (lift2 P A) (lift2 P B) :=
  ⟨by rw [lift2_mul hP, h.1], by rw [lift2_mul hP, h.2]⟩

theorem cmp_lift1 {Q : LMat} (hQ : Q * Q = Q) {A B : LMat} (h : Cmp A B) :
    Cmp (lift1 Q A) (lift1 Q B) :=
  h.elim (fun h => Or.inl (le_lift1 hQ h)) (fun h => Or.inr (le_lift1 hQ h))

theorem cmp_lift2 {P : LMat} (hP : P * P = P) {A B : LMat} (h : Cmp A B) :
    Cmp (lift2 P A) (lift2 P B) :=
  h.elim (fun h => Or.inl (le_lift2 hP h)) (fun h => Or.inr (le_lift2 hP h))

theorem lift1_zero (Q : LMat) : lift1 Q 0 = 0 := kron_zero_left Q

theorem lift2_one (P : LMat) : lift2 P 1 = 1 := by
  rw [lift2, ← kron_add_left, sub_add_cancel, kron_one_one]

theorem lift2_zero (P : LMat) : lift2 P 0 = kron (1 - P) 1 := by
  rw [lift2, kron_zero_right, add_zero]

theorem lift2_compl (P K : LMat) : lift2 P (1 - K) = 1 - kron P K := by
  rw [lift2, kron_sub_right, ← lift2_one P, lift2]
  abel

/-! ### Ranks of lifted differences -/

theorem rank_lift1_sub {Q A B : LMat} (hQ : Q * Q = Q) (hA : A * A = A) (hB : B * B = B)
    (h : Le A B) : (lift1 Q B - lift1 Q A).rank = (B - A).rank * Q.rank := by
  rw [lift1, lift1, ← kron_sub_left,
    kron_rank (Exchange.sub_idempotent A B hA hB h.1 h.2) hQ]

theorem rank_lift2_sub {P A B : LMat} (hP : P * P = P) (hA : A * A = A) (hB : B * B = B)
    (h : Le A B) : (lift2 P B - lift2 P A).rank = P.rank * (B - A).rank := by
  rw [lift2, lift2, add_sub_add_left_eq_sub, ← kron_sub_right,
    kron_rank hP (Exchange.sub_idempotent A B hA hB h.1 h.2)]

end

end IntegerMultBounds.MathlibTM2.M8.Global
