module

public import IntegerMultBounds.MathlibTM2.M8.ExchangeProgram

/-!
# The coefficients of the exchange program are bounded

`factors U` is the height-bounded factorization (`Height.exists_bounded_univ`), so every number
the reduction of `program U` must avoid (`numbers U`) and every coefficient of its operations
(`opCoeffs`) has height at most `2 ^ numbersE U` (`numbers_le`, `program_coeffs_le`), with
`numbersE U = max (expOf U) (14 N³ (facE U + 1))`.

For matrices of size at most `529` whose entries have numerators and denominators at most
`10 ^ 10000`, all of these are at most `Networks.coefficientBound = 2 ^ 2 ^ 2 ^ 16`
(`numbers_le_coefficientBound`, `program_coeffs_le_coefficientBound`). A prime beyond that bound
therefore serves every such matrix (`specialize_run_of_bound`). The comparisons go through
exponents; no tower is evaluated.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Exchange

noncomputable section
open Matrix Finset
open IntegerMultBounds.Networks
open IntegerMultBounds.Swap.Shear (State LowerTriangular pivotMatrix)
open IntegerMultBounds.Swap.Modular (ratMod reduce Admissible denominators)
open Height (ht Bounded)

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

local notation "N" => Fintype.card ι

/-- The factor exponent of `U`. -/
def facE (U : Matrix ι ι ℚ) : ℕ := Height.FE N (2 * N) (expOf U)

/-- The exponent bounding every number of `U`. -/
def numbersE (U : Matrix ι ι ℚ) : ℕ := max (expOf U) (max (facE U) (14 * N ^ 3 * (facE U + 1)))

omit [Fintype ι] [LinearOrder ι] in
theorem bounded_pivot [DecidableEq ι] (L : List (ι × ι)) (hL : L.Nodup) :
    Bounded (pivotMatrix L : Matrix ι ι ℚ) (2 ^ 0) := fun i j => by
  rw [Swap.PivotRank.pivotMatrix_apply L hL]
  split_ifs <;> simp

theorem bounded_corr (U : Matrix ι ι ℚ) (hN : 1 ≤ N) :
    Bounded (corr U) (2 ^ (14 * N ^ 3 * (facE U + 1))) := by
  obtain ⟨h₁, _, h₂, _⟩ := factors_bounded U
  have hP := bounded_pivot (factors U).L ((factors U).nodup₁.of_map _)
  have hPt := Height.bounded_transpose hP
  have hM := Height.bounded_mul h₂ h₁
  have hPPt := Height.bounded_mul hP hPt
  have hPtP := Height.bounded_mul hPt hP
  have t1 := Height.bounded_mul hM hPPt
  have t2 := Height.bounded_mul hPtP hM
  have t3 := Height.bounded_mul t2 hPPt
  have k := Height.bounded_sub (Height.bounded_add (Height.bounded_sub t1 t2) t3) hPt
  refine k.pow_mono ?_
  change _ ≤ 14 * N ^ 3 * (Height.FE N (2 * N) (expOf U) + 1)
  set e := Height.FE N (2 * N) (expOf U)
  have hN2 : N ≤ N ^ 2 := by nlinarith
  have hN3 : N ^ 2 ≤ N ^ 3 := by nlinarith
  nlinarith [Nat.zero_le e, Nat.zero_le (N * e), Nat.zero_le (N ^ 2 * e)]

omit [LinearOrder ι] in
theorem facE_le_numbersE (U : Matrix ι ι ℚ) : facE U ≤ numbersE U :=
  le_max_of_le_right (le_max_left _ _)

omit [LinearOrder ι] in
theorem corrE_le_numbersE (U : Matrix ι ι ℚ) : 14 * N ^ 3 * (facE U + 1) ≤ numbersE U :=
  le_max_of_le_right (le_max_right _ _)

omit [Fintype ι] [LinearOrder ι] in
theorem ht_le_of_bounded {A : Matrix ι ι ℚ} {a b : ℕ} (hA : Bounded A (2 ^ a)) (hab : a ≤ b)
    (i j : ι) : ht (A i j) ≤ 2 ^ b :=
  (hA.pow_mono hab) i j

omit [LinearOrder ι] in
theorem den_mem_le {A : Matrix ι ι ℚ} {a b : ℕ} (hA : Bounded A (2 ^ a)) (hab : a ≤ b) {d : ℕ}
    (hd : d ∈ denominators A) : d ≤ 2 ^ b := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hd
  exact (Height.den_le_ht _).trans (ht_le_of_bounded hA hab p.1 p.2)

omit [Fintype ι] [LinearOrder ι] in
theorem bounded_map_inv {A : Matrix ι ι ℚ} {h : ℕ} (hA : Bounded A h) :
    Bounded (A.map (·⁻¹)) h := fun i j => by
  rw [map_apply, Height.ht_inv]; exact hA i j

/-- **Bounded numbers.** -/
theorem numbers_le (U : Matrix ι ι ℚ) (hN : 1 ≤ N) : ∀ d ∈ numbers U, d ≤ 2 ^ numbersE U := by
  obtain ⟨h₁, h₁', h₂, h₂'⟩ := factors_bounded U
  have hf : facE U ≤ numbersE U := facE_le_numbersE U
  have hK := bounded_corr U hN
  have hk : 14 * N ^ 3 * (facE U + 1) ≤ numbersE U := corrE_le_numbersE U
  have hU : expOf U ≤ numbersE U := le_max_left _ _
  intro d hd
  simp only [numbers, Swap.Modular.factorizationDenominators, Finset.mem_union] at hd
  rcases hd with (((((((((hd | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd))
  · exact den_mem_le (bounded_expOf U) hU hd
  · exact den_mem_le h₁ hf hd
  · exact den_mem_le h₁' hf hd
  · exact den_mem_le h₂ hf hd
  · exact den_mem_le h₂' hf hd
  · exact den_mem_le hK hk hd
  · exact den_mem_le (bounded_map_inv hK) hk hd
  · exact den_mem_le (Height.bounded_neg hK) hk hd
  · exact den_mem_le (bounded_map_inv (Height.bounded_neg hK)) hk hd

/-! ### Coefficients of the operations -/

/-- The rational coefficients of a field operation. -/
def opCoeffs : AffineFieldProgram.Op ι ℚ → List ℚ
  | .affineH (.scale _ a) => [a]
  | .affineH (.shift _ _ a) => [a]
  | .affineD (.scale _ a) => [a]
  | .affineD (.shift _ _ a) => [a]
  | .addToD _ _ => [1]
  | .subFromD _ _ => [1, -1]
  | .interchange _ _ => []

theorem transformOps_coeffs {A B : Matrix ι ι ℚ} {h : ℕ} (hA : Bounded A h) (hB : Bounded B h) :
    ∀ op ∈ transformOps A B, ∀ r ∈ opCoeffs op, ht r ≤ h := by
  intro op hop r hr
  obtain ⟨src, hsrc, hin⟩ := List.mem_flatMap.mp hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsrc
  rcases hsrc with rfl | rfl
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hin
    rcases OrderedAffine.coefficient_origin A a ha with ⟨i, rfl⟩ | ⟨i, j, _, rfl⟩ <;>
      simp only [opCoeffs, List.mem_singleton] at hr <;> subst hr <;> exact hA _ _
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hin
    rcases OrderedAffine.coefficient_origin B a ha with ⟨i, rfl⟩ | ⟨i, j, _, rfl⟩ <;>
      simp only [opCoeffs, List.mem_singleton] at hr <;> subst hr <;> exact hB _ _

omit [LinearOrder ι] in
theorem crossQ_coeffs {K : Matrix ι ι ℚ} {h : ℕ} (hK : Bounded K h) (h1 : 1 ≤ h) :
    ∀ op ∈ crossQ K, ∀ r ∈ opCoeffs op, ht r ≤ h := by
  intro op hop r hr
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hop
  split_ifs at hp
  · simp at hp
  · simp only [crossEntry, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [opCoeffs, List.mem_singleton] at hr <;> subst hr
    · rw [Height.ht_inv]; exact hK _ _
    · simpa using h1
    · exact hK _ _

/-- Every coefficient of `program U` has height at most `2 ^ numbersE U`. -/
theorem program_coeffs_le (U : Matrix ι ι ℚ) (hN : 1 ≤ N) :
    ∀ op ∈ program U, ∀ r ∈ opCoeffs op, ht r ≤ 2 ^ numbersE U := by
  obtain ⟨h₁, h₁', h₂, h₂'⟩ := factors_bounded U
  have hf : facE U ≤ numbersE U := facE_le_numbersE U
  have hK := (bounded_corr U hN).pow_mono (corrE_le_numbersE U)
  have h1 : 1 ≤ 2 ^ numbersE U := Nat.one_le_two_pow
  intro op hop r hr
  simp only [program, exchangeOps, List.mem_append] at hop
  rcases hop with (((h | h) | h) | h) | h
  · exact transformOps_coeffs (h₁'.pow_mono hf) (h₂.pow_mono hf) op h r hr
  · exact crossQ_coeffs hK h1 op h r hr
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    simp [opCoeffs] at hr
  · exact crossQ_coeffs (Height.bounded_neg hK) h1 op h r hr
  · exact transformOps_coeffs (h₁.pow_mono hf) (h₂'.pow_mono hf) op h r hr

/-! ### The literal bound -/

omit [LinearOrder ι] in
/-- For size at most `529` and entries with numerators and denominators at most `10 ^ 10000`,
the exponent is at most `2 ^ 53000`. -/
theorem numbersE_le (U : Matrix ι ι ℚ) (hN : 1 ≤ N) (hN' : N ≤ 529)
    (hU : ∀ i j, (U i j).num.natAbs ≤ 10 ^ 10000 ∧ (U i j).den ≤ 10 ^ 10000) :
    numbersE U ≤ 2 ^ 53000 := by
  have hexp : expOf U ≤ 33220 := by
    unfold expOf
    rw [Nat.size_le]
    refine lt_of_le_of_lt (Finset.sup_le fun p _ => max_le (hU p.1 p.2).1 (hU p.1 p.2).2) ?_
    decide +kernel
  have hbase : 16 * N ^ 5 ≤ 2 ^ 50 :=
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hN' 5)).trans (by norm_num)
  have hpow : (16 * N ^ 5) ^ (2 * N) ≤ 2 ^ 52900 := by
    calc (16 * N ^ 5) ^ (2 * N) ≤ (2 ^ 50) ^ (2 * N) := Nat.pow_le_pow_left hbase _
      _ ≤ (2 ^ 50) ^ 1058 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 2 ^ 52900 := (pow_mul 2 50 1058).symm.trans (congrArg (fun k => 2 ^ k) (by norm_num))
  have hfac : facE U ≤ 2 ^ 52916 := by
    calc facE U ≤ (16 * N ^ 5) ^ (2 * N) * (expOf U + 1) := Height.FE_le N hN _ _
      _ ≤ 2 ^ 52900 * 2 ^ 16 := Nat.mul_le_mul hpow (by omega)
      _ = 2 ^ 52916 := by rw [← pow_add]
  have hN3 : 14 * N ^ 3 ≤ 2 ^ 32 :=
    (Nat.mul_le_mul_left 14 (Nat.pow_le_pow_left hN' 3)).trans (by norm_num)
  have hk : 14 * N ^ 3 * (facE U + 1) ≤ 2 ^ 53000 := by
    calc 14 * N ^ 3 * (facE U + 1) ≤ 2 ^ 32 * (2 ^ 52916 + 2 ^ 52916) :=
          Nat.mul_le_mul hN3 (by have := Nat.one_le_two_pow (n := 52916); omega)
      _ = 2 ^ 52949 := by rw [← two_mul, ← pow_succ', ← pow_add]
      _ ≤ 2 ^ 53000 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  refine max_le (hexp.trans ?_) (max_le (hfac.trans ?_) hk)
  · exact (show 33220 < 2 ^ 16 by norm_num).le.trans (pow_le_pow_right₀ (by norm_num) (by norm_num))
  · exact pow_le_pow_right₀ (by norm_num) (by norm_num)

theorem le_coefficientBound {a : ℕ} (ha : a ≤ 2 ^ 53000) : 2 ^ a ≤ coefficientBound :=
  Networks.two_pow_le_coefficientBound (Networks.le_coefficientExponent ha)

/-- The numbers of a matrix of size at most `529` with entries of height at most `10 ^ 10000`
are at most `coefficientBound`. -/
theorem numbers_le_coefficientBound (U : Matrix ι ι ℚ) (hN : 1 ≤ N) (hN' : N ≤ 529)
    (hU : ∀ i j, (U i j).num.natAbs ≤ 10 ^ 10000 ∧ (U i j).den ≤ 10 ^ 10000) :
    ∀ d ∈ numbers U, d ≤ coefficientBound := fun d hd =>
  (numbers_le U hN d hd).trans (le_coefficientBound (numbersE_le U hN hN' hU))

/-- The coefficients of the program of such a matrix have numerators and denominators at most
`coefficientBound`. -/
theorem program_coeffs_le_coefficientBound (U : Matrix ι ι ℚ) (hN : 1 ≤ N) (hN' : N ≤ 529)
    (hU : ∀ i j, (U i j).num.natAbs ≤ 10 ^ 10000 ∧ (U i j).den ≤ 10 ^ 10000) :
    ∀ op ∈ program U, ∀ r ∈ opCoeffs op,
      r.num.natAbs ≤ coefficientBound ∧ r.den ≤ coefficientBound := by
  intro op hop r hr
  have h := (program_coeffs_le U hN op hop r hr).trans
    (le_coefficientBound (numbersE_le U hN hN' hU))
  exact ⟨(Height.num_le_ht r).trans h, (Height.den_le_ht r).trans h⟩

/-- **The reduced exchange program under the literal bound.** For a rational idempotent of size
at most `529` with entries of height at most `10 ^ 10000`, and a prime beyond
`coefficientBound`, the reduction mod every `q ^ b` runs as the reduced exchange. -/
theorem specialize_run_of_bound (U : Matrix ι ι ℚ) (hU : U * U = U) (hN : 1 ≤ N) (hN' : N ≤ 529)
    (hH : ∀ i j, (U i j).num.natAbs ≤ 10 ^ 10000 ∧ (U i j).den ≤ 10 ^ 10000)
    {q : ℕ} (hq : q.Prime) (hqb : coefficientBound < q) (b : ℕ) (s : State ι (ZMod (q ^ b))) :
    AffineFieldProgram.run ((program U).map (AffineFieldProgram.mapOp (ratMod (q ^ b)))) s =
      exchange (reduce (q ^ b) U) s :=
  specialize_run hU hq (fun d hd => lt_of_le_of_lt (numbers_le_coefficientBound U hN hN' hH d hd) hqb)
    b s

theorem specialize_legal_of_bound (U : Matrix ι ι ℚ) (hN : 1 ≤ N) (hN' : N ≤ 529)
    (hH : ∀ i j, (U i j).num.natAbs ≤ 10 ^ 10000 ∧ (U i j).den ≤ 10 ^ 10000)
    {q : ℕ} (hq : q.Prime) (hqb : coefficientBound < q) (b : ℕ) :
    ∀ op ∈ (program U).map (AffineFieldProgram.mapOp (ratMod (q ^ b))),
      AffineFieldProgram.Legal op :=
  specialize_legal hq (fun d hd => lt_of_le_of_lt (numbers_le_coefficientBound U hN hN' hH d hd) hqb)
    b

end
end IntegerMultBounds.MathlibTM2.M8.Exchange
