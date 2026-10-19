module

public import IntegerMultBounds.MathlibTM2.M8.Exchange
public import IntegerMultBounds.Swap.PivotRank

/-!
# The reversed exchange as one reversed child

Stage 2 conjugates every frame of the node by `diag(1, C)`, with `C` the reversal of the
coordinates. A projector's partial swap then becomes the reversed exchange
`D'_P = transform 1 C ∘ D_P ∘ transform 1 C` (`revExchange`). Its children are reversed
interchanges: `h_k ↔ d_{m-1-k}` for `k < r` (`revPivots`), the first `r` coordinates of the head
field against the last `r` of the tail field in opposite orders.

When `P C = L Π_r R` with lower-triangular invertible `L`, `R` and `Π_r` the pivot matrix of
`revPivots r` (`revExchange_factor`), `D'_P` is the transformation by `L⁻¹` and `R`, the shear by
`K`, the `r` reversed interchanges, the shear by `-K`, and the transformation by `L` and `R⁻¹`,
with `K = kMat Π_r (R C L)`. This is `Exchange.exchange_factor` at `U = P`, `E₁ = L`,
`E₂ = R C`: the conjugation by `C` meets `E₂` and cancels (`C C = 1`). The same holds for any
involution `C` and pivot list (`revExchangeOf_factor`).

With `f` atoms per sub-field, the reversal of all atoms is `C_m ⊗ C_f` and the projector acts as
`P ⊗ 1`. Its reversed exchange is the lifted program, with factors `L ⊗ 1`, `R ⊗ 1` and the
`r f` reversed pivots of `r` sub-fields (`atomPivots`, `revExchange_atoms`): one reversed child
on the first `r f` head atoms and the last `r f` tail atoms.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.ReversedExchange

open Matrix
open scoped Kronecker
open IntegerMultBounds.Swap.Shear (State Op run pivotMatrix LowerTriangular)
open Exchange (exchange transform cross swaps kMat)

variable {m : ℕ} {R : Type*} [CommRing R]

/-- The reversal of the coordinates. -/
def rev (m : ℕ) : Matrix (Fin m) (Fin m) R := Matrix.of fun i j => if j = i.rev then 1 else 0

theorem rev_mul_rev : rev m * rev m = (1 : Matrix (Fin m) (Fin m) R) := by
  ext i j
  simp only [rev, mul_apply, of_apply, one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i.rev]
  · simp only [Fin.rev_rev, eq_comm]
    simp
  · intro k _ hk
    simp [hk]
  · simp

theorem rev_mul_rev_mul (A : Matrix (Fin m) (Fin m) R) : rev m * (rev m * A) = A := by
  rw [← Matrix.mul_assoc, rev_mul_rev, Matrix.one_mul]

/-- The reversed exchange `D'_P`: the partial swap of `P` in the frame `diag(1, C)`. -/
def revExchange (P : Matrix (Fin m) (Fin m) R) (s : State (Fin m) R) : State (Fin m) R :=
  transform 1 (rev m) (exchange P (transform 1 (rev m) s))

/-- The reversed pivots `(k, m-1-k)` for `k < r`. -/
def revPivots (m r : ℕ) : List (Fin m × Fin m) :=
  ((List.finRange m).filter fun k => k.val < r).map fun k => (k, k.rev)

theorem revPivots_fst (m r : ℕ) : ((revPivots m r).map Prod.fst).Nodup := by
  simp only [revPivots, List.map_map, Function.comp_def, List.map_id']
  exact (List.nodup_finRange m).filter _

theorem revPivots_snd (m r : ℕ) : ((revPivots m r).map Prod.snd).Nodup := by
  simp only [revPivots, List.map_map, Function.comp_def]
  exact ((List.nodup_finRange m).filter _).map Fin.rev_injective

theorem transform_comp {ι : Type*} [Fintype ι] (A B A' B' : Matrix ι ι R) (s : State ι R) :
    transform A B (transform A' B' s) = transform (A * A') (B * B') s := by
  simp [transform, mulVec_mulVec]

/-- The partial swap of `P` in the frame `diag(1, C)`, for any involution `C`. -/
def revExchangeOf {ι : Type*} [Fintype ι] [DecidableEq ι] (C P : Matrix ι ι R) (s : State ι R) :
    State ι R :=
  transform 1 C (exchange P (transform 1 C s))

/-- The reversed exchange program for any involution `C` and pivot list: if `P C = L Π R`, the
partial swap of `P` in the frame `diag(1, C)` is the transformation by `L⁻¹` and `R`, the shear by
`K`, the interchanges of the pivots, the shear by `-K`, and the transformation by `L` and `R⁻¹`. -/
theorem revExchangeOf_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι R)
    (hC : C * C = 1) (L L' R' R'' : Matrix ι ι R) (pivots : List (ι × ι))
    (h₁ : (pivots.map Prod.fst).Nodup) (h₂ : (pivots.map Prod.snd).Nodup)
    (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1) (hR' : R'' * R' = 1)
    (P : Matrix ι ι R) (hP : P * C = L * pivotMatrix pivots * R') (hidem : P * P = P)
    (s : State ι R) :
    transform L R'' (cross (-kMat (pivotMatrix pivots) (R' * C * L))
      (run (swaps pivots) (cross (kMat (pivotMatrix pivots) (R' * C * L)) (transform L' R' s)))) =
      revExchangeOf C P s := by
  have hCC (A : Matrix ι ι R) : C * (C * A) = A := by rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  have hU : P = L * pivotMatrix pivots * (R' * C) := by
    rw [← Matrix.mul_assoc, ← hP, Matrix.mul_assoc, hC, Matrix.mul_one]
  have e₂ : R' * C * (C * R'') = 1 := by
    rw [Matrix.mul_assoc, hCC, hR]
  have e₂' : C * R'' * (R' * C) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc R'', hR', Matrix.one_mul, hC]
  have he := Exchange.exchange_factor L L' (R' * C) (C * R'') pivots h₁ h₂ hL hL' e₂ e₂' P hU
    hidem (transform 1 C s)
  rw [revExchangeOf, ← he]
  simp only [transform_comp, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hC, hCC]

/-- **The reversed exchange program.** For `P` idempotent with `P C = L Π_r R`, `L`, `R`
invertible, `D'_P` is the transformation by `L⁻¹` and `R`, the shear by `K`, the reversed
interchanges, the shear by `-K`, and the transformation by `L` and `R⁻¹`. -/
theorem revExchange_factor (L L' R' R'' : Matrix (Fin m) (Fin m) R) (r : ℕ)
    (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1) (hR' : R'' * R' = 1)
    (P : Matrix (Fin m) (Fin m) R) (hP : P * rev m = L * pivotMatrix (revPivots m r) * R')
    (hidem : P * P = P) (s : State (Fin m) R) :
    transform L R'' (cross (-kMat (pivotMatrix (revPivots m r)) (R' * rev m * L))
      (run (swaps (revPivots m r))
        (cross (kMat (pivotMatrix (revPivots m r)) (R' * rev m * L)) (transform L' R' s)))) =
      revExchange P s :=
  revExchangeOf_factor (rev m) rev_mul_rev L L' R' R'' (revPivots m r) (revPivots_fst m r)
    (revPivots_snd m r) hL hL' hR hR' P hP hidem s

/-! ### Fields of atoms -/

/-- The reversed pivots of `r` sub-fields of `f` atoms: atom `x` of head sub-field `k < r` against
atom `f-1-x` of tail sub-field `m-1-k`. -/
def atomPivots (m f r : ℕ) : List ((Fin m × Fin f) × (Fin m × Fin f)) :=
  (((List.finRange m).filter fun k => k.val < r) ×ˢ List.finRange f).map
    fun q => (q, (q.1.rev, q.2.rev))

theorem atomPivots_fst (m f r : ℕ) : ((atomPivots m f r).map Prod.fst).Nodup := by
  simp only [atomPivots, List.map_map, Function.comp_def, List.map_id']
  exact ((List.nodup_finRange m).filter _).product (List.nodup_finRange f)

theorem atomPivots_snd (m f r : ℕ) : ((atomPivots m f r).map Prod.snd).Nodup := by
  simp only [atomPivots, List.map_map, Function.comp_def]
  refine (((List.nodup_finRange m).filter _).product (List.nodup_finRange f)).map ?_
  intro q q' h
  simp only [Prod.mk.injEq, Fin.rev_inj] at h
  exact Prod.ext h.1 h.2

theorem mem_atomPivots (m f r : ℕ) (q q' : Fin m × Fin f) :
    (q, q') ∈ atomPivots m f r ↔ q.1.val < r ∧ q'.1 = q.1.rev ∧ q'.2 = q.2.rev := by
  obtain ⟨a, x⟩ := q
  obtain ⟨b, y⟩ := q'
  simp only [atomPivots, List.mem_map, Prod.exists, List.mem_product, List.mem_filter,
    List.mem_finRange, true_and, and_true, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a', x', ha, ⟨rfl, rfl⟩, rfl, rfl⟩
    exact ⟨ha, rfl, rfl⟩
  · rintro ⟨ha, rfl, rfl⟩
    exact ⟨a, x, ha, ⟨rfl, rfl⟩, rfl, rfl⟩

theorem mem_revPivots (m r : ℕ) (a b : Fin m) : (a, b) ∈ revPivots m r ↔ a.val < r ∧ b = a.rev := by
  simp only [revPivots, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, rfl, rfl⟩
    exact ⟨hk, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl, rfl⟩

theorem atomPivots_matrix (m f r : ℕ) :
    (pivotMatrix (atomPivots m f r) : Matrix (Fin m × Fin f) (Fin m × Fin f) R) =
      pivotMatrix (revPivots m r) ⊗ₖ rev f := by
  ext ⟨a, x⟩ ⟨b, y⟩
  rw [IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply _ ((atomPivots_fst m f r).of_map _),
    kroneckerMap_apply,
    IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply _ ((revPivots_fst m r).of_map _)]
  simp only [mem_atomPivots, mem_revPivots, rev, of_apply]
  by_cases h1 : a.val < r ∧ b = a.rev <;> by_cases h2 : y = x.rev <;> simp_all

theorem rev_kron_mul_rev_kron (f : ℕ) :
    (rev m ⊗ₖ rev f) * (rev m ⊗ₖ rev f) = (1 : Matrix (Fin m × Fin f) (Fin m × Fin f) R) := by
  rw [← mul_kronecker_mul, rev_mul_rev, rev_mul_rev, one_kronecker_one]

/-- **The reversed exchange on atoms.** With `f` atoms per sub-field, the reversal of all atoms is
`C_m ⊗ C_f`, and the projector acts as `P ⊗ 1`. Its reversed exchange is the lifted program:
transformations by `L⁻¹ ⊗ 1` and `R ⊗ 1`, the shear by the lifted correction, and the `r f`
interchanges of the reversed pivots of `r` sub-fields, which form one reversed child on the
first `r f` head atoms and the last `r f` tail atoms. -/
theorem revExchange_atoms (f : ℕ) (L L' R' R'' : Matrix (Fin m) (Fin m) R) (r : ℕ)
    (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1) (hR' : R'' * R' = 1)
    (P : Matrix (Fin m) (Fin m) R) (hP : P * rev m = L * pivotMatrix (revPivots m r) * R')
    (hidem : P * P = P) (s : State (Fin m × Fin f) R) :
    transform (L ⊗ₖ 1) (R'' ⊗ₖ 1)
      (cross (-kMat (pivotMatrix (atomPivots m f r)) ((R' ⊗ₖ 1) * (rev m ⊗ₖ rev f) * (L ⊗ₖ 1)))
        (run (swaps (atomPivots m f r))
          (cross (kMat (pivotMatrix (atomPivots m f r)) ((R' ⊗ₖ 1) * (rev m ⊗ₖ rev f) * (L ⊗ₖ 1)))
            (transform (L' ⊗ₖ 1) (R' ⊗ₖ 1) s)))) =
      revExchangeOf (rev m ⊗ₖ rev f) (P ⊗ₖ (1 : Matrix (Fin f) (Fin f) R)) s := by
  have one_one : (1 : Matrix (Fin f) (Fin f) R) * 1 = 1 := Matrix.one_mul 1
  have hk (A B : Matrix (Fin m) (Fin m) R) (h : A * B = 1) :
      (A ⊗ₖ (1 : Matrix (Fin f) (Fin f) R)) * (B ⊗ₖ 1) = 1 := by
    rw [← mul_kronecker_mul, h, one_one, one_kronecker_one]
  apply revExchangeOf_factor (rev m ⊗ₖ rev f) (rev_kron_mul_rev_kron f) _ _ _ _ (atomPivots m f r)
    (atomPivots_fst m f r) (atomPivots_snd m f r) (hk _ _ hL) (hk _ _ hL') (hk _ _ hR) (hk _ _ hR')
  · simp only [atomPivots_matrix, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hP]
  · rw [← mul_kronecker_mul, hidem, one_one]

/-- In the atom order of `Fin (m * f)` (sub-field major), a lower-triangular `L` lifts to a
lower-triangular `L ⊗ 1`: every update reads an earlier atom. -/
theorem lower_kron_one {f : ℕ} {L : Matrix (Fin m) (Fin m) R} (hL : LowerTriangular L) :
    LowerTriangular ((L ⊗ₖ (1 : Matrix (Fin f) (Fin f) R)).reindex finProdFinEquiv finProdFinEquiv) := by
  intro u v huv
  obtain ⟨⟨a, x⟩, rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨b, y⟩, rfl⟩ := finProdFinEquiv.surjective v
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply]
  rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val] at huv
  have huv' : (x : ℕ) + f * a < y + f * b := huv
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [hL a b hab, zero_mul]
  · have hxy : x ≠ y := by
      intro h
      subst h
      exact lt_irrefl _ huv'
    rw [one_apply_ne hxy, mul_zero]
  · exfalso
    have hy := y.isLt
    have hb : (b : ℕ) + 1 ≤ a := hab
    have h1 := Nat.mul_le_mul_left f hb
    have h2 : f * ((b : ℕ) + 1) = f * b + f := by ring
    have hx := x.isLt
    omega

/-! ### The ordinary wrapper -/

/-- The reversed interchange of two whole fields: `(h, d) ↦ (C d, C h)`. -/
def revSwap {ι : Type*} [Fintype ι] (C : Matrix ι ι R) (s : State ι R) : State ι R :=
  (C *ᵥ s.2, C *ᵥ s.1)

/-- **The `F L F` wrapper.** For an involution `C`, the sequence `d ← d - h`, `F`, `d ← d + h`,
`F`, `d ← h - d` is the ordinary interchange `(h, d) ↦ (d, h)`: two reversed calls and three
shears. -/
theorem flf_wrapper {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι R) (hC : C * C = 1)
    (s : State ι R) :
    let t₁ : State ι R := (s.1, s.2 - s.1)
    let t₂ := revSwap C t₁
    let t₃ : State ι R := (t₂.1, t₂.2 + t₂.1)
    let t₄ := revSwap C t₃
    ((t₄.1, t₄.1 - t₄.2) : State ι R) = (s.2, s.1) := by
  have hCC (v : ι → R) : C *ᵥ (C *ᵥ v) = v := by rw [mulVec_mulVec, hC, one_mulVec]
  obtain ⟨h, d⟩ := s
  simp only [revSwap, mulVec_sub, mulVec_add, hCC]
  refine Prod.ext ?_ ?_
  · simp
  · simp only
    abel

end IntegerMultBounds.MathlibTM2.M8.ReversedExchange
