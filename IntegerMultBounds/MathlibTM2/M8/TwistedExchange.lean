module

public import IntegerMultBounds.MathlibTM2.M8.ReversedExchange

/-!
# The reversed exchange over an atom ring

Stage 2 keeps the `m` coordinates of a field and lets each coordinate carry `f` atoms: the
coordinates take values in a ring `S` (`(ℤ/q^w)^f`, atomwise), and the reversal of the atoms
inside a coordinate is a ring involution `σ` of `S`. Rational scalars act on every atom alike, so
the matrices of the node have entries fixed by `σ` (`Fixed`). The reversal of all atoms is then
the reversal of the coordinates followed by `σ` in every coordinate.

Here `σ` is any involutive ring endomorphism. Twisting the tail field by `σ` (`conj`) commutes
with transformations by fixed matrices, turns the cross shear `d ← d + K h` into the twisted shear
`d ← d + K σ(h)` (`crossTw`) and every interchange into the twisted interchange
`h_i ← σ(d_j)`, `d_j ← σ(h_i)` (`revSwaps`). So `ReversedExchange.revExchangeOf_factor` over `S`
gives the reversed exchange of the atom field as the fixed transformations, two twisted shears
and `r` twisted interchanges (`twisted_factor`, `twisted_rev_factor`). The `r` twisted
interchanges on the reversed pivots `(k, m-1-k)`, `k < r`, are one reversed child on the first
`r f` head atoms and the last `r f` tail atoms. Nothing depends on `f`.

`atomRev` is the involution of `Fin f → R`, and `algebraMap` matrices are fixed by it
(`fixed_algebraMap`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.TwistedExchange

open Matrix
open IntegerMultBounds.Swap.Shear (State Op run pivotMatrix)
open Exchange (transform cross swaps kMat)
open ReversedExchange (revExchangeOf rev)

variable {ι S : Type*} [CommRing S] (σ : S →+* S)

/-- `σ` in every coordinate. -/
def twist (v : ι → S) : ι → S := fun i => σ (v i)

/-- The tail field twisted by `σ`. -/
def conj (s : State ι S) : State ι S := (s.1, twist σ s.2)

/-- A matrix whose entries `σ` fixes. -/
def Fixed (A : Matrix ι ι S) : Prop := A.map σ = A

/-- The twisted shear `d ← d + K σ(h)`. -/
def crossTw [Fintype ι] (K : Matrix ι ι S) (s : State ι S) : State ι S :=
  (s.1, s.2 + K *ᵥ twist σ s.1)

variable [Fintype ι] [DecidableEq ι]

/-- The twisted interchange `h_i ← σ(d_j)`, `d_j ← σ(h_i)`. -/
def revSwap (p : ι × ι) (s : State ι S) : State ι S :=
  (Function.update s.1 p.1 (σ (s.2 p.2)), Function.update s.2 p.2 (σ (s.1 p.1)))

/-- The twisted interchanges of a pivot list, in order. -/
def revSwaps (L : List (ι × ι)) (s : State ι S) : State ι S := L.foldl (fun s p => revSwap σ p s) s

variable {σ}

section Fixed

omit [Fintype ι] [DecidableEq ι] in
theorem fixed_apply {A : Matrix ι ι S} (h : Fixed σ A) (i j : ι) : σ (A i j) = A i j :=
  congrFun (congrFun h i) j

omit [DecidableEq ι] in
theorem fixed_mul {A B : Matrix ι ι S} (hA : Fixed σ A) (hB : Fixed σ B) : Fixed σ (A * B) := by
  rw [Fixed, Matrix.map_mul, hA, hB]

omit [Fintype ι] [DecidableEq ι] in
theorem fixed_add {A B : Matrix ι ι S} (hA : Fixed σ A) (hB : Fixed σ B) : Fixed σ (A + B) := by
  rw [Fixed, Matrix.map_add _ (map_add σ), hA, hB]

omit [Fintype ι] [DecidableEq ι] in
theorem fixed_sub {A B : Matrix ι ι S} (hA : Fixed σ A) (hB : Fixed σ B) : Fixed σ (A - B) := by
  rw [Fixed, Matrix.map_sub _ (map_sub σ), hA, hB]

omit [Fintype ι] [DecidableEq ι] in
theorem fixed_neg {A : Matrix ι ι S} (hA : Fixed σ A) : Fixed σ (-A) := by
  rw [Fixed, Matrix.map_neg _ (map_neg σ), hA]

omit [Fintype ι] [DecidableEq ι] in
theorem fixed_transpose {A : Matrix ι ι S} (hA : Fixed σ A) : Fixed σ Aᵀ := by
  rw [Fixed, Matrix.transpose_map, hA]

omit [Fintype ι] in
theorem fixed_pivot (L : List (ι × ι)) : Fixed σ (pivotMatrix L : Matrix ι ι S) := by
  induction L with
  | nil => exact Matrix.map_zero σ (map_zero σ)
  | cons p L ih =>
    refine fixed_add ?_ ih
    ext a b
    simp only [Matrix.map_apply, single, of_apply]
    split_ifs <;> simp

omit [DecidableEq ι] in
theorem fixed_kMat {P M : Matrix ι ι S} (hP : Fixed σ P) (hM : Fixed σ M) : Fixed σ (kMat P M) := by
  have hPt := fixed_transpose hP
  exact fixed_sub (fixed_add (fixed_sub (fixed_mul hM (fixed_mul hP hPt))
    (fixed_mul (fixed_mul hPt hP) hM)) (fixed_mul (fixed_mul (fixed_mul hPt hP) hM)
    (fixed_mul hP hPt))) hPt

end Fixed

section Conj

variable (hσ : ∀ x, σ (σ x) = x)
include hσ

omit [Fintype ι] [DecidableEq ι] in
theorem twist_twist (v : ι → S) : twist σ (twist σ v) = v := funext fun i => hσ (v i)

omit [Fintype ι] [DecidableEq ι] in
theorem conj_conj (s : State ι S) : conj σ (conj σ s) = s := by
  simp [conj, twist_twist hσ]

omit hσ [Fintype ι] [DecidableEq ι] in
theorem twist_add (v w : ι → S) : twist σ (v + w) = twist σ v + twist σ w :=
  funext fun _ => map_add σ _ _

omit hσ [DecidableEq ι] in
theorem twist_mulVec {A : Matrix ι ι S} (hA : Fixed σ A) (v : ι → S) :
    twist σ (A *ᵥ v) = A *ᵥ twist σ v := by
  funext i
  simp only [twist, mulVec, dotProduct, map_sum, map_mul, fixed_apply hA]

omit hσ [DecidableEq ι] in
theorem conj_transform (A : Matrix ι ι S) {B : Matrix ι ι S} (hB : Fixed σ B) (s : State ι S) :
    conj σ (transform A B s) = transform A B (conj σ s) := by
  simp [conj, transform, twist_mulVec hB]

omit hσ [DecidableEq ι] in
theorem conj_cross {K : Matrix ι ι S} (hK : Fixed σ K) (s : State ι S) :
    conj σ (cross K s) = crossTw σ K (conj σ s) := by
  simp [conj, cross, crossTw, twist_add, twist_mulVec hK]

theorem conj_interchange (p : ι × ι) (s : State ι S) :
    conj σ ((Op.interchange p.1 p.2).run s) = revSwap σ p (conj σ s) := by
  obtain ⟨h, d⟩ := s
  simp only [conj, Op.run, revSwap, twist, hσ]
  refine Prod.ext rfl (funext fun k => ?_)
  by_cases hk : k = p.2
  · subst hk; simp [twist]
  · simp [twist, hk]

theorem conj_swaps (L : List (ι × ι)) (s : State ι S) :
    conj σ (run (swaps L) s) = revSwaps σ L (conj σ s) := by
  induction L generalizing s with
  | nil => rfl
  | cons p L ih =>
    change conj σ (run (swaps L) ((Op.interchange p.1 p.2).run s)) =
      revSwaps σ L (revSwap σ p (conj σ s))
    rw [ih, conj_interchange hσ]

/-- **The twisted exchange program.** For `σ`-fixed matrices with `P C = L Π R`, the reversed
exchange of `P` in the frame `diag(1, C σ)` is the transformation by `L⁻¹` and `R`, the twisted
shear by `K`, the twisted interchanges of the pivots, the twisted shear by `-K`, and the
transformation by `L` and `R⁻¹`, with `K = kMat Π (R C L)`. -/
theorem twisted_factor {C : Matrix ι ι S} (hC : C * C = 1) {L L' R' R'' : Matrix ι ι S}
    (hfR' : Fixed σ R') (hfR'' : Fixed σ R'') (hfC : Fixed σ C) (hfL : Fixed σ L)
    (pivots : List (ι × ι)) (h₁ : (pivots.map Prod.fst).Nodup) (h₂ : (pivots.map Prod.snd).Nodup)
    (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1) (hR' : R'' * R' = 1)
    (P : Matrix ι ι S) (hP : P * C = L * pivotMatrix pivots * R') (hidem : P * P = P)
    (s : State ι S) :
    transform L R'' (crossTw σ (-kMat (pivotMatrix pivots) (R' * C * L))
      (revSwaps σ pivots (crossTw σ (kMat (pivotMatrix pivots) (R' * C * L))
        (transform L' R' s)))) =
      conj σ (revExchangeOf C P (conj σ s)) := by
  have hK : Fixed σ (kMat (pivotMatrix pivots) (R' * C * L)) :=
    fixed_kMat (fixed_pivot pivots) (fixed_mul (fixed_mul hfR' hfC) hfL)
  rw [← ReversedExchange.revExchangeOf_factor C hC L L' R' R'' pivots h₁ h₂ hL hL' hR hR' P hP
    hidem, conj_transform _ hfR'', conj_cross (fixed_neg hK), conj_swaps hσ, conj_cross hK,
    conj_transform _ hfR', conj_conj hσ]

/-- **The twisted exchange on reversed pivots.** With the reversal `C` of the coordinates, the
twisted interchanges are those of `revPivots m r`: one reversed child on the first `r` head
coordinates and the last `r` tail coordinates, all their atoms included. -/
theorem twisted_rev_factor {m : ℕ} {L L' R' R'' : Matrix (Fin m) (Fin m) S}
    (hfR' : Fixed σ R') (hfR'' : Fixed σ R'') (hfL : Fixed σ L) (r : ℕ)
    (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1) (hR' : R'' * R' = 1)
    (P : Matrix (Fin m) (Fin m) S) (hP : P * rev m = L * pivotMatrix (ReversedExchange.revPivots m r) * R')
    (hidem : P * P = P) (s : State (Fin m) S) :
    transform L R'' (crossTw σ (-kMat (pivotMatrix (ReversedExchange.revPivots m r)) (R' * rev m * L))
      (revSwaps σ (ReversedExchange.revPivots m r)
        (crossTw σ (kMat (pivotMatrix (ReversedExchange.revPivots m r)) (R' * rev m * L))
          (transform L' R' s)))) =
      conj σ (revExchangeOf (rev m) P (conj σ s)) :=
  twisted_factor hσ ReversedExchange.rev_mul_rev hfR' hfR'' (by
      ext i j
      simp only [Matrix.map_apply, rev, of_apply]
      split_ifs <;> simp) hfL _
    (ReversedExchange.revPivots_fst m r) (ReversedExchange.revPivots_snd m r) hL hL' hR hR' P hP
    hidem s

end Conj

/-! ### The atom ring -/

section Atoms

variable {R : Type*} [CommRing R] (f : ℕ)

/-- The reversal of the `f` atoms of a coordinate. -/
def atomRev : (Fin f → R) →+* (Fin f → R) := RingHom.pi fun x => Pi.evalRingHom _ x.rev

@[simp] theorem atomRev_apply (v : Fin f → R) (x : Fin f) : atomRev f v x = v x.rev := rfl

theorem atomRev_atomRev (v : Fin f → R) : atomRev f (atomRev f v) = v :=
  funext fun x => by simp

omit [Fintype ι] [DecidableEq ι] in
/-- Scalars act on every atom alike, so their matrices are fixed by the atom reversal. -/
theorem fixed_algebraMap (A : Matrix ι ι R) :
    Fixed (atomRev f) (A.map (algebraMap R (Fin f → R))) := by
  ext i j x
  simp [Matrix.map_apply]

end Atoms

end IntegerMultBounds.MathlibTM2.M8.TwistedExchange
