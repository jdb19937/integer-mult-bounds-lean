module

public import IntegerMultBounds.MathlibTM2.M8.Exchange
public import IntegerMultBounds.Networks.AffineFieldProgram
public import IntegerMultBounds.Networks.ModularFrameSchedule
public import IntegerMultBounds.Networks.AffineFieldCoordinates
public import IntegerMultBounds.Networks.CoefficientBound
public import IntegerMultBounds.MathlibTM2.M8.Height
public import Mathlib.Data.Nat.Size

/-!
# The exchange program in field operations

`Exchange.exchange_factor` writes the exchange `D_U` of an idempotent `U = E₁ Π E₂` as
transformations within the fields, two cross shears and the pivot interchanges. Here the steps
become the field operations of `AffineFieldProgram`:
* a lower triangular transformation is its ordered scalings and in-field shifts
  (`AffineFieldProgram.compile`);
* the cross shear `d ← d + K h` is, for each nonzero entry `c = K j i`, the three operations
  `d_j ← c⁻¹ d_j`, `d_j ← d_j + h_i`, `d_j ← c d_j` (`crossEntry`);
* each pivot `(i, j)` is one `interchange i j`, the recursive child.

For a rational idempotent `U`, `program U` uses a fixed lower triangular factorization of `U`
(`factors U`). Its run is `D_U` (`program_run`), it has exactly `rank U` interchanges
(`program_interchanges`), and its operations are legal (`program_legal`). For a prime `q` beyond
the denominators and numerators of the coefficients (`numbers U`), its reduction mod every `q^b`
runs as the exchange on the reduction of `U` (`specialize_run`), with legal operations
(`specialize_legal`) and the same interchanges. One prime serves any finite family of
idempotents (`exists_prime_numbers`).

On the flat `H ++ D` coordinate vector, every legal nonrecursive field operation expands to
ordered scalar steps that are legal there: unit scalings and shifts whose control precedes the
target (`expand_legal`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Exchange

noncomputable section
open Matrix Finset
open IntegerMultBounds.Networks
open IntegerMultBounds.Swap.Shear (State LowerTriangular pivotMatrix)
open IntegerMultBounds.Swap.Modular (ratMod reduce Admissible denominators admissible_of_lt)

variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]

/-! ### The cross shear in field operations -/

/-- `d_j ← d_j + c h_i` as a scaling, an addition and a scaling, for `c c' = 1`. -/
def crossEntry (i j : ι) (c c' : R) : List (AffineFieldProgram.Op ι R) :=
  [.affineD (.scale j c'), .addToD i j, .affineD (.scale j c)]

theorem crossEntry_run (i j : ι) (c c' : R) (hc : c * c' = 1) (s : State ι R) :
    AffineFieldProgram.run (crossEntry i j c c') s =
      (s.1, Function.update s.2 j (s.2 j + c * s.1 i)) := by
  obtain ⟨h, d⟩ := s
  simp only [crossEntry, AffineFieldProgram.run, List.foldl_cons, List.foldl_nil,
    AffineFieldProgram.execute, OrderedAffine.execute, Swap.Shear.Op.run, Function.update_self,
    Function.update_idem]
  congr 2
  rw [mul_add, ← mul_assoc, hc, one_mul]

/-- The cross program of a coefficient family on a list of pairs `(i, j)`: entries with
`skip p` are omitted, the others add `c p · h_i` to `d_j`. -/
def crossOps (l : List (ι × ι)) (skip : ι × ι → Prop) [DecidablePred skip] (c c' : ι × ι → R) :
    List (AffineFieldProgram.Op ι R) :=
  l.flatMap fun p => if skip p then [] else crossEntry p.1 p.2 (c p) (c' p)

lemma run_append (p q : List (AffineFieldProgram.Op ι R)) (s : State ι R) :
    AffineFieldProgram.run (p ++ q) s = AffineFieldProgram.run q (AffineFieldProgram.run p s) :=
  List.foldl_append

theorem crossOps_run (l : List (ι × ι)) (skip : ι × ι → Prop) [DecidablePred skip]
    (c c' : ι × ι → R) (hskip : ∀ p, skip p → c p = 0) (hunit : ∀ p, ¬skip p → c p * c' p = 1)
    (s : State ι R) :
    AffineFieldProgram.run (crossOps l skip c c') s =
      (s.1, s.2 + (l.map fun p => single p.2 p.1 (c p)).sum *ᵥ s.1) := by
  induction l generalizing s with
  | nil => simp [crossOps, AffineFieldProgram.run]
  | cons p l ih =>
    have hc : crossOps (p :: l) skip c c' =
        (if skip p then [] else crossEntry p.1 p.2 (c p) (c' p)) ++ crossOps l skip c c' := rfl
    rw [hc, run_append, ih]
    have hstep : AffineFieldProgram.run (if skip p then [] else crossEntry p.1 p.2 (c p) (c' p)) s =
        (s.1, s.2 + single p.2 p.1 (c p) *ᵥ s.1) := by
      split_ifs with hp
      · simp [AffineFieldProgram.run, hskip p hp]
      · rw [crossEntry_run _ _ _ _ (hunit p hp), single_mulVec]
        congr 1
        funext k
        by_cases hk : k = p.2
        · subst hk; simp
        · simp [hk]
    rw [hstep]
    simp only [List.map_cons, List.sum_cons, add_mulVec]
    congr 1
    abel

/-- All pairs, each once. -/
def allPairs (ι : Type*) [Fintype ι] : List (ι × ι) := (univ : Finset (ι × ι)).toList

/-- On all pairs, the cross program adds the matrix with entries `K j i = c (i, j)`. -/
theorem sum_allPairs (c : ι × ι → R) :
    ((allPairs ι).map fun p => single p.2 p.1 (c p)).sum = Matrix.of fun j i => c (i, j) := by
  rw [allPairs, Finset.sum_map_toList]
  ext a b
  rw [Matrix.sum_apply, Finset.sum_eq_single (b, a)]
  · simp [single]
  · intro p _ hp
    simp only [single, of_apply]
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    exact hp (Prod.ext h2 h1)
  · intro h; exact absurd (mem_univ _) h

/-! ### The exchange program over a ring -/

/-- The interchanges of a pivot list as field operations. -/
def swapOps (L : List (ι × ι)) : List (AffineFieldProgram.Op ι R) :=
  L.map fun p => .interchange p.1 p.2

theorem swapOps_run (L : List (ι × ι)) (s : State ι R) :
    AffineFieldProgram.run (swapOps L) s = Swap.Shear.run (swaps L) s := by
  induction L generalizing s with
  | nil => rfl
  | cons p L ih => exact ih _

/-- The transformation by `A` on `H` and `B` on `D`. -/
def transformOps (A B : Matrix ι ι R) : List (AffineFieldProgram.Op ι R) :=
  AffineFieldProgram.compile [.transformH A, .transformD B]

theorem transformOps_run (A B : Matrix ι ι R) (hA : LowerTriangular A) (hB : LowerTriangular B)
    (s : State ι R) : AffineFieldProgram.run (transformOps A B) s = transform A B s := by
  rw [transformOps, AffineFieldProgram.compile_run]
  · rfl
  · intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · exact hA
    · exact hB

/-- The exchange program from its parts. -/
def exchangeOps (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι))
    (crossK crossNegK : List (AffineFieldProgram.Op ι R)) : List (AffineFieldProgram.Op ι R) :=
  transformOps E₁' E₂ ++ crossK ++ swapOps L ++ crossNegK ++ transformOps E₁ E₂'

theorem exchangeOps_run (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι))
    (h₁ : (L.map Prod.fst).Nodup) (h₂ : (L.map Prod.snd).Nodup)
    (hl₁ : LowerTriangular E₁) (hl₁' : LowerTriangular E₁') (hl₂ : LowerTriangular E₂)
    (hl₂' : LowerTriangular E₂')
    (hinv₁ : E₁ * E₁' = 1) (hinv₁' : E₁' * E₁ = 1) (hinv₂ : E₂ * E₂' = 1) (hinv₂' : E₂' * E₂ = 1)
    (U : Matrix ι ι R) (hU : U = E₁ * pivotMatrix L * E₂) (hidem : U * U = U)
    (crossK crossNegK : List (AffineFieldProgram.Op ι R))
    (hK : ∀ s, AffineFieldProgram.run crossK s = cross (kMat (pivotMatrix L) (E₂ * E₁)) s)
    (hK' : ∀ s, AffineFieldProgram.run crossNegK s = cross (-kMat (pivotMatrix L) (E₂ * E₁)) s)
    (s : State ι R) :
    AffineFieldProgram.run (exchangeOps E₁ E₁' E₂ E₂' L crossK crossNegK) s = exchange U s := by
  rw [exchangeOps, run_append, run_append, run_append, run_append, transformOps_run _ _ hl₁' hl₂,
    hK, swapOps_run, hK', transformOps_run _ _ hl₁ hl₂']
  exact exchange_factor E₁ E₁' E₂ E₂' L h₁ h₂ hinv₁ hinv₁' hinv₂ hinv₂' U hU hidem s

omit [CommRing R] in
theorem exchangeOps_interchanges (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι))
    (crossK crossNegK : List (AffineFieldProgram.Op ι R))
    (hK : AffineFieldProgram.interchanges crossK = 0)
    (hK' : AffineFieldProgram.interchanges crossNegK = 0) :
    AffineFieldProgram.interchanges (exchangeOps E₁ E₁' E₂ E₂' L crossK crossNegK) = L.length := by
  have ht : ∀ A B : Matrix ι ι R, AffineFieldProgram.interchanges (transformOps A B) = 0 := by
    intro A B
    rw [transformOps, AffineFieldProgram.compile_interchanges]
    rfl
  have hs : AffineFieldProgram.interchanges (swapOps (R := R) L) = L.length := by
    induction L with
    | nil => rfl
    | cons p L ih =>
      change AffineFieldProgram.interchanges (swapOps L) + 1 = L.length + 1
      rw [ih]
  simp only [exchangeOps, AffineFieldProgram.interchanges_append, ht, hK, hK', hs]
  omega

omit [Fintype ι] [LinearOrder ι] [CommRing R] in
theorem crossOps_interchanges (l : List (ι × ι))
    (skip : ι × ι → Prop) [DecidablePred skip] (c c' : ι × ι → R) :
    AffineFieldProgram.interchanges (crossOps l skip c c') = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change AffineFieldProgram.interchanges
      ((if skip p then [] else crossEntry p.1 p.2 (c p) (c' p)) ++ crossOps l skip c c') = 0
    rw [AffineFieldProgram.interchanges_append, ih]
    split_ifs <;> rfl

/-! ### Legality -/

omit [Fintype ι] in
theorem crossOps_legal (l : List (ι × ι)) (skip : ι × ι → Prop) [DecidablePred skip]
    (c c' : ι × ι → R) (hunit : ∀ p, ¬skip p → c p * c' p = 1) :
    ∀ op ∈ crossOps l skip c c', AffineFieldProgram.Legal op := by
  intro op hop
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hop
  split_ifs at hp with hs
  · simp at hp
  · have hu := hunit p hs
    simp only [crossEntry, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact IsUnit.of_mul_eq_one (c p) (by rw [mul_comm]; exact hu)
    · trivial
    · exact IsUnit.of_mul_eq_one (c' p) hu

lemma isUnit_of_inverse {A A' : Matrix ι ι R} (h : A * A' = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse h)

theorem transformOps_legal {A A' B B' : Matrix ι ι R} (hA : LowerTriangular A)
    (hB : LowerTriangular B) (hA' : A * A' = 1) (hB' : B * B' = 1) :
    ∀ op ∈ transformOps A B, AffineFieldProgram.Legal op := by
  apply AffineFieldProgram.compile_legal
  intro op hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · exact ⟨hA, isUnit_of_inverse hA'⟩
  · exact ⟨hB, isUnit_of_inverse hB'⟩

theorem exchangeOps_legal (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι))
    (hl₁ : LowerTriangular E₁) (hl₁' : LowerTriangular E₁') (hl₂ : LowerTriangular E₂)
    (hl₂' : LowerTriangular E₂')
    (hinv₁ : E₁ * E₁' = 1) (hinv₁' : E₁' * E₁ = 1) (hinv₂ : E₂ * E₂' = 1) (hinv₂' : E₂' * E₂ = 1)
    (crossK crossNegK : List (AffineFieldProgram.Op ι R))
    (hK : ∀ op ∈ crossK, AffineFieldProgram.Legal op)
    (hK' : ∀ op ∈ crossNegK, AffineFieldProgram.Legal op) :
    ∀ op ∈ exchangeOps E₁ E₁' E₂ E₂' L crossK crossNegK, AffineFieldProgram.Legal op := by
  intro op hop
  simp only [exchangeOps, List.mem_append] at hop
  rcases hop with (((h | h) | h) | h) | h
  · exact transformOps_legal hl₁' hl₂ hinv₁' hinv₂ op h
  · exact hK op h
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    trivial
  · exact hK' op h
  · exact transformOps_legal hl₁ hl₂' hinv₁ hinv₂' op h

/-! ### Specialization of the parts -/

section Map
variable {S : Type*} [CommRing S] (f : R → S)

omit [Fintype ι] [LinearOrder ι] [CommRing R] [CommRing S] in
theorem crossOps_map (l : List (ι × ι)) (skip : ι × ι → Prop) [DecidablePred skip]
    (c c' : ι × ι → R) :
    (crossOps l skip c c').map (AffineFieldProgram.mapOp f) =
      crossOps l skip (fun p => f (c p)) (fun p => f (c' p)) := by
  simp only [crossOps, List.map_flatMap]
  congr 1
  funext p
  split_ifs <;> rfl

omit [CommRing R] [CommRing S] in
theorem transformOps_map (A B : Matrix ι ι R) :
    (transformOps A B).map (AffineFieldProgram.mapOp f) = transformOps (A.map f) (B.map f) := by
  rw [transformOps, ← AffineFieldProgram.compile_map]
  rfl

omit [Fintype ι] [LinearOrder ι] [CommRing R] [CommRing S] in
theorem swapOps_map (L : List (ι × ι)) :
    (swapOps (R := R) L).map (AffineFieldProgram.mapOp f) = swapOps L := by
  simp only [swapOps, List.map_map]
  rfl

omit [CommRing R] [CommRing S] in
theorem exchangeOps_map (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι))
    (crossK crossNegK : List (AffineFieldProgram.Op ι R)) :
    (exchangeOps E₁ E₁' E₂ E₂' L crossK crossNegK).map (AffineFieldProgram.mapOp f) =
      exchangeOps (E₁.map f) (E₁'.map f) (E₂.map f) (E₂'.map f) L
        (crossK.map (AffineFieldProgram.mapOp f)) (crossNegK.map (AffineFieldProgram.mapOp f)) := by
  simp only [exchangeOps, List.map_append, transformOps_map, swapOps_map]

end Map

/-! ### The rational exchange program -/

/-- The bit length of the largest entry height of a rational matrix. -/
def expOf (U : Matrix ι ι ℚ) : ℕ := Nat.size (univ.sup fun p : ι × ι => Height.ht (U p.1 p.2))

omit [LinearOrder ι] in
theorem bounded_expOf (U : Matrix ι ι ℚ) : Height.Bounded U (2 ^ expOf U) := fun i j =>
  ((Finset.le_sup (f := fun p : ι × ι => Height.ht (U p.1 p.2)) (mem_univ (i, j))).trans
    (Nat.lt_size_self _).le)

/-- The fixed lower triangular factorization of a rational matrix, with bounded heights. -/
def factors (U : Matrix ι ι ℚ) : Swap.LowerTriangular.Factorization univ univ U :=
  Classical.choose (Height.exists_bounded_univ U (expOf U) (bounded_expOf U))

theorem factors_bounded (U : Matrix ι ι ℚ) :
    Height.FactorsBounded (factors U)
      (2 ^ Height.FE (Fintype.card ι) (2 * Fintype.card ι) (expOf U)) :=
  Classical.choose_spec (Height.exists_bounded_univ U (expOf U) (bounded_expOf U))

/-- The correction shear of a rational matrix, from its fixed factorization. -/
def corr (U : Matrix ι ι ℚ) : Matrix ι ι ℚ :=
  kMat (pivotMatrix (factors U).L) ((factors U).E₂ * (factors U).E₁)

/-- The cross program of a rational matrix, on its nonzero entries. -/
def crossQ (K : Matrix ι ι ℚ) : List (AffineFieldProgram.Op ι ℚ) :=
  crossOps (allPairs ι) (fun p => K p.2 p.1 = 0) (fun p => K p.2 p.1) (fun p => (K p.2 p.1)⁻¹)

/-- **The exchange program** of a rational matrix. -/
def program (U : Matrix ι ι ℚ) : List (AffineFieldProgram.Op ι ℚ) :=
  exchangeOps (factors U).E₁ (factors U).E₁' (factors U).E₂ (factors U).E₂' (factors U).L
    (crossQ (corr U)) (crossQ (-corr U))

theorem crossQ_run (K : Matrix ι ι ℚ) (s : State ι ℚ) :
    AffineFieldProgram.run (crossQ K) s = cross K s := by
  rw [crossQ, crossOps_run _ _ _ _ (fun p hp => hp) (fun p hp => mul_inv_cancel₀ hp),
    sum_allPairs]
  rfl

/-- The exchange program of a rational idempotent runs as its exchange. -/
theorem program_run (U : Matrix ι ι ℚ) (hU : U * U = U) (s : State ι ℚ) :
    AffineFieldProgram.run (program U) s = exchange U s :=
  exchangeOps_run _ _ _ _ _ (factors U).nodup₁ (factors U).nodup₂ (factors U).lower₁
    (factors U).lower₁' (factors U).lower₂ (factors U).lower₂' (factors U).inv₁ (factors U).inv₁'
    (factors U).inv₂ (factors U).inv₂' U (factors U).eq hU _ _ (crossQ_run _) (crossQ_run _) s

/-- Exactly `rank U` interchanges. -/
theorem program_interchanges (U : Matrix ι ι ℚ) :
    AffineFieldProgram.interchanges (program U) = U.rank := by
  have h0 : ∀ K : Matrix ι ι ℚ, AffineFieldProgram.interchanges (crossQ K) = 0 :=
    fun K => crossOps_interchanges _ _ _ _
  rw [program, exchangeOps_interchanges _ _ _ _ _ _ _ (h0 _) (h0 _)]
  exact Swap.PivotRank.length_eq_rank (factors U)

theorem program_legal (U : Matrix ι ι ℚ) :
    ∀ op ∈ program U, AffineFieldProgram.Legal op :=
  exchangeOps_legal _ _ _ _ _ (factors U).lower₁ (factors U).lower₁' (factors U).lower₂
    (factors U).lower₂' (factors U).inv₁ (factors U).inv₁' (factors U).inv₂ (factors U).inv₂' _ _
    (crossOps_legal _ _ _ _ fun _ hp => mul_inv_cancel₀ hp)
    (crossOps_legal _ _ _ _ fun _ hp => mul_inv_cancel₀ hp)

/-! ### Reduction mod a prime power -/

/-- The denominators that the reduction must avoid: those of the factorization, of the
correction and its negative, and of their entrywise inverses (the scalings). -/
def numbers (U : Matrix ι ι ℚ) : Finset ℕ :=
  Swap.Modular.factorizationDenominators (factors U) ∪ denominators (corr U) ∪
    denominators ((corr U).map (·⁻¹)) ∪ denominators (-corr U) ∪
    denominators ((-corr U).map (·⁻¹))

omit [LinearOrder ι] in
theorem reduce_kMat (m : ℕ) {P M : Matrix ι ι ℚ} (hP : Admissible m P) (hM : Admissible m M) :
    reduce m (kMat P M) = kMat (reduce m P) (reduce m M) := by
  have hPt : Admissible m Pᵀ := fun i j => hP j i
  have rT : reduce m Pᵀ = (reduce m P)ᵀ := rfl
  have a1 := Swap.Modular.admissible_mul m hP hPt
  have a2 := Swap.Modular.admissible_mul m hPt hP
  have a3 := Swap.Modular.admissible_mul m hM a1
  have a4 := Swap.Modular.admissible_mul m a2 hM
  have a5 := Swap.Modular.admissible_mul m a4 a1
  have a6 := ModularFrameSchedule.admissible_sub m a3 a4
  have a7 := ModularFrameSchedule.admissible_add m a6 a5
  unfold kMat
  rw [ModularFrameSchedule.reduce_sub m a7 hPt, ModularFrameSchedule.reduce_add m a6 a5,
    ModularFrameSchedule.reduce_sub m a3 a4, Swap.Modular.reduce_mul m hM a1,
    Swap.Modular.reduce_mul m a4 a1, Swap.Modular.reduce_mul m a2 hM,
    Swap.Modular.reduce_mul m hP hPt, Swap.Modular.reduce_mul m hPt hP, rT]

/-- The reduced cross program of `K` adds the reduction of `K`. -/
theorem crossQ_specialize_run (m : ℕ) (K : Matrix ι ι ℚ) (hK : Admissible m K)
    (hK' : Admissible m (K.map (·⁻¹))) (s : State ι (ZMod m)) :
    AffineFieldProgram.run ((crossQ K).map (AffineFieldProgram.mapOp (ratMod m))) s =
      cross (reduce m K) s := by
  rw [crossQ, crossOps_map, crossOps_run, sum_allPairs]
  · rfl
  · intro p hp
    rw [hp, Swap.Modular.ratMod_zero]
  · intro p hp
    rw [← Swap.Modular.ratMod_mul m (x := K p.2 p.1) (y := (K p.2 p.1)⁻¹) (hK p.2 p.1) (hK' p.2 p.1),
      mul_inv_cancel₀ hp, Swap.Modular.ratMod_one]

theorem crossQ_specialize_legal (m : ℕ) (K : Matrix ι ι ℚ) (hK : Admissible m K)
    (hK' : Admissible m (K.map (·⁻¹))) :
    ∀ op ∈ (crossQ K).map (AffineFieldProgram.mapOp (ratMod m)), AffineFieldProgram.Legal op := by
  rw [crossQ, crossOps_map]
  apply crossOps_legal
  intro p hp
  rw [← Swap.Modular.ratMod_mul m (x := K p.2 p.1) (y := (K p.2 p.1)⁻¹) (hK p.2 p.1) (hK' p.2 p.1),
    mul_inv_cancel₀ hp, Swap.Modular.ratMod_one]

variable {U : Matrix ι ι ℚ} {q : ℕ}

/-- The admissibility facts of a prime beyond `numbers U`. -/
theorem numbers_admissible (hq : q.Prime) (hd : ∀ d ∈ numbers U, d < q) (b : ℕ) :
    Admissible (q ^ b) (corr U) ∧ Admissible (q ^ b) ((corr U).map (·⁻¹)) ∧
      Admissible (q ^ b) (-corr U) ∧ Admissible (q ^ b) ((-corr U).map (·⁻¹)) ∧
      ∀ d ∈ Swap.Modular.factorizationDenominators (factors U), d < q := by
  refine ⟨admissible_of_lt hq (fun d h => hd d ?_) b, admissible_of_lt hq (fun d h => hd d ?_) b,
    admissible_of_lt hq (fun d h => hd d ?_) b, admissible_of_lt hq (fun d h => hd d ?_) b,
    fun d h => hd d ?_⟩ <;> simp only [numbers, Finset.mem_union] <;> tauto

/-- **The reduced exchange program.** For a rational idempotent `U` and a prime beyond
`numbers U`, the reduction of `program U` mod every `q^b` runs as the exchange on the reduction
of `U`. -/
theorem specialize_run (hU : U * U = U) (hq : q.Prime) (hd : ∀ d ∈ numbers U, d < q) (b : ℕ)
    (s : State ι (ZMod (q ^ b))) :
    AffineFieldProgram.run ((program U).map (AffineFieldProgram.mapOp (ratMod (q ^ b)))) s =
      exchange (reduce (q ^ b) U) s := by
  obtain ⟨hK, hKi, hN, hNi, hf⟩ := numbers_admissible hq hd b
  obtain ⟨_, hl₁, hl₁', hl₂, hl₂', hi₁, hi₁', hi₂, hi₂', heq⟩ :=
    Swap.Modular.reduce_factorization_of_prime (factors U) hq hf b
  have hadm : ∀ A ∈ [U, (factors U).E₁, (factors U).E₂], Admissible (q ^ b) A := by
    intro A hA
    apply admissible_of_lt hq _ b
    intro d hdA
    apply hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    simp only [Swap.Modular.factorizationDenominators, Finset.mem_union]
    rcases hA with rfl | rfl | rfl <;> tauto
  have hUa := hadm U (by simp)
  have hidem : reduce (q ^ b) U * reduce (q ^ b) U = reduce (q ^ b) U := by
    rw [← Swap.Modular.reduce_mul _ hUa hUa, hU]
  have hP : Admissible (q ^ b) (pivotMatrix (factors U).L : Matrix ι ι ℚ) :=
    Swap.Modular.admissible_pivotMatrix _ _ ((factors U).nodup₁.of_map _)
  have hE₁ := hadm (factors U).E₁ (by simp)
  have hE₂ := hadm (factors U).E₂ (by simp)
  have hM := Swap.Modular.admissible_mul _ hE₂ hE₁
  have hcorr : reduce (q ^ b) (corr U) =
      kMat (pivotMatrix (factors U).L) (reduce (q ^ b) (factors U).E₂ * reduce (q ^ b) (factors U).E₁) := by
    rw [corr, reduce_kMat _ hP hM, Swap.Modular.reduce_pivotMatrix _ _ ((factors U).nodup₁.of_map _),
      Swap.Modular.reduce_mul _ hE₂ hE₁]
  rw [program, exchangeOps_map]
  refine exchangeOps_run _ _ _ _ _ (factors U).nodup₁ (factors U).nodup₂ hl₁ hl₁' hl₂ hl₂' hi₁ hi₁'
    hi₂ hi₂' _ heq hidem _ _ (fun t => ?_) (fun t => ?_) s
  · rw [crossQ_specialize_run _ _ hK hKi, hcorr]
  · rw [crossQ_specialize_run _ _ hN hNi, ModularFrameSchedule.reduce_neg _ hK, hcorr]

theorem specialize_legal (hq : q.Prime) (hd : ∀ d ∈ numbers U, d < q) (b : ℕ) :
    ∀ op ∈ (program U).map (AffineFieldProgram.mapOp (ratMod (q ^ b))),
      AffineFieldProgram.Legal op := by
  obtain ⟨hK, hKi, hN, hNi, hf⟩ := numbers_admissible hq hd b
  obtain ⟨_, hl₁, hl₁', hl₂, hl₂', hi₁, hi₁', hi₂, hi₂', _⟩ :=
    Swap.Modular.reduce_factorization_of_prime (factors U) hq hf b
  rw [program, exchangeOps_map]
  exact exchangeOps_legal _ _ _ _ _ hl₁ hl₁' hl₂ hl₂' hi₁ hi₁' hi₂ hi₂' _ _
    (crossQ_specialize_legal _ _ hK hKi) (crossQ_specialize_legal _ _ hN hNi)

omit [Fintype ι] [LinearOrder ι] in
theorem interchanges_map {S : Type*} (f : ℚ → S) (p : List (AffineFieldProgram.Op ι ℚ)) :
    AffineFieldProgram.interchanges (p.map (AffineFieldProgram.mapOp f)) =
      AffineFieldProgram.interchanges p := by
  induction p with
  | nil => rfl
  | cons op p ih =>
    cases op with
    | interchange i j =>
      change AffineFieldProgram.interchanges (p.map (AffineFieldProgram.mapOp f)) + 1 =
        AffineFieldProgram.interchanges p + 1
      rw [ih]
    | affineH op => exact ih
    | affineD op => exact ih
    | addToD i j => exact ih
    | subFromD i j => exact ih

/-- One prime beyond the numbers of every idempotent of a finite family. -/
theorem exists_prime_numbers (Us : Finset (Matrix ι ι ℚ)) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ U ∈ Us, ∀ d ∈ numbers U, d < q := by
  classical
  obtain ⟨q, hq, h2, hd⟩ := Swap.Modular.exists_prime_gt (Us.biUnion numbers)
  exact ⟨q, hq, h2, fun U hU d hdU => hd d (Finset.mem_biUnion.mpr ⟨U, hU, hdU⟩)⟩

/-! ### Flat coordinates -/

omit [Fintype ι] [LinearOrder ι] in
/-- A legal nonrecursive field operation expands to legal ordered steps on `H ++ D`. -/
theorem expand_legal {d : ℕ} (op : AffineFieldProgram.Op (Fin d) R)
    (hop : AffineFieldProgram.Legal op) :
    ∀ x ∈ AffineFieldCoordinates.expand op, OrderedAffine.Legal x := by
  intro x hx
  cases op with
  | affineH a =>
    cases a with
    | scale i r =>
      simp only [AffineFieldCoordinates.expand, AffineFieldCoordinates.liftH, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      subst hx; exact hop
    | shift i j r =>
      simp only [AffineFieldCoordinates.expand, AffineFieldCoordinates.liftH, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      subst hx
      exact (hop : j.val < i.val)
  | affineD a =>
    cases a with
    | scale i r =>
      simp only [AffineFieldCoordinates.expand, AffineFieldCoordinates.liftD, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      subst hx; exact hop
    | shift i j r =>
      simp only [AffineFieldCoordinates.expand, AffineFieldCoordinates.liftD, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      subst hx
      exact Nat.add_lt_add_left (hop : j.val < i.val) d
  | addToD i j =>
    simp only [AffineFieldCoordinates.expand, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact AffineFieldCoordinates.h_before_d i j
  | subFromD i j =>
    simp only [AffineFieldCoordinates.expand, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact isUnit_one.neg
    · exact AffineFieldCoordinates.h_before_d i j
  | interchange i j => simp [AffineFieldCoordinates.expand] at hx

end
end IntegerMultBounds.MathlibTM2.M8.Exchange
