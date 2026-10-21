module

public import IntegerMultBounds.MathlibTM2.M8.ReversedPivots
public import IntegerMultBounds.MathlibTM2.M8.TwistedProgram

/-!
# Stage-2 edge programs

A frame change `D_U` of the stage-1 node becomes, in the frame `diag(1, C)` with `C` the reversal
of the coordinates, the reversed exchange `revExchangeOf C U`. Its program factors `U C` once
(`revFactors`, the fixed bounded factorization `Exchange.factors (U C)`) and runs the stage-1
exchange parts on it: the transformations by the factors, the cross shears by
`revCorr U = kMat Π (R C L)` and the interchanges of the pivots (`revProgram`).

* `revProgram_run`: over `ℚ`, for every idempotent `U`, the program runs as `revExchangeOf C U`.
* `revProgram_map_run`: for a prime `q` beyond the denominators `revNumbers U` and any ring map
  `φ : ℤ/q^b → S`, the reduced program, mapped to `S`, runs as the reversed exchange of the
  mapped matrices. With an involution `σ` of `S` that fixes the image of `φ` (the atom reversal
  of `Fin f → ℤ/q^b`), the twisted run is the reversed exchange of the atom field
  (`revProgram_twRun`).
* `revProgram_interchanges`: exactly `rank U` interchanges. When `U` is generic up to its rank
  (`GenericBasis.Generic`), the interchanges are those of `revPivots m (rank U)`
  (`mem_revProgram_interchange`): one reversed block child of rank `rank U`.
* `revProgram_specialize_legal`: the reduced operations are legal.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Rev

noncomputable section
open Matrix
open IntegerMultBounds.Networks
open IntegerMultBounds.Swap.Shear (State LowerTriangular pivotMatrix)
open IntegerMultBounds.Swap.Modular (ratMod reduce Admissible denominators admissible_of_lt)
open Exchange (kMat exchangeOps crossQ factors transformOps swapOps crossOps)
open ReversedExchange (rev revPivots revExchangeOf)

variable {m : ℕ}

/-- The fixed bounded factorization of `U C`. -/
def revFactors (U : Matrix (Fin m) (Fin m) ℚ) :
    Swap.LowerTriangular.Factorization Finset.univ Finset.univ (U * rev m) :=
  factors (U * rev m)

/-- The cross correction of the reversed exchange: `kMat Π (R C L)`. -/
def revCorr (U : Matrix (Fin m) (Fin m) ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  kMat (pivotMatrix (revFactors U).L) ((revFactors U).E₂ * rev m * (revFactors U).E₁)

/-- **The stage-2 edge program** of a rational matrix. -/
def revProgram (U : Matrix (Fin m) (Fin m) ℚ) : List (AffineFieldProgram.Op (Fin m) ℚ) :=
  exchangeOps (revFactors U).E₁ (revFactors U).E₁' (revFactors U).E₂ (revFactors U).E₂'
    (revFactors U).L (crossQ (revCorr U)) (crossQ (-revCorr U))

/-- **The rational run**: the reversed exchange. -/
theorem revProgram_run (U : Matrix (Fin m) (Fin m) ℚ) (hU : U * U = U) (s : State (Fin m) ℚ) :
    AffineFieldProgram.run (revProgram U) s = revExchangeOf (rev m) U s :=
  TwistedProgram.revOps_run ReversedExchange.rev_mul_rev (revFactors U).lower₁
    (revFactors U).lower₁' (revFactors U).lower₂ (revFactors U).lower₂' _ (revFactors U).nodup₁
    (revFactors U).nodup₂ (revFactors U).inv₁ (revFactors U).inv₁' (revFactors U).inv₂
    (revFactors U).inv₂' U (revFactors U).eq hU _ _ (Exchange.crossQ_run _) (Exchange.crossQ_run _) s

/-! ### Interchanges -/

theorem rank_mul_rev (U : Matrix (Fin m) (Fin m) ℚ) : (U * rev m).rank = U.rank :=
  rank_mul_eq_left_of_isUnit_det _ _ ReversedPivots.isUnit_det_rev

/-- Exactly `rank U` interchanges. -/
theorem revProgram_interchanges (U : Matrix (Fin m) (Fin m) ℚ) :
    AffineFieldProgram.interchanges (revProgram U) = U.rank := by
  have h0 : ∀ K : Matrix (Fin m) (Fin m) ℚ, AffineFieldProgram.interchanges (crossQ K) = 0 :=
    fun K => Exchange.crossOps_interchanges _ _ _ _
  rw [revProgram, Exchange.exchangeOps_interchanges _ _ _ _ _ _ _ (h0 _) (h0 _),
    Swap.PivotRank.length_eq_rank (revFactors U), rank_mul_rev]

/-- The pivots of a generic projector's factorization are the reversed pivots. -/
theorem mem_revFactors_L (U : Matrix (Fin m) (Fin m) ℚ) (hgen : GenericBasis.Generic U U.rank)
    (p : Fin m × Fin m) : p ∈ (revFactors U).L ↔ p ∈ revPivots m U.rank := by
  set f := revFactors U
  have hL : f.L.Nodup := f.nodup₁.of_map _
  have hc : ∀ i j, (f.L.filter (ReversedPivots.inRect i j)).length = min i (min (m - j) U.rank) := by
    intro i j
    rw [← ReversedPivots.rank_mask f.E₁ f.E₁' f.E₂ f.E₂' f.lower₁ f.lower₁' f.lower₂ f.lower₂'
      f.inv₁ f.inv₂ f.L f.nodup₁ f.nodup₂ i j, ← f.eq]
    exact ReversedPivots.rank_mask_rev U hgen i j
  exact (ReversedPivots.pivots_forced f.L hL U.rank hc p).trans
    (ReversedExchange.mem_revPivots m U.rank p.1 p.2).symm

theorem not_interchange_crossOps (l : List (Fin m × Fin m)) (skip : Fin m × Fin m → Prop)
    [DecidablePred skip] (c c' : Fin m × Fin m → ℚ) (i j : Fin m) :
    AffineFieldProgram.Op.interchange i j ∉ crossOps l skip c c' := by
  intro h
  obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp h
  split_ifs at hp
  · simp at hp
  · simp [Exchange.crossEntry] at hp

theorem not_interchange_transformOps (A B : Matrix (Fin m) (Fin m) ℚ) (i j : Fin m) :
    AffineFieldProgram.Op.interchange i j ∉ transformOps A B := by
  intro h
  simp only [transformOps, AffineFieldProgram.compile, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_append, AffineFieldProgram.expand, List.mem_map] at h
  rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

/-- **One block child.** For `U` generic up to its rank, the interchanges of its program are
those of the reversed pivots `revPivots m (rank U)`. -/
theorem mem_revProgram_interchange (U : Matrix (Fin m) (Fin m) ℚ)
    (hgen : GenericBasis.Generic U U.rank) (i j : Fin m) :
    AffineFieldProgram.Op.interchange i j ∈ revProgram U ↔ (i, j) ∈ revPivots m U.rank := by
  rw [← mem_revFactors_L U hgen]
  simp only [revProgram, exchangeOps, List.mem_append, swapOps, List.mem_map]
  constructor
  · rintro ((((h | h) | ⟨p, hp, he⟩) | h) | h)
    · exact (not_interchange_transformOps _ _ i j h).elim
    · exact (not_interchange_crossOps _ _ _ _ i j h).elim
    · cases he; exact hp
    · exact (not_interchange_crossOps _ _ _ _ i j h).elim
    · exact (not_interchange_transformOps _ _ i j h).elim
  · intro h
    exact Or.inl (Or.inl (Or.inr ⟨(i, j), h, rfl⟩))

/-! ### Reduction mod a prime power and the atom ring -/

/-- The denominators that the reduction must avoid. -/
def revNumbers (U : Matrix (Fin m) (Fin m) ℚ) : Finset ℕ :=
  Swap.Modular.factorizationDenominators (revFactors U) ∪ denominators (revCorr U) ∪
    denominators ((revCorr U).map (·⁻¹)) ∪ denominators (-revCorr U) ∪
    denominators ((-revCorr U).map (·⁻¹)) ∪ denominators U ∪ denominators (rev m : Matrix (Fin m) (Fin m) ℚ)

variable {U : Matrix (Fin m) (Fin m) ℚ} {q : ℕ}

theorem revNumbers_admissible (hq : q.Prime) (hd : ∀ d ∈ revNumbers U, d < q) (b : ℕ) :
    Admissible (q ^ b) (revCorr U) ∧ Admissible (q ^ b) ((revCorr U).map (·⁻¹)) ∧
      Admissible (q ^ b) (-revCorr U) ∧ Admissible (q ^ b) ((-revCorr U).map (·⁻¹)) ∧
      Admissible (q ^ b) U ∧ Admissible (q ^ b) (rev m : Matrix (Fin m) (Fin m) ℚ) ∧
      ∀ d ∈ Swap.Modular.factorizationDenominators (revFactors U), d < q := by
  refine ⟨admissible_of_lt hq (fun d h => hd d ?_) b, admissible_of_lt hq (fun d h => hd d ?_) b,
    admissible_of_lt hq (fun d h => hd d ?_) b, admissible_of_lt hq (fun d h => hd d ?_) b,
    admissible_of_lt hq (fun d h => hd d ?_) b, admissible_of_lt hq (fun d h => hd d ?_) b,
    fun d h => hd d ?_⟩ <;> simp only [revNumbers, Finset.mem_union] <;> tauto

section Ring

variable {S : Type*} [CommRing S] (φ : ZMod (q ^ b) →+* S)

theorem lower_map {A : Matrix (Fin m) (Fin m) (ZMod (q ^ b))} (hA : LowerTriangular A) :
    LowerTriangular (A.map φ) := fun i j h => by
  rw [Matrix.map_apply, hA i j h, map_zero]

theorem pivot_map (L : List (Fin m × Fin m)) :
    (pivotMatrix L : Matrix (Fin m) (Fin m) (ZMod (q ^ b))).map φ = pivotMatrix L := by
  induction L with
  | nil => exact Matrix.map_zero φ (map_zero φ)
  | cons p L ih =>
    simp only [pivotMatrix]
    rw [Matrix.map_add _ (map_add φ), ih]
    congr 1
    ext a c
    simp only [Matrix.map_apply, Matrix.single, Matrix.of_apply]
    split_ifs <;> simp

theorem kMat_map (P M : Matrix (Fin m) (Fin m) (ZMod (q ^ b))) :
    (kMat P M).map φ = kMat (P.map φ) (M.map φ) := by
  simp only [kMat, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ), Matrix.map_mul,
    Matrix.transpose_map]

/-- The cross program of `K`, reduced and mapped to `S`, adds the image of the reduction. -/
theorem crossQ_map_run (K : Matrix (Fin m) (Fin m) ℚ) (hK : Admissible (q ^ b) K)
    (hK' : Admissible (q ^ b) (K.map (·⁻¹))) (s : State (Fin m) S) :
    AffineFieldProgram.run (((crossQ K).map (AffineFieldProgram.mapOp (ratMod (q ^ b)))).map
      (AffineFieldProgram.mapOp φ)) s = Exchange.cross ((reduce (q ^ b) K).map φ) s := by
  rw [crossQ, Exchange.crossOps_map, Exchange.crossOps_map, Exchange.crossOps_run, Exchange.sum_allPairs]
  · rfl
  · intro p hp
    simp only [hp, Swap.Modular.ratMod_zero, map_zero]
  · intro p hp
    rw [← map_mul, ← Swap.Modular.ratMod_mul (q ^ b) (x := K p.2 p.1) (y := (K p.2 p.1)⁻¹)
      (hK p.2 p.1) (hK' p.2 p.1), mul_inv_cancel₀ hp, Swap.Modular.ratMod_one, map_one]

/-- **The reduced program over a ring.** For a rational idempotent `U` and a prime beyond
`revNumbers U`, the reduced program mapped by any ring map runs as the reversed exchange of the
mapped matrices. -/
theorem revProgram_map_run (hU : U * U = U) (hq : q.Prime) (hd : ∀ d ∈ revNumbers U, d < q)
    (s : State (Fin m) S) :
    AffineFieldProgram.run (((revProgram U).map (AffineFieldProgram.mapOp (ratMod (q ^ b)))).map
      (AffineFieldProgram.mapOp φ)) s =
      revExchangeOf ((reduce (q ^ b) (rev m)).map φ) ((reduce (q ^ b) U).map φ) s := by
  obtain ⟨hK, hKi, hN, hNi, hUa, hCa, hf⟩ := revNumbers_admissible hq hd b
  obtain ⟨_, hl₁, hl₁', hl₂, hl₂', hi₁, hi₁', hi₂, hi₂', heq⟩ :=
    Swap.Modular.reduce_factorization_of_prime (revFactors U) hq hf b
  set f := revFactors U
  have hadm : ∀ A ∈ [f.E₁, f.E₂], Admissible (q ^ b) A := by
    intro A hA
    apply admissible_of_lt hq _ b
    intro d hdA
    apply hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    simp only [Swap.Modular.factorizationDenominators, Finset.mem_union]
    rcases hA with rfl | rfl <;> tauto
  have hE₁ := hadm f.E₁ (by simp)
  have hE₂ := hadm f.E₂ (by simp)
  have hPv : Admissible (q ^ b) (pivotMatrix f.L : Matrix (Fin m) (Fin m) ℚ) :=
    Swap.Modular.admissible_pivotMatrix _ _ (f.nodup₁.of_map _)
  have hM := Swap.Modular.admissible_mul _ (Swap.Modular.admissible_mul _ hE₂ hCa) hE₁
  have mi (A B : Matrix (Fin m) (Fin m) (ZMod (q ^ b))) (h : A * B = 1) : A.map φ * B.map φ = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hC : (reduce (q ^ b) (rev m)).map φ * (reduce (q ^ b) (rev m)).map φ = 1 := by
    apply mi
    rw [← Swap.Modular.reduce_mul _ hCa hCa, ReversedExchange.rev_mul_rev, Swap.Modular.reduce_one]
  have hidem : (reduce (q ^ b) U).map φ * (reduce (q ^ b) U).map φ = (reduce (q ^ b) U).map φ := by
    rw [← Matrix.map_mul, ← Swap.Modular.reduce_mul _ hUa hUa, hU]
  have hP : (reduce (q ^ b) U).map φ * (reduce (q ^ b) (rev m)).map φ =
      (reduce (q ^ b) f.E₁).map φ * pivotMatrix f.L * (reduce (q ^ b) f.E₂).map φ := by
    rw [← Matrix.map_mul, ← Swap.Modular.reduce_mul _ hUa hCa, heq, Matrix.map_mul, Matrix.map_mul,
      pivot_map]
  have hcorr : (reduce (q ^ b) (revCorr U)).map φ = kMat (pivotMatrix f.L)
      ((reduce (q ^ b) f.E₂).map φ * (reduce (q ^ b) (rev m)).map φ * (reduce (q ^ b) f.E₁).map φ) := by
    rw [revCorr, Exchange.reduce_kMat _ hPv hM, kMat_map,
      Swap.Modular.reduce_pivotMatrix _ _ (f.nodup₁.of_map _), pivot_map,
      Swap.Modular.reduce_mul _ (Swap.Modular.admissible_mul _ hE₂ hCa) hE₁,
      Swap.Modular.reduce_mul _ hE₂ hCa, Matrix.map_mul, Matrix.map_mul]
  rw [revProgram, Exchange.exchangeOps_map, Exchange.exchangeOps_map]
  refine TwistedProgram.revOps_run hC (lower_map φ hl₁) (lower_map φ hl₁') (lower_map φ hl₂)
    (lower_map φ hl₂') _ f.nodup₁ f.nodup₂ (mi _ _ hi₁) (mi _ _ hi₁') (mi _ _ hi₂) (mi _ _ hi₂')
    _ hP hidem _ _ (fun t => ?_) (fun t => ?_) s
  · rw [crossQ_map_run φ _ hK hKi, hcorr]
  · rw [crossQ_map_run φ _ hN hNi, ModularFrameSchedule.reduce_neg (q ^ b) hK, Matrix.map_neg _ (map_neg φ),
      hcorr]

/-- **The twisted run on the atom field.** With an involution `σ` of `S` fixing the image of
`φ`, the reduced program, mapped to `S` and run twisted, is the reversed exchange of the atom
field: the reversed exchange of the mapped matrices conjugated by the twist of the tail. -/
theorem revProgram_twRun (hU : U * U = U) (hq : q.Prime) (hd : ∀ d ∈ revNumbers U, d < q)
    {σ : S →+* S} (hσ : ∀ x, σ (σ x) = x) (hφ : ∀ c, σ (φ c) = φ c) (s : State (Fin m) S) :
    TwistedProgram.twRun σ (((revProgram U).map (AffineFieldProgram.mapOp (ratMod (q ^ b)))).map
      (AffineFieldProgram.mapOp φ)) s =
      TwistedExchange.conj σ (revExchangeOf ((reduce (q ^ b) (rev m)).map φ) ((reduce (q ^ b) U).map φ)
        (TwistedExchange.conj σ s)) := by
  rw [TwistedProgram.twRun_eq hσ (fun op hop => by
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hop
    exact TwistedProgram.fixedOp_mapOp hφ o), revProgram_map_run φ hU hq hd]

end Ring

/-- The reduced operations are legal. -/
theorem revProgram_specialize_legal (hq : q.Prime) (hd : ∀ d ∈ revNumbers U, d < q) (b : ℕ) :
    ∀ op ∈ (revProgram U).map (AffineFieldProgram.mapOp (ratMod (q ^ b))),
      AffineFieldProgram.Legal op := by
  obtain ⟨hK, hKi, hN, hNi, -, -, hf⟩ := revNumbers_admissible hq hd b
  obtain ⟨_, hl₁, hl₁', hl₂, hl₂', hi₁, hi₁', hi₂, hi₂', _⟩ :=
    Swap.Modular.reduce_factorization_of_prime (revFactors U) hq hf b
  rw [revProgram, Exchange.exchangeOps_map]
  exact Exchange.exchangeOps_legal _ _ _ _ _ hl₁ hl₁' hl₂ hl₂' hi₁ hi₁' hi₂ hi₂' _ _
    (Exchange.crossQ_specialize_legal _ _ hK hKi) (Exchange.crossQ_specialize_legal _ _ hN hNi)

/-- One prime beyond the numbers of every matrix of a finite family. -/
theorem exists_prime_revNumbers (Us : Finset (Matrix (Fin m) (Fin m) ℚ)) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ U ∈ Us, ∀ d ∈ revNumbers U, d < q := by
  classical
  obtain ⟨q, hq, h2, hd⟩ := Swap.Modular.exists_prime_gt (Us.biUnion revNumbers)
  exact ⟨q, hq, h2, fun U hU d hdU => hd d (Finset.mem_biUnion.mpr ⟨U, hU, hdU⟩)⟩

end

end IntegerMultBounds.MathlibTM2.M8.Rev
