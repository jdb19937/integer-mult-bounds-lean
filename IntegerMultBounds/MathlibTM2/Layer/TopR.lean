module

public import IntegerMultBounds.MathlibTM2.Layer.LayerR

/-!
# The top of a round with rounded pieces

`topR` is `topZ` with the pieces run by the rounded layer `layerR` and the input multiplied by
`2^g` (guard bits) after the phase. `topR_err`: every output entry is within
`√2 + √2 · piecesErr / 2^s` of the normalized butterflies `Hl` on the selected bits, for the shift
`s = ⌈D/2⌉ + |top| + Σ scaleR + g`. With enough guard bits the second term is at most one, so
the round is within `√2 + 1` of `Hl` entrywise, against `√2` for the exact layer.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks ComplexFramedExecution

variable {R r n : ℕ}

/-- One rounded piece. -/
noncomputable def pieceR (u : ℕ) (ds : Directions) (R₀ j : ℕ) {R₂ : ℕ} (hR : R₂ = rowsAt R₀ j)
    (e : Fin (bits u j) → Fin n) (Z : ZArr (Fin R₂ × Fin r) n) : ZArr (Fin R₂ × Fin r) n :=
  fun p => layerR u ds R₀ j e (fun q => Z ((Fin.cast hR.symm q.1.1, q.1.2), q.2))
    ((Fin.cast hR p.1.1, p.1.2), p.2)

/-- Run the rounded pieces in order. -/
noncomputable def piecesR (ds : Directions) {R₂ : ℕ} :
    List (Piece n R₂) → ZArr (Fin R₂ × Fin r) n → ZArr (Fin R₂ × Fin r) n
  | [], Z => Z
  | P :: Ps, Z => piecesR ds Ps (pieceR P.u ds P.R₀ P.j P.hR P.e Z)

/-- The scale of a rounded piece. -/
noncomputable def Piece.expR {R₂ : ℕ} (ds : Directions) (P : Piece n R₂) : ℕ := scaleR P.u ds P.j

/-- The error bound of the rounded pieces: each piece's error, multiplied by the scales of the
pieces after it. -/
noncomputable def piecesErr (ds : Directions) (r : ℕ) {R₂ : ℕ} : List (Piece n R₂) → ℝ
  | [] => 0
  | P :: Ps => (2 : ℝ) ^ (Ps.map (Piece.expR ds)).sum * errL P.u ds P.R₀ r n P.j + piecesErr ds r Ps

/-- The rounded layer on its top: the input after the phase, times `2^g`, the kernels on `top`,
the rounded pieces, the phase, the unit and the shift by `2^s`. -/
noncomputable def topR (ds : Directions) (a : ℕ) (low : List (Fin n)) (top : List (Fin (n + a)))
    {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂) (Ps : List (Piece n R₂)) (g s : ℕ)
    (Z : ZArr (Fin R × Fin r) (n + a)) : ZArr (Fin R × Fin r) (n + a) :=
  let sel : List (Fin (n + a)) := low.map (Fin.castAdd a) ++ top
  let Z₁ : ZArr (Fin R × Fin r) (n + a) := fun p => (2 ^ g : GaussianInt) * sZ sel Z p
  let Z₂ := k2s top Z₁
  let Z₃ := ofRows a (unpadRows hR₂ (piecesR ds Ps (padRows R₂ (toRows a Z₂))))
  let Z₄ := sZ sel Z₃
  fun p => tdivZ s (unitD sel.length * Z₄ p)

/-! ### The pieces -/

lemma l2_Cl {X : Type} [Fintype X] (l : List (Fin n)) (f : Arr X n) : l2 (Cl X l f) = l2 f :=
  l2_prod_kBit l f

lemma pieceR_err (u : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (R₀ j : ℕ)
    {R₂ : ℕ} (hR : R₂ = rowsAt R₀ j) (e : Fin (bits u j) → Fin n) (he : Function.Injective e)
    (W : ZArr (Fin R₂ × Fin r) n) :
    l2 (toC (pieceR u ds R₀ j hR e W) -
      (2 : ℂ) ^ scaleR u ds j • Cl _ ((List.finRange (bits u j)).map e) (toC W)) ≤
      errL u ds R₀ r n j := by
  subst hR
  rw [Cl, List.map_map]
  exact layerR_err u ds hd R₀ j e he W

/-- The rounded pieces are within `piecesErr` of `2 ^ (Σ scaleR)` times the kernels on their
bits. -/
lemma piecesR_err (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) {R₂ : ℕ}
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (W : ZArr (Fin R₂ × Fin r) n) :
    l2 (toC (piecesR ds Ps W) -
      (2 : ℂ) ^ (Ps.map (Piece.expR ds)).sum • Cl _ (Ps.flatMap Piece.bitsList) (toC W)) ≤
      piecesErr ds r Ps := by
  induction Ps generalizing W with
  | nil => simp [piecesR, piecesErr, Cl]; unfold l2; simp
  | cons P Ps ih =>
    simp only [piecesR, piecesErr]
    set X := pieceR P.u ds P.R₀ P.j P.hR P.e W
    set E' := (Ps.map (Piece.expR ds)).sum
    have h1 := ih (fun Q hQ => hinj Q (List.mem_cons_of_mem _ hQ)) X
    have h2 := pieceR_err P.u ds hd P.R₀ P.j P.hR P.e (hinj P List.mem_cons_self) W
    have hcl : Cl _ ((P :: Ps).flatMap Piece.bitsList) (toC W) =
        Cl _ (Ps.flatMap Piece.bitsList) (Cl _ P.bitsList (toC W)) := by
      rw [List.flatMap_cons, Cl_perm List.perm_append_comm, Cl_append]
    have hsum : ((P :: Ps).map (Piece.expR ds)).sum = scaleR P.u ds P.j + E' := by
      simp [Piece.expR, E']
    rw [hcl, hsum]
    have hsplit : toC (piecesR ds Ps X) -
        (2 : ℂ) ^ (scaleR P.u ds P.j + E') • Cl _ (Ps.flatMap Piece.bitsList)
          (Cl _ P.bitsList (toC W)) =
        (toC (piecesR ds Ps X) - (2 : ℂ) ^ E' • Cl _ (Ps.flatMap Piece.bitsList) (toC X)) +
          (2 : ℂ) ^ E' • Cl _ (Ps.flatMap Piece.bitsList)
            (toC X - (2 : ℂ) ^ scaleR P.u ds P.j • Cl _ P.bitsList (toC W)) := by
      rw [map_sub, map_smul, smul_sub, smul_smul, ← pow_add, add_comm E']; abel
    rw [hsplit]
    refine (l2_add_le _ _).trans ?_
    rw [l2_smul, l2_Cl, norm_pow, RCLike.norm_two]
    have h2' : l2 (toC X - (2 : ℂ) ^ scaleR P.u ds P.j • Cl _ P.bitsList (toC W)) ≤
        errL P.u ds P.R₀ r n P.j := by
      unfold Piece.bitsList; exact h2
    have hp : (0 : ℝ) ≤ 2 ^ E' := by positivity
    nlinarith

/-! ### Reindexing complex arrays -/

lemma unpad_pad_C {R₂ : ℕ} (h : R ≤ R₂) (l : List (Fin n)) (c : ℂ) (W : ZArr (Fin R × Fin r) n)
    (p : (Fin R × Fin r) × (Fin n → ZMod 2)) :
    (c • Cl _ l (toC (padRows R₂ W))) ((Fin.castLE h p.1.1, p.1.2), p.2) =
      (c • Cl _ l (toC W)) p := by
  let φ : Fin R × Fin r → Fin R₂ × Fin r := fun z => (Fin.castLE h z.1, z.2)
  have h2 : (fun q : (Fin R × Fin r) × (Fin n → ZMod 2) => toC (padRows R₂ W) (φ q.1, q.2)) =
      toC W := by
    funext q
    simp [toC, padRows, φ]
  rw [Pi.smul_apply, Pi.smul_apply, ← h2]
  exact congrArg (c • ·) (congrFun (prod_respec φ 1 l _) p)

lemma ofRows_C (a : ℕ) (l : List (Fin n)) (c : ℂ) (Z : ZArr (Fin R × Fin r) (n + a))
    (p : (Fin R × Fin r) × (Fin (n + a) → ZMod 2)) :
    (c • Cl _ l (toC (toRows a Z))) (ofRowsIdx a p) = (c • Cl _ (l.map (Fin.castAdd a)) (toC Z)) p := by
  have hZ : (fun p => toC (toRows a Z) (ofRowsIdx a p)) = toC Z := by
    change toC (ofRows a (toRows a Z)) = toC Z
    rw [ofRows_toRows]
  rw [Pi.smul_apply, Pi.smul_apply, ← hZ, ← prod_ofRows]

/-- The source cell of `toRows`. -/
def toRowsIdx (a : ℕ) (x : (Fin (R * 2 ^ a) × Fin r) × (Fin n → ZMod 2)) :
    (Fin R × Fin r) × (Fin (n + a) → ZMod 2) :=
  ((⟨x.1.1 / 2 ^ a, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq x.1.1.2 (Nat.mul_comm _ _))⟩, x.1.2),
    Fin.append x.2 (addrBits a (x.1.1 % 2 ^ a)))

lemma toRowsIdx_ofRowsIdx (a : ℕ) (p : (Fin R × Fin r) × (Fin (n + a) → ZMod 2)) :
    toRowsIdx a (ofRowsIdx a p) = p := by
  classical
  by_contra hc
  have h := congrFun (ofRows_toRows a (fun q => if q = p then (1 : GaussianInt) else 0)) p
  rw [ofRows_apply, show toRows a (fun q => if q = p then (1 : GaussianInt) else 0)
    (ofRowsIdx a p) = if toRowsIdx a (ofRowsIdx a p) = p then 1 else 0 from rfl] at h
  simp [hc] at h

lemma ofRowsIdx_injective (a : ℕ) :
    Function.Injective (ofRowsIdx (R := R) (r := r) (n := n) a) := fun p q h => by
  rw [← toRowsIdx_ofRowsIdx a p, h, toRowsIdx_ofRowsIdx]

/-! ### The phase and the unit -/

lemma norm_Sl_apply {X : Type} (l : List (Fin n)) (F : Arr X n) (p : X × (Fin n → ZMod 2)) :
    ‖Sl X l F p‖ = ‖F p‖ := by
  induction l generalizing F with
  | nil => simp [Sl]
  | cons t l ih =>
    simp only [Sl, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    change ‖sBit t _ p‖ = _
    simp only [sBit, LinearMap.coe_mk, AddHom.coe_mk, norm_mul]
    rw [ih]
    split_ifs <;> simp

lemma norm_unitD_le (D : ℕ) : ‖GaussianInt.toComplex (unitD D)‖ ≤ √2 := by
  have h1 : ‖(1 : ℂ) - Complex.I‖ = √2 := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp; norm_num
  simp only [unitD, map_mul, map_pow, norm_mul, norm_pow, GaussianInt.toComplex_def']
  have hi : ‖((0 : ℤ) : ℂ) + ((-1 : ℤ) : ℂ) * Complex.I‖ = 1 := by simp
  have ho : ‖((1 : ℤ) : ℂ) + ((-1 : ℤ) : ℂ) * Complex.I‖ = √2 := by
    rw [← h1]; congr 1; push_cast; ring
  rw [hi, ho, one_pow, one_mul]
  rcases Nat.mod_two_eq_zero_or_one D with h | h
  · rw [h, pow_zero]; exact (Real.one_lt_sqrt_two).le
  · rw [h, pow_one]

/-! ### The error of the top -/

/-- **The rounded top.** Every entry is within `√2 + √2 piecesErr / 2^s` of `Hl` on the selected
bits, for the shift `s = ⌈D/2⌉ + |top| + Σ scaleR + g`. -/
theorem topR_err (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (a : ℕ)
    (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂)
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup) (g s : ℕ)
    (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.expR ds)).sum + g)
    (Z : ZArr (Fin R × Fin r) (n + a)) (p : (Fin R × Fin r) × (Fin (n + a) → ZMod 2)) :
    ‖GaussianInt.toComplex (topR ds a low top hR₂ Ps g s Z p) -
      Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p‖ ≤
      √2 + √2 * piecesErr ds r Ps / 2 ^ s := by
  set sel : List (Fin (n + a)) := low.map (Fin.castAdd a) ++ top with hsel_def
  set L := Ps.flatMap Piece.bitsList
  set E := (Ps.map (Piece.expR ds)).sum
  set Z₁ : ZArr (Fin R × Fin r) (n + a) := fun p => (2 ^ g : GaussianInt) * sZ sel Z p
  set Z₂ := k2s top Z₁
  set W := padRows R₂ (toRows a Z₂)
  set X := piecesR ds Ps W
  set Z₃ := ofRows a (unpadRows hR₂ X)
  set D := sel.length with hD
  set F := Sl _ sel (Cl _ sel (Sl _ sel (toC Z)))
  have hZ₁ : toC Z₁ = (2 : ℂ) ^ g • Sl _ sel (toC Z) := by
    funext q; simp only [Z₁, toC, map_mul, map_pow, Pi.smul_apply, smul_eq_mul]
    rw [← toC_sZ]; simp [toC, toComplex_two]
  have hZ₂ : toC Z₂ = (2 : ℂ) ^ (top.length + g) • Cl _ top (Sl _ sel (toC Z)) := by
    rw [toC_k2s, prod_reverse_kBit, hZ₁, map_smul, smul_smul, ← pow_add]; rfl
  -- the exact value of the third stage
  set G : Arr (Fin R × Fin r) (n + a) := (2 : ℂ) ^ (E + top.length + g) • Cl _ sel (Sl _ sel (toC Z))
  have hG : ∀ q, ((2 : ℂ) ^ E • Cl _ L (toC W)) ((Fin.castLE hR₂ (ofRowsIdx a q).1.1,
      (ofRowsIdx a q).1.2), (ofRowsIdx a q).2) = G q := by
    intro q
    rw [unpad_pad_C hR₂ L _ _ (ofRowsIdx a q), ofRows_C, Cl_perm (hcover.map _), hZ₂, map_smul,
      smul_smul, ← pow_add]
    simp only [Pi.smul_apply, G, hsel_def, Cl_append]
    congr 2; ring
  -- the third stage is within `piecesErr` of `G`
  have hX := piecesR_err ds hd Ps hinj W
  have hZ₃ : ‖toC Z₃ p - G p‖ ≤ piecesErr ds r Ps := by
    have : toC Z₃ p - G p = (toC X - (2 : ℂ) ^ E • Cl _ L (toC W))
        ((Fin.castLE hR₂ (ofRowsIdx a p).1.1, (ofRowsIdx a p).1.2), (ofRowsIdx a p).2) := by
      rw [Pi.sub_apply, hG]; rfl
    rw [this]
    exact (norm_le_l2 _ _).trans hX
  -- the exact identity of the top
  have hH : Hl _ sel (toC Z) p = ((1 - Complex.I) / 2) ^ D * F p := by
    rw [Hl_eq sel hsel]; rfl
  have hDlen : D = low.length + top.length := by
    rw [hD, hsel_def, List.length_append, List.length_map]
  have hexact : GaussianInt.toComplex (unitD D) * Sl _ sel G p = (2 : ℂ) ^ s * Hl _ sel (toC Z) p := by
    have hSG : Sl _ sel G p = (2 : ℂ) ^ (E + top.length + g) * F p := by
      simp only [G, map_smul, Pi.smul_apply, smul_eq_mul]; rfl
    rw [hSG, hH, div_pow, one_sub_I_pow, hs, ← hDlen]
    have h2D : (2 : ℂ) ^ ((D + 1) / 2) * 2 ^ (D / 2) = 2 ^ D := by
      rw [← pow_add]; congr 1; omega
    have h2 : (2 : ℂ) ^ D ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [pow_add, pow_add, pow_add]
    field_simp
    linear_combination (-(GaussianInt.toComplex (unitD D) * F p * 2 ^ E * 2 ^ top.length)) * h2D
  -- assemble
  set x := GaussianInt.toComplex (unitD D * sZ sel Z₃ p)
  have hx : x = GaussianInt.toComplex (unitD D) * Sl _ sel (toC Z₃) p := by
    simp only [x, map_mul]; rw [← toC_sZ]; rfl
  have hT := norm_tdivZ_sub_le s (unitD D * sZ sel Z₃ p)
  have hpos : (0 : ℝ) < 2 ^ s := by positivity
  have hdiff : ‖x / 2 ^ s - Hl _ sel (toC Z) p‖ ≤ √2 * piecesErr ds r Ps / 2 ^ s := by
    have e1 : x / 2 ^ s - Hl _ sel (toC Z) p =
        GaussianInt.toComplex (unitD D) * Sl _ sel (toC Z₃ - G) p / 2 ^ s := by
      have hH' : Hl _ sel (toC Z) p = GaussianInt.toComplex (unitD D) * Sl _ sel G p / 2 ^ s := by
        rw [eq_div_iff (pow_ne_zero _ two_ne_zero), hexact]; ring
      rw [hH', hx, ← sub_div, ← mul_sub, map_sub, Pi.sub_apply]
    rw [e1, norm_div, norm_mul, norm_Sl_apply, norm_pow, RCLike.norm_two, Pi.sub_apply]
    have hu := norm_unitD_le D
    apply div_le_div_of_nonneg_right _ hpos.le
    exact mul_le_mul hu hZ₃ (norm_nonneg _) (Real.sqrt_nonneg _)
  have e2 : GaussianInt.toComplex (topR ds a low top hR₂ Ps g s Z p) - Hl _ sel (toC Z) p =
      (GaussianInt.toComplex (tdivZ s (unitD D * sZ sel Z₃ p)) - x / 2 ^ s) +
        (x / 2 ^ s - Hl _ sel (toC Z) p) := by
    simp only [topR]; abel
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  linarith

end IntegerMultBounds.MathlibTM2.Layer
