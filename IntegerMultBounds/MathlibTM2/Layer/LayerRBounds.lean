module

public import IntegerMultBounds.MathlibTM2.Layer.TopR
import Mathlib.Tactic.Positivity.Finset

/-!
# The size of the rounding error of a round

`errL_le`: the error bound of the rounded layer at level `j` grows at most like
`j · B · A^j`, with `A = lipProd · (facCount + 1)` the gain of one level and
`B = √2 · √(rows · r · 2^n)` the truncation error of one level. `errL_le_two_pow` restates it
with powers of two, and `piecesErr_div_le` bounds the error term of `topR_err` by the sum of
the piece errors over `2^g`. Together they give the number of guard bits that make the error
term of a round at most one (`topR_err_guard`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks ComplexFramedExecution

variable {r n : ℕ}

lemma rowsAt_le_succ (R₀ j : ℕ) : rowsAt R₀ j ≤ rowsAt R₀ (j + 1) := by
  show rowsAt R₀ j ≤ NW * rowsAt R₀ j
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_neZero NW)

/-- The gain of one level of the rounded layer. -/
noncomputable def gainL (ds : Directions) : ℝ :=
  lipProd (program ds) * (facCount (program ds) + 1)

lemma one_le_gainL (ds : Directions) : 1 ≤ gainL ds := by
  have h1 := one_le_lipProd (program ds)
  have h2 : (1 : ℝ) ≤ facCount (program ds) + 1 := by
    have := (facCount (program ds)).cast_nonneg (α := ℝ); linarith
  unfold gainL
  nlinarith

lemma errL_step_arith {E E' L F S b B A : ℝ} {j : ℕ} (hstep : E' ≤ L * F * (b + E / S))
    (ih : E ≤ j * b * A ^ j) (hE : 0 ≤ E) (hS : 1 ≤ S) (hb : 0 ≤ b) (hbB : b ≤ B)
    (hL : 1 ≤ L) (hA : L * (F + 1) = A) (hA1 : 1 ≤ A) :
    E' ≤ ((j : ℝ) + 1) * B * A ^ (j + 1) := by
  have hdiv : E / S ≤ E := div_le_self hE hS
  have hAj : 1 ≤ A ^ j := one_le_pow₀ hA1
  have hB : 0 ≤ B := hb.trans hbB
  have h1 : b + E / S ≤ B + j * B * A ^ j := by
    have : (j : ℝ) * b * A ^ j ≤ j * B * A ^ j := by gcongr
    linarith
  have h2 : L * F ≤ A := by
    rw [← hA]
    have : F ≤ F + 1 := by linarith
    gcongr
  have hL0 : 0 ≤ L := by linarith
  calc E' ≤ (L * F) * (b + E / S) := hstep
    _ ≤ A * (B + j * B * A ^ j) := by
        gcongr
    _ ≤ ((j : ℝ) + 1) * B * A ^ (j + 1) := by
        have : B ≤ B * A ^ j := le_mul_of_one_le_right hB hAj
        rw [pow_succ]; nlinarith

/-- **The growth of the layer error.** -/
theorem errL_le (u : ℕ) (ds : Directions) (R₀ r n : ℕ) :
    ∀ j, errL u ds R₀ r n j ≤ j * (√2 * √(rowsAt R₀ j * r * 2 ^ n)) * gainL ds ^ j
  | 0 => by simp [errL]
  | j + 1 => by
    have hR : (rowsAt R₀ j : ℝ) ≤ rowsAt R₀ (j + 1) := by exact_mod_cast rowsAt_le_succ R₀ j
    have hBj : √2 * √(rowsAt R₀ j * r * 2 ^ n) ≤ √2 * √(rowsAt R₀ (j + 1) * r * 2 ^ n) := by
      gcongr
    push_cast
    exact errL_step_arith (errL_succ_le u ds R₀ r n j) (errL_le u ds R₀ r n j)
      (errL_nonneg u ds R₀ r n j) (one_le_pow₀ (by norm_num)) (by positivity) hBj
      (one_le_lipProd _) rfl (one_le_gainL ds)

/-- The growth of the layer error in powers of two: with `gainL ≤ 2^a` and a truncation error
of at most `2^b` per level, `errL j ≤ 2^(j + b + a j)`. -/
theorem errL_le_two_pow (u : ℕ) (ds : Directions) (R₀ r n j a b : ℕ)
    (ha : gainL ds ≤ 2 ^ a) (hB : √2 * √(rowsAt R₀ j * r * 2 ^ n) ≤ 2 ^ b) :
    errL u ds R₀ r n j ≤ 2 ^ (j + b + a * j) := by
  refine (errL_le u ds R₀ r n j).trans ?_
  have hj : (j : ℝ) ≤ 2 ^ j := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hA : gainL ds ^ j ≤ (2 ^ a) ^ j := pow_le_pow_left₀ (by linarith [one_le_gainL ds]) ha j
  have h0 : 0 ≤ gainL ds ^ j := pow_nonneg (by linarith [one_le_gainL ds]) _
  rw [pow_add, pow_add, pow_mul]
  gcongr

/-- The number of bits of the gain of one level. -/
noncomputable def cGain (ds : Directions) : ℕ := Nat.clog 2 ⌈gainL ds⌉₊

lemma gainL_le_two_pow (ds : Directions) : gainL ds ≤ 2 ^ cGain ds := by
  have h1 := Nat.le_ceil (gainL ds)
  have h2 : ⌈gainL ds⌉₊ ≤ 2 ^ cGain ds := Nat.le_pow_clog (by norm_num) _
  have h3 : ((⌈gainL ds⌉₊ : ℕ) : ℝ) ≤ ((2 ^ cGain ds : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  linarith

lemma lipProd_le_two_pow (ds : Directions) : lipProd (program ds) ≤ 2 ^ cGain ds := by
  refine le_trans ?_ (gainL_le_two_pow ds)
  unfold gainL
  have h1 := one_le_lipProd (program ds)
  have h2 : (0 : ℝ) ≤ facCount (program ds) := Nat.cast_nonneg _
  nlinarith

/-- **The level errors in the agreed form.** With `2 rows r 2^n ≤ 2^Lb` and `j ≤ D`,
`errL j ≤ 2^(Lb + D (cGain + 1))`. -/
theorem errL_le_K (u : ℕ) (ds : Directions) (R₀ r n j Lb D : ℕ) (hj : j ≤ D)
    (hrows : 2 * (rowsAt R₀ j * r * 2 ^ n) ≤ 2 ^ Lb) :
    errL u ds R₀ r n j ≤ 2 ^ (Lb + D * (cGain ds + 1)) := by
  have hB : √2 * √(rowsAt R₀ j * r * 2 ^ n) ≤ 2 ^ Lb := by
    rw [← Real.sqrt_mul (by norm_num)]
    have h1 : (2 : ℝ) * (rowsAt R₀ j * r * 2 ^ n) ≤ 2 ^ Lb := by exact_mod_cast hrows
    have h2 : (2 : ℝ) ^ Lb ≤ (2 ^ Lb) ^ 2 := by
      have : (1 : ℝ) ≤ 2 ^ Lb := one_le_pow₀ (by norm_num)
      nlinarith
    rw [Real.sqrt_le_left (by positivity)]
    linarith
  refine (errL_le_two_pow u ds R₀ r n j (cGain ds) Lb (gainL_le_two_pow ds) hB).trans ?_
  apply pow_le_pow_right₀ (by norm_num)
  have : j * (cGain ds + 1) ≤ D * (cGain ds + 1) := Nat.mul_le_mul_right _ hj
  nlinarith

lemma piecesErr_nonneg (ds : Directions) (r : ℕ) {R₂ : ℕ} :
    ∀ Ps : List (Piece n R₂), 0 ≤ piecesErr ds r Ps
  | [] => le_rfl
  | P :: Ps => add_nonneg (mul_nonneg (by positivity) (errL_nonneg _ _ _ _ _ _))
      (piecesErr_nonneg ds r Ps)

/-- The error term of `topR_err` is at most the sum of the piece errors over `2^g`. -/
lemma piecesErr_le (ds : Directions) (r : ℕ) {R₂ : ℕ} :
    ∀ Ps : List (Piece n R₂), piecesErr ds r Ps ≤
      2 ^ (Ps.map (Piece.expR ds)).sum * (Ps.map fun P => errL P.u ds P.R₀ r n P.j).sum
  | [] => by simp [piecesErr]
  | P :: Ps => by
    have ih := piecesErr_le ds r Ps
    have hE := errL_nonneg P.u ds P.R₀ r n P.j
    have hS : 0 ≤ (Ps.map fun P => errL P.u ds P.R₀ r n P.j).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx; exact errL_nonneg _ _ _ _ _ _
    simp only [piecesErr, List.map_cons, List.sum_cons, mul_add]
    have h2 : (2 : ℝ) ^ (Ps.map (Piece.expR ds)).sum * (Ps.map fun P => errL P.u ds P.R₀ r n P.j).sum ≤
        2 ^ (P.expR ds + (Ps.map (Piece.expR ds)).sum) *
          (Ps.map fun P => errL P.u ds P.R₀ r n P.j).sum := by
      gcongr <;> norm_num
    have h3 : (2 : ℝ) ^ (Ps.map (Piece.expR ds)).sum * errL P.u ds P.R₀ r n P.j ≤
        2 ^ (P.expR ds + (Ps.map (Piece.expR ds)).sum) * errL P.u ds P.R₀ r n P.j := by
      gcongr <;> norm_num
    linarith

/-- **Guard bits for a round.** If every piece error is at most `2^K` and
`2^(K + 1) · |Ps| ≤ 2^g`, the error term of `topR_err` is at most one, so every output entry of
the rounded round is within `√2 + 1` of the normalized butterflies. -/
theorem topR_err_guard (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (a : ℕ)
    {R : ℕ} (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂)
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup) (g s K : ℕ)
    (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.expR ds)).sum + g)
    (hK : ∀ P ∈ Ps, errL P.u ds P.R₀ r n P.j ≤ 2 ^ K) (hg : 2 ^ (K + 1) * Ps.length ≤ 2 ^ g)
    (Z : ZArr (Fin R × Fin r) (n + a)) (p : (Fin R × Fin r) × (Fin (n + a) → ZMod 2)) :
    ‖GaussianInt.toComplex (topR ds a low top hR₂ Ps g s Z p) -
      Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p‖ ≤ √2 + 1 := by
  refine (topR_err ds hd a low top hR₂ Ps hinj hcover hsel g s hs Z p).trans ?_
  set E := (Ps.map (Piece.expR ds)).sum
  have hsum : (Ps.map fun P => errL P.u ds P.R₀ r n P.j).sum ≤ Ps.length * 2 ^ K := by
    have := List.sum_le_length_nsmul (Ps.map fun P => errL P.u ds P.R₀ r n P.j) (2 ^ K)
      (fun x hx => by obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hx; exact hK Q hQ)
    simpa using this
  have hpe := piecesErr_le ds r Ps
  have hs' : (2 : ℝ) ^ (E + g) ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) (by omega)
  have hg' : (2 : ℝ) ^ (K + 1) * Ps.length ≤ 2 ^ g := by exact_mod_cast hg
  have hsq : √2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < 2 ^ s := by positivity
  have hP0 := piecesErr_nonneg ds r Ps
  suffices h : √2 * piecesErr ds r Ps ≤ 2 ^ s by
    have := (div_le_one hpos).2 h
    rw [mul_div_assoc] at this ⊢
    linarith
  calc √2 * piecesErr ds r Ps ≤ 2 * (2 ^ E * (Ps.length * 2 ^ K)) := by
        have hE : (0 : ℝ) ≤ 2 ^ E := by positivity
        have := mul_le_mul_of_nonneg_left hsum hE
        nlinarith
    _ = 2 ^ E * (2 ^ (K + 1) * Ps.length) := by rw [pow_succ]; ring
    _ ≤ 2 ^ E * 2 ^ g := by gcongr
    _ = 2 ^ (E + g) := (pow_add _ _ _).symm
    _ ≤ 2 ^ s := hs'

/-! ### The size of the entries -/

/-- Every entry of the rounded layer is at most `2^scaleR j ‖f‖₂ + errL j`. -/
theorem layerR_entry_le (u : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (R₀ j : ℕ) (e : Fin (bits u j) → Fin n) (he : Function.Injective e)
    (f : ZArr (Fin (rowsAt R₀ j) × Fin r) n) (q : (Fin (rowsAt R₀ j) × Fin r) × (Fin n → ZMod 2)) :
    ‖GaussianInt.toComplex (layerR u ds R₀ j e f q)‖ ≤
      2 ^ scaleR u ds j * l2 (toC f) + errL u ds R₀ r n j := by
  have h := layerR_err u ds hd R₀ j e he f
  have hP : l2 (((List.finRange (bits u j)).map fun i => kBit 1 (e i)).prod (toC f)) =
      l2 (toC f) := by
    have := l2_prod_kBit ((List.finRange (bits u j)).map e) (toC f)
    rw [List.map_map] at this
    exact this
  generalize layerR u ds R₀ j e f = Y at h ⊢
  generalize ((List.finRange (bits u j)).map fun i => kBit 1 (e i)).prod (toC f) = P at h hP
  have h2 := norm_le_l2 (toC Y) q
  have h3 : l2 (toC Y) ≤ l2 (toC Y - (2 : ℂ) ^ scaleR u ds j • P) + 2 ^ scaleR u ds j * l2 (toC f) := by
    have := l2_add_le (toC Y - (2 : ℂ) ^ scaleR u ds j • P) ((2 : ℂ) ^ scaleR u ds j • P)
    rw [sub_add_cancel, l2_smul, hP, norm_pow, RCLike.norm_two] at this
    exact this
  change ‖toC Y q‖ ≤ _
  linarith

end IntegerMultBounds.MathlibTM2.Layer
