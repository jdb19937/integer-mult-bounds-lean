module

public import IntegerMultBounds.MathlibTM2.Layer.LayerRFit
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcR

/-!
# The tape pieces are the rounded pieces

`layerRW_eq_of_le`: the closed form of `layerRW_eq_layerR` with `lipProd ≤ 2^a`, every level
error at most `2^K` and every scale at most `S`: the tape layer is the rounded layer on inputs of
norm at most `B` once `2^(S + a j) (B + j 2^K) + 2^K < 2^(w-1)`.

`piecesRW_eq_of_le`: the pieces run by the tape agree with the rounded pieces on an input of norm
at most `B₀` when every piece fits with the bound `2^E (B₀ + |Ps| 2^K)` on its input, `E` the sum
of the scales of the pieces.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks ComplexFramedExecution
open IntegerMultBounds.MathlibTM2.LayerMachine (layerRW pieceRW piecesRW)

variable {r n : ℕ}

/-- The input bound at level `i` below a top level `j` with input bound `B`. -/
noncomputable def betaL (a K j : ℕ) (B : ℝ) (i : ℕ) : ℝ :=
  2 ^ (a * (j - i)) * (B + ((j - i : ℕ) : ℝ) * 2 ^ K)

lemma betaL_nonneg (a K j : ℕ) {B : ℝ} (hB : 0 ≤ B) (i : ℕ) : 0 ≤ betaL a K j B i :=
  mul_nonneg (pow_nonneg (by norm_num) _)
    (add_nonneg hB (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)))

lemma betaL_step (a K j : ℕ) (B : ℝ) {i : ℕ} (hi : i < j) :
    betaL a K j B i = 2 ^ a * betaL a K j B (i + 1) + 2 ^ (a * (j - i)) * 2 ^ K := by
  have hji : j - i = (j - (i + 1)) + 1 := by omega
  unfold betaL
  rw [hji]
  push_cast
  rw [mul_add a, pow_add, mul_one]
  ring

lemma betaL_le (a K j : ℕ) {B : ℝ} (hB : 0 ≤ B) (i : ℕ) :
    betaL a K j B i ≤ 2 ^ (a * j) * (B + j * 2 ^ K) := by
  unfold betaL
  have h1 : ((j - i : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.sub_le j i
  have h2 : (2 : ℝ) ^ (a * (j - i)) ≤ 2 ^ (a * j) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.sub_le j i))
  have h3 : B + ((j - i : ℕ) : ℝ) * 2 ^ K ≤ B + j * 2 ^ K := by
    have := mul_le_mul_of_nonneg_right h1 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) K)
    linarith
  exact mul_le_mul h2 h3 (add_nonneg hB (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)))
    (pow_nonneg (by norm_num) _)

/-- **The tape layer on small inputs, closed form.** -/
theorem layerRW_eq_of_le (w u : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (R₀ j : ℕ) (hw : 1 ≤ w) {a K S : ℕ} {B : ℝ} (hB : 0 ≤ B) (ha : lipProd (program ds) ≤ 2 ^ a)
    (hK : ∀ i ≤ j, errL u ds R₀ r n i ≤ 2 ^ K) (hS : ∀ i < j, scaleR u ds i ≤ S)
    (hfit : 2 ^ (S + a * j) * (B + j * 2 ^ K) + 2 ^ K < 2 ^ (w - 1))
    (e : Fin (bits u j) → Fin n) (he : Function.Injective e)
    (f : ZArr (Fin (rowsAt R₀ j) × Fin r) n) (hf : l2 (toC f) ≤ B) :
    layerRW w u ds R₀ j e f = layerR u ds R₀ j e f := by
  refine layerRW_eq_layerR w u ds hd R₀ hw (betaL a K j B) j (fun i hi => ?_) (fun i hi => ?_)
    e he f ?_
  · -- the step of the bounds
    have hE := hK (i + 1) (by omega)
    have h0 := betaL_nonneg a K j hB (i + 1)
    have h1 : lipProd (program ds) * betaL a K j B (i + 1) ≤ 2 ^ a * betaL a K j B (i + 1) :=
      mul_le_mul_of_nonneg_right ha h0
    have h2 : (2 : ℝ) ^ K ≤ 2 ^ (a * (j - i)) * 2 ^ K :=
      le_mul_of_one_le_left (pow_nonneg (by norm_num) _) (one_le_pow₀ (by norm_num))
    have h3 := betaL_step a K j B hi
    linarith
  · -- the fit of the child results
    have hE := hK i (by omega)
    have h1 := betaL_le a K j hB i
    have h2 : (2 : ℝ) ^ scaleR u ds i ≤ 2 ^ S := pow_le_pow_right₀ (by norm_num) (hS i hi)
    have h3 : (2 : ℝ) ^ scaleR u ds i * betaL a K j B i ≤ 2 ^ (S + a * j) * (B + j * 2 ^ K) := by
      rw [pow_add, mul_assoc]
      exact mul_le_mul h2 h1 (betaL_nonneg a K j hB i) (pow_nonneg (by norm_num) _)
    linarith
  · simpa [betaL] using hf

/-- One rounded piece multiplies the input norm by its scale and adds its error. -/
lemma l2_pieceR_le (u : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (R₀ j : ℕ)
    {R₂ : ℕ} (hR : R₂ = rowsAt R₀ j) (e : Fin (bits u j) → Fin n) (he : Function.Injective e)
    (W : ZArr (Fin R₂ × Fin r) n) :
    l2 (toC (pieceR u ds R₀ j hR e W)) ≤ 2 ^ scaleR u ds j * l2 (toC W) + errL u ds R₀ r n j := by
  have h := pieceR_err u ds hd R₀ j hR e he W
  have := l2_add_le (toC (pieceR u ds R₀ j hR e W) -
      (2 : ℂ) ^ scaleR u ds j • Cl _ ((List.finRange (bits u j)).map e) (toC W))
    ((2 : ℂ) ^ scaleR u ds j • Cl _ ((List.finRange (bits u j)).map e) (toC W))
  rw [sub_add_cancel, l2_smul, l2_Cl, norm_pow, RCLike.norm_two] at this
  linarith

/-- The tape piece is the rounded piece on small inputs. -/
lemma pieceRW_eq_of_le (w u : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (R₀ j : ℕ) {R₂ : ℕ} (hR : R₂ = rowsAt R₀ j) (hw : 1 ≤ w) {a K S : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (ha : lipProd (program ds) ≤ 2 ^ a)
    (hK : ∀ i ≤ j, errL u ds R₀ r n i ≤ 2 ^ K) (hS : ∀ i < j, scaleR u ds i ≤ S)
    (hfit : 2 ^ (S + a * j) * (B + j * 2 ^ K) + 2 ^ K < 2 ^ (w - 1))
    (e : Fin (bits u j) → Fin n) (he : Function.Injective e)
    (Y : ZArr (Fin R₂ × Fin r) n) (hY : l2 (toC Y) ≤ B) :
    pieceRW w u ds R₀ j hR e Y = pieceR u ds R₀ j hR e Y := by
  subst hR
  have := layerRW_eq_of_le w u ds hd R₀ j hw hB ha hK hS hfit e he Y hY
  funext p
  unfold pieceRW pieceR
  exact congrFun this _

/-- **The tape pieces are the rounded pieces on small inputs.** -/
theorem piecesRW_eq_of_le (w : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds)
    {R₂ : ℕ} (hw : 1 ≤ w) {a K S : ℕ} (ha : lipProd (program ds) ≤ 2 ^ a) (B : ℝ)
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hK : ∀ P ∈ Ps, ∀ i ≤ P.j, errL P.u ds P.R₀ r n i ≤ 2 ^ K)
    (hS : ∀ P ∈ Ps, ∀ i < P.j, scaleR P.u ds i ≤ S)
    (hfit : ∀ P ∈ Ps, 2 ^ (S + a * P.j) * (B + P.j * 2 ^ K) + 2 ^ K < 2 ^ (w - 1)) :
    ∀ (B₀ : ℝ) (W : ZArr (Fin R₂ × Fin r) n), 0 ≤ B₀ → l2 (toC W) ≤ B₀ →
      2 ^ (Ps.map (Piece.expR ds)).sum * (B₀ + Ps.length * 2 ^ K) ≤ B →
      piecesRW w ds Ps W = piecesR ds Ps W := by
  induction Ps with
  | nil => intro _ _ _ _ _; rfl
  | cons P Ps ih =>
    intro B₀ W hB₀ hW hB
    have hP := List.mem_cons_self (a := P) (l := Ps)
    have hE : (2 : ℝ) ^ (Ps.map (Piece.expR ds)).sum * 2 ^ P.expR ds =
        2 ^ ((P :: Ps).map (Piece.expR ds)).sum := by
      rw [← pow_add]; congr 1; simp [add_comm]
    have hlen : (((P :: Ps).length : ℕ) : ℝ) = Ps.length + 1 := by simp
    -- the input of the first piece is small
    have hWB : l2 (toC W) ≤ B := by
      have h1 : B₀ ≤ 2 ^ ((P :: Ps).map (Piece.expR ds)).sum * (B₀ + (P :: Ps).length * 2 ^ K) := by
        have : B₀ ≤ B₀ + (P :: Ps).length * 2 ^ K := by
          have : (0 : ℝ) ≤ (P :: Ps).length * 2 ^ K := by positivity
          linarith
        exact this.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num)))
      linarith
    have hB0 : 0 ≤ B := (l2_nonneg _).trans hWB
    have h1 : pieceRW w P.u ds P.R₀ P.j P.hR P.e W = pieceR P.u ds P.R₀ P.j P.hR P.e W :=
      pieceRW_eq_of_le w P.u ds hd P.R₀ P.j P.hR hw hB0 ha (hK P hP) (hS P hP) (hfit P hP)
        P.e (hinj P hP) W hWB
    simp only [piecesRW, piecesR]
    rw [h1]
    -- the next input
    set X := pieceR P.u ds P.R₀ P.j P.hR P.e W
    have hX : l2 (toC X) ≤ 2 ^ P.expR ds * B₀ + 2 ^ K := by
      have := l2_pieceR_le P.u ds hd P.R₀ P.j P.hR P.e (hinj P hP) W
      have h2 := hK P hP P.j le_rfl
      have h3 : (2 : ℝ) ^ scaleR P.u ds P.j * l2 (toC W) ≤ 2 ^ P.expR ds * B₀ :=
        mul_le_mul_of_nonneg_left hW (by positivity)
      linarith
    refine ih (fun Q hQ => hinj Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ => hK Q (List.mem_cons_of_mem _ hQ)) (fun Q hQ => hS Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ => hfit Q (List.mem_cons_of_mem _ hQ)) (2 ^ P.expR ds * B₀ + 2 ^ K) X
      (by positivity) hX ?_
    -- the bound for the remaining pieces
    have hK1 : (2 : ℝ) ^ K ≤ 2 ^ P.expR ds * 2 ^ K :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    have h4 : (2 : ℝ) ^ (Ps.map (Piece.expR ds)).sum *
        (2 ^ P.expR ds * B₀ + 2 ^ K + Ps.length * 2 ^ K) ≤
        2 ^ (Ps.map (Piece.expR ds)).sum * (2 ^ P.expR ds * (B₀ + (Ps.length + 1) * 2 ^ K)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : (0 : ℝ) ≤ 2 ^ P.expR ds * (Ps.length * 2 ^ K) := by positivity
      have h5 : (Ps.length : ℝ) * 2 ^ K ≤ 2 ^ P.expR ds * (Ps.length * 2 ^ K) :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      nlinarith
    calc (2 : ℝ) ^ (Ps.map (Piece.expR ds)).sum * (2 ^ P.expR ds * B₀ + 2 ^ K + Ps.length * 2 ^ K)
        ≤ 2 ^ (Ps.map (Piece.expR ds)).sum * (2 ^ P.expR ds * (B₀ + (Ps.length + 1) * 2 ^ K)) := h4
      _ = 2 ^ ((P :: Ps).map (Piece.expR ds)).sum * (B₀ + (P :: Ps).length * 2 ^ K) := by
          rw [← hE, hlen]; ring
      _ ≤ B := hB

/-! ### The array before the shifts -/

lemma l2_Sl {X : Type} [Fintype X] (l : List (Fin n)) (f : Arr X n) : l2 (Sl X l f) = l2 f :=
  l2_congr_norm _ _ fun q => norm_Sl_apply l f q

lemma norm_Hl_le {X : Type} [Fintype X] (l : List (Fin n)) (hl : l.Nodup) (f : Arr X n)
    (q : X × (Fin n → ZMod 2)) : ‖Hl X l f q‖ ≤ l2 f := by
  refine (norm_le_l2 _ q).trans ?_
  rw [Hl_eq l hl, l2_smul, l2_Sl, l2_Cl, l2_Sl, norm_pow]
  have h : ‖(1 - Complex.I) / 2‖ ≤ 1 := by
    rw [norm_div, RCLike.norm_two, div_le_one (by norm_num), Complex.norm_def,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.I_re, Complex.sub_im, Complex.one_im,
      Complex.I_im]
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  exact mul_le_of_le_one_left (l2_nonneg _) (pow_le_one₀ (norm_nonneg _) h)

open IntegerMultBounds.MathlibTM2.LayerMachine (topPreRW topSel)
open IntegerMultBounds.MathlibTM2.Node (TopFitsZ)

/-- **The array before the shifts fits.** When the tape pieces agree with the rounded pieces,
every entry of `topPreRW` fits `w'` signed bits once `2^s ‖Z‖₂ + √2 piecesErr < 2^(w'-1)`. -/
theorem topPreRW_fits {R : ℕ} (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (w w' a : ℕ)
    (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂)
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup) (g s : ℕ)
    (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.expR ds)).sum + g)
    (Z : ZArr (Fin R × Fin r) (n + a))
    (h : piecesRW w ds Ps (padRows R₂ (toRows a
        (k2s top ((2 ^ g : GaussianInt) • sZ (topSel a low top) Z)))) =
      piecesR ds Ps (padRows R₂ (toRows a
        (k2s top ((2 ^ g : GaussianInt) • sZ (topSel a low top) Z)))))
    (hb : 2 ^ s * l2 (toC Z) + √2 * piecesErr ds r Ps < 2 ^ (w' - 1)) :
    ∀ p, TopFitsZ w' (topPreRW ds w a low top hR₂ Ps g Z p) := by
  intro p
  have e : topPreRW ds w a low top hR₂ Ps g Z p = topPre ds a low top hR₂ Ps g Z p := by
    simp only [topPreRW, h]
    rfl
  rw [e]
  refine topFitsZ_of_norm_lt ?_
  have h1 := topPre_err ds hd a low top hR₂ Ps hinj hcover hsel g s hs Z p
  have h2 := norm_Hl_le _ hsel (toC Z) p
  have h3 : ‖(2 : ℂ) ^ s * Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p‖ ≤ 2 ^ s * l2 (toC Z) := by
    rw [norm_mul, norm_pow, RCLike.norm_two]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 := norm_sub_norm_le (GaussianInt.toComplex (topPre ds a low top hR₂ Ps g Z p))
    ((2 : ℂ) ^ s * Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p)
  linarith

end IntegerMultBounds.MathlibTM2.Layer
