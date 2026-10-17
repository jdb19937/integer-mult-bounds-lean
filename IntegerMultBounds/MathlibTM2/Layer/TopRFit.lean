module

import IntegerMultBounds.MathlibTM2.Layer.LayerRFit
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcR
public import IntegerMultBounds.MathlibTM2.Layer.LayerRBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

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

/-! ### The size of the input of the pieces -/

section Input

variable {R : ℕ}

lemma l2_le_of_injOn {X X' : Type} [Fintype X] [Fintype X'] (F : X → ℂ) (G : X' → ℂ) (ι : X → X')
    (hι : ∀ x y, F x ≠ 0 → F y ≠ 0 → ι x = ι y → x = y) (hF : ∀ x, F x ≠ 0 → F x = G (ι x)) :
    l2 F ≤ l2 G := by
  classical
  unfold l2
  apply Real.sqrt_le_sqrt
  set T := Finset.univ.filter fun x => F x ≠ 0
  have h1 : ∑ x, ‖F x‖ ^ 2 = ∑ x ∈ T, ‖G (ι x)‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => F x ≠ 0)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬F x ≠ 0), ‖F x‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun x hx => by
        simp only [Finset.mem_filter, not_not] at hx; simp [hx.2]
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun x hx => by
      rw [hF x (Finset.mem_filter.1 hx).2]
  rw [h1, ← Finset.sum_image (f := fun y => ‖G y‖ ^ 2) (fun x hx y hy h =>
    hι x y (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hy).2 h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity

lemma l2_padRows_le (hR : 0 < R) (R₂ : ℕ) (X : ZArr (Fin R × Fin r) n) :
    l2 (toC (padRows R₂ X)) ≤ l2 (toC X) := by
  refine l2_le_of_injOn _ _ (fun p => ((⟨p.1.1 % R, Nat.mod_lt _ hR⟩, p.1.2), p.2))
    (fun x y hx hy h => ?_) (fun x hx => ?_)
  · have hx' : (x.1.1 : ℕ) < R := by
      by_contra hc; apply hx; simp [toC, padRows, hc]
    have hy' : (y.1.1 : ℕ) < R := by
      by_contra hc; apply hy; simp [toC, padRows, hc]
    simp only [Prod.mk.injEq, Fin.mk.injEq, Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at h
    exact Prod.ext (Prod.ext (Fin.ext h.1.1) h.1.2) h.2
  · have hx' : (x.1.1 : ℕ) < R := by
      by_contra hc; apply hx; simp [toC, padRows, hc]
    simp [toC, padRows, hx', Nat.mod_eq_of_lt hx']

lemma l2_toRows_le (a : ℕ) (Y : ZArr (Fin R × Fin r) (n + a)) :
    l2 (toC (toRows a Y)) ≤ l2 (toC Y) := by
  have hbij : Function.Bijective (ofRowsIdx (R := R) (r := r) (n := n) a) := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨ofRowsIdx_injective a, ?_⟩
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, ZMod.card]
    ring
  have hinj : Function.Injective (toRowsIdx (R := R) (r := r) (n := n) a) := by
    intro x y h
    obtain ⟨p, rfl⟩ := hbij.2 x
    obtain ⟨q, rfl⟩ := hbij.2 y
    rw [toRowsIdx_ofRowsIdx, toRowsIdx_ofRowsIdx] at h
    rw [h]
  have : toC (toRows a Y) = toC Y ∘ toRowsIdx a := rfl
  rw [this]
  exact l2_le_of_injective _ _ hinj

lemma l2_k2s (l : List (Fin n)) (f : ZArr (Fin R × Fin r) n) :
    l2 (toC (k2s l f)) = 2 ^ l.length * l2 (toC f) := by
  rw [toC_k2s, l2_smul, prod_reverse_kBit, l2_prod_kBit, norm_pow, RCLike.norm_two]

lemma l2_sZ (l : List (Fin n)) (Z : ZArr (Fin R × Fin r) n) : l2 (toC (sZ l Z)) = l2 (toC Z) := by
  rw [toC_sZ, l2_Sl]

lemma l2_two_pow_smul (g : ℕ) (Z : ZArr (Fin R × Fin r) n) :
    l2 (toC ((2 ^ g : GaussianInt) • Z)) = 2 ^ g * l2 (toC Z) := by
  have : toC ((2 ^ g : GaussianInt) • Z) = (2 : ℂ) ^ g • toC Z := by
    funext q; simp [toC, toComplex_two]
  rw [this, l2_smul, norm_pow, RCLike.norm_two]

end Input

/-! ### The fits of a round from the parameters -/

section Round

lemma two_pow_le_two_pow {x y : ℕ} (h : x ≤ y) : (2 : ℝ) ^ x ≤ 2 ^ y :=
  pow_le_pow_right₀ (by norm_num) h

lemma sqrt_two_pow_le (x : ℕ) : √((2 : ℝ) ^ x) ≤ 2 ^ x := by
  rw [Real.sqrt_le_left (by positivity)]
  have : (1 : ℝ) ≤ 2 ^ x := one_le_pow₀ (by norm_num)
  nlinarith

lemma rowsAt_mono (R₀ : ℕ) {i j : ℕ} (h : i ≤ j) : rowsAt R₀ i ≤ rowsAt R₀ j := by
  rw [rowsAt_eq, rowsAt_eq]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.pos_of_neZero NW) h)

/-- **The fits of a rounded round.** For a one-row round on `n + a` address bits with `r = 2^l`
coefficients, entries of norm at most `2^p`, at most `D + 1` pieces of level at most `D` with
child scales at most `S`, the guard `g ≥ K + D + 6` for `K = Lb + D (cGain + 1)`,
`Lb = n + a + l + 2`, and the width `w' ≥ S + cGain D + s + p + Lb + 5`: the tape pieces are the
rounded pieces on the padded input, and the array before the shifts fits `w'` signed bits. -/
theorem topR_fits (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (a l : ℕ)
    (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : 1 * 2 ^ a ≤ R₂)
    (hR₂' : R₂ ≤ 2 * (1 * 2 ^ a)) (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup) (g s w' p D S : ℕ)
    (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.expR ds)).sum + g)
    (Z : ZArr (Fin 1 × Fin (2 ^ l)) (n + a)) (hZ : ∀ z, ‖GaussianInt.toComplex (Z z)‖ ≤ 2 ^ p)
    (hj : ∀ P ∈ Ps, P.j ≤ D) (hlen : Ps.length ≤ D + 1)
    (hS : ∀ P ∈ Ps, ∀ i < P.j, scaleR P.u ds i ≤ S)
    (hg : (n + a + l + 2) + D * (cGain ds + 1) + D + 6 ≤ g)
    (hw : S + cGain ds * D + s + p + (n + a + l + 2) + 5 ≤ w') :
    piecesRW w' ds Ps (padRows R₂ (toRows a
        (k2s top ((2 ^ g : GaussianInt) • sZ (LayerMachine.topSel a low top) Z)))) =
      piecesR ds Ps (padRows R₂ (toRows a
        (k2s top ((2 ^ g : GaussianInt) • sZ (LayerMachine.topSel a low top) Z)))) ∧
    ∀ z, Node.TopFitsZ w' (LayerMachine.topPreRW ds w' a low top hR₂ Ps g Z z) := by
  set Lb := n + a + l + 2 with hLb
  set K := Lb + D * (cGain ds + 1) with hK
  set E := (Ps.map (Piece.expR ds)).sum with hE
  set q := top.length with hq
  have hw1 : 1 ≤ w' := by omega
  -- the level errors
  have hK' : ∀ P ∈ Ps, ∀ i ≤ P.j, errL P.u ds P.R₀ (2 ^ l) n i ≤ 2 ^ K := by
    intro P hP i hi
    refine errL_le_K P.u ds P.R₀ (2 ^ l) n i Lb D (hi.trans (hj P hP)) ?_
    have h1 : rowsAt P.R₀ i ≤ R₂ := by
      have := rowsAt_mono P.R₀ hi; rw [← P.hR] at this; exact this
    have h2 : 2 * (rowsAt P.R₀ i * 2 ^ l * 2 ^ n) ≤ 2 * (2 * 2 ^ a * 2 ^ l * 2 ^ n) := by
      have : rowsAt P.R₀ i ≤ 2 * 2 ^ a := by omega
      gcongr
    refine h2.trans (le_of_eq ?_)
    rw [hLb]; ring
  -- the input of the pieces
  have hZ2 : l2 (toC Z) ≤ 2 ^ (p + Lb) := by
    have h := l2_le_of_norm_le (by positivity) (toC Z) (fun z => hZ z)
    have hc : (Fintype.card ((Fin 1 × Fin (2 ^ l)) × (Fin (n + a) → ZMod 2)) : ℝ) = 2 ^ (l + (n + a)) := by
      simp [pow_add]
    rw [hc] at h
    refine h.trans ?_
    have := sqrt_two_pow_le (l + (n + a))
    calc √((2 : ℝ) ^ (l + (n + a))) * 2 ^ p ≤ 2 ^ (l + (n + a)) * 2 ^ p := by gcongr
      _ ≤ 2 ^ (p + Lb) := by rw [← pow_add]; exact two_pow_le_two_pow (by omega)
  set W0 := padRows R₂ (toRows a (k2s top ((2 ^ g : GaussianInt) • sZ (LayerMachine.topSel a low top) Z)))
  have hW0 : l2 (toC W0) ≤ 2 ^ (g + q + p + Lb) := by
    refine (l2_padRows_le (R := 1 * 2 ^ a) (by positivity) R₂ _).trans
      ((l2_toRows_le (R := 1) a _).trans ?_)
    rw [l2_k2s, l2_two_pow_smul, l2_sZ]
    calc (2 : ℝ) ^ top.length * (2 ^ g * l2 (toC Z)) ≤ 2 ^ q * (2 ^ g * 2 ^ (p + Lb)) := by gcongr
      _ = 2 ^ (g + q + p + Lb) := by rw [← pow_add, ← pow_add]; congr 1; omega
  -- the bound on every piece input
  set B : ℝ := 2 ^ E * (2 ^ (g + q + p + Lb) + (D + 1) * 2 ^ K)
  have hDK : ((D : ℝ) + 1) * 2 ^ K ≤ 2 ^ (g + q + p + Lb) := by
    have h1 : ((D : ℝ) + 1) ≤ 2 ^ D := by
      have := Nat.lt_two_pow_self (n := D); exact_mod_cast this
    calc ((D : ℝ) + 1) * 2 ^ K ≤ 2 ^ D * 2 ^ K := by gcongr
      _ ≤ 2 ^ (g + q + p + Lb) := by rw [← pow_add]; exact two_pow_le_two_pow (by omega)
  have hB : B ≤ 2 ^ (E + g + q + p + Lb + 1) := by
    calc B ≤ 2 ^ E * (2 * 2 ^ (g + q + p + Lb)) := by
          simp only [B]; gcongr; linarith
      _ = 2 ^ (E + g + q + p + Lb + 1) := by
          rw [← pow_succ', ← pow_add]; congr 1; omega
  have hEs : E + g + q ≤ s := by omega
  have hpieces := piecesRW_eq_of_le w' ds hd hw1 (lipProd_le_two_pow ds) B Ps hinj hK' hS
    (fun P hP => by
      have hjD := hj P hP
      have h1 : (P.j : ℝ) * 2 ^ K ≤ 2 ^ (E + g + q + p + Lb + 1) := by
        have : (P.j : ℝ) * 2 ^ K ≤ ((D : ℝ) + 1) * 2 ^ K := by
          gcongr; have : (P.j : ℝ) ≤ D := by exact_mod_cast hjD
          linarith
        refine this.trans (hDK.trans ?_)
        exact two_pow_le_two_pow (by omega)
      have h2 : B + P.j * 2 ^ K ≤ 2 ^ (E + g + q + p + Lb + 2) := by
        rw [pow_succ]; linarith
      have h3 : (2 : ℝ) ^ (S + cGain ds * P.j) ≤ 2 ^ (S + cGain ds * D) :=
        two_pow_le_two_pow (by have := Nat.mul_le_mul_left (cGain ds) hjD; omega)
      have hB0 : 0 ≤ B := by positivity
      have h4 : (2 : ℝ) ^ (S + cGain ds * P.j) * (B + P.j * 2 ^ K) ≤
          2 ^ (S + cGain ds * D + (E + g + q + p + Lb + 2)) := by
        calc (2 : ℝ) ^ (S + cGain ds * P.j) * (B + P.j * 2 ^ K)
            ≤ 2 ^ (S + cGain ds * D) * 2 ^ (E + g + q + p + Lb + 2) :=
              mul_le_mul h3 h2 (by positivity) (by positivity)
          _ = _ := (pow_add _ _ _).symm
      have h5 : (2 : ℝ) ^ (S + cGain ds * D + (E + g + q + p + Lb + 2)) ≤ 2 ^ (w' - 3) :=
        two_pow_le_two_pow (by omega)
      have h6 : (2 : ℝ) ^ K ≤ 2 ^ (w' - 3) := two_pow_le_two_pow (by omega)
      have h7 : (2 : ℝ) ^ (w' - 3) * 2 < 2 ^ (w' - 1) := by
        rw [← pow_succ]; exact pow_lt_pow_right₀ (by norm_num) (by omega)
      linarith)
    (l2 (toC W0)) W0 (l2_nonneg _) le_rfl (by
      simp only [B]
      gcongr
      · have : ((Ps.length : ℕ) : ℝ) ≤ D + 1 := by exact_mod_cast hlen
        exact this)
  refine ⟨hpieces, ?_⟩
  -- the array before the shifts
  refine topPreRW_fits ds hd w' w' a low top hR₂ Ps hinj hcover hsel g s hs Z hpieces ?_
  have hpe : piecesErr ds (2 ^ l) Ps ≤ 2 ^ (E + g) := by
    refine (piecesErr_le ds (2 ^ l) Ps).trans ?_
    have hsum : (Ps.map fun P => errL P.u ds P.R₀ (2 ^ l) n P.j).sum ≤ Ps.length * 2 ^ K := by
      have := List.sum_le_length_nsmul (Ps.map fun P => errL P.u ds P.R₀ (2 ^ l) n P.j) (2 ^ K)
        (fun x hx => by obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hx; exact hK' Q hQ Q.j le_rfl)
      simpa using this
    have h1 : ((Ps.length : ℕ) : ℝ) * 2 ^ K ≤ 2 ^ g := by
      have : ((Ps.length : ℕ) : ℝ) ≤ 2 ^ D := by
        have h := Nat.lt_two_pow_self (n := D)
        have : Ps.length ≤ 2 ^ D := by omega
        exact_mod_cast this
      calc ((Ps.length : ℕ) : ℝ) * 2 ^ K ≤ 2 ^ D * 2 ^ K := by gcongr
        _ ≤ 2 ^ g := by rw [← pow_add]; exact two_pow_le_two_pow (by omega)
    calc (2 : ℝ) ^ E * (Ps.map fun P => errL P.u ds P.R₀ (2 ^ l) n P.j).sum
        ≤ 2 ^ E * 2 ^ g := by gcongr; linarith
      _ = 2 ^ (E + g) := (pow_add _ _ _).symm
  have h1 : (2 : ℝ) ^ s * l2 (toC Z) ≤ 2 ^ (s + p + Lb) := by
    calc (2 : ℝ) ^ s * l2 (toC Z) ≤ 2 ^ s * 2 ^ (p + Lb) := by gcongr
      _ = 2 ^ (s + p + Lb) := by rw [← pow_add, add_assoc]
  have h2 : √2 * piecesErr ds (2 ^ l) Ps ≤ 2 * 2 ^ (s + p + Lb) := by
    have hs2 : √2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have : (2 : ℝ) ^ (E + g) ≤ 2 ^ (s + p + Lb) := two_pow_le_two_pow (by omega)
    have h0 := piecesErr_nonneg ds (2 ^ l) Ps
    nlinarith
  have h3 : (2 : ℝ) ^ (s + p + Lb) * 4 < 2 ^ (w' - 1) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have h4 : (0 : ℝ) ≤ 2 ^ (s + p + Lb) := by positivity
  linarith

/-- `topR_fits` for the array before the shifts, in the form used by `refine`. -/
theorem topR_fits_pre (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (a l : ℕ)
    (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : 1 * 2 ^ a ≤ R₂)
    (hR₂' : R₂ ≤ 2 * (1 * 2 ^ a)) (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup) (g s w' p D S : ℕ)
    (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.expR ds)).sum + g)
    (Z : ZArr (Fin 1 × Fin (2 ^ l)) (n + a)) (hZ : ∀ z, ‖GaussianInt.toComplex (Z z)‖ ≤ 2 ^ p)
    (hj : ∀ P ∈ Ps, P.j ≤ D) (hlen : Ps.length ≤ D + 1)
    (hS : ∀ P ∈ Ps, ∀ i < P.j, scaleR P.u ds i ≤ S)
    (hg : (n + a + l + 2) + D * (cGain ds + 1) + D + 6 ≤ g)
    (hw : S + cGain ds * D + s + p + (n + a + l + 2) + 5 ≤ w') (z) :
    Node.TopFitsZ w' (LayerMachine.topPreRW ds w' a low top hR₂ Ps g Z z) :=
  (topR_fits ds hd a l low top hR₂ hR₂' Ps hinj hcover hsel g s w' p D S hs Z hZ hj hlen hS hg hw).2 z

end Round

end IntegerMultBounds.MathlibTM2.Layer
