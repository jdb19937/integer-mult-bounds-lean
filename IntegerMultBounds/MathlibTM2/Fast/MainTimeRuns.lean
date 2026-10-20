module

public import IntegerMultBounds.MathlibTM2.Fast.MainProg
import IntegerMultBounds.MathlibTM2.Cost.CRTDirectEntry
import IntegerMultBounds.MathlibTM2.Cost.MatchBandB
public import IntegerMultBounds.MathlibTM2.Cost.CRTDirectFull
import IntegerMultBounds.MathlibTM2.Cost.MatchConv
import IntegerMultBounds.MathlibTM2.Cost.MatchChirp
import IntegerMultBounds.MathlibTM2.Cost.MatchResampA
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The three source-transform runs against `totDirectBound`

`mn_runs_le`: the step bound `mnRuns` of the three source-transform runs of the fast
multiplier (`srcDirectP` on both operands, `oppDirectP`, `Fast/MainProg`) is eventually at most a constant
times `totDirectCRT + totResamp + totConv + T M(p) + T p`.

* `mn_core_le`: one run of `srcCore` on base files whose first cleared registers hold at most
  `T w` symbols costs at most `C (totDirectCRT + totResamp + totConv + T M(p) + T p) + 2 cF + cO`:
  `Ã` and `B̃₀` by `mt_rsa_stage_le`, `mt_band_stage_le_linear`; the chirp kernel by `mt_ch_kernel_le`
  and the stored descriptions (`ldcBlocks`, at most `2 T` symbols each); the chirp products by
  `mt_ch_chirpMul_le`; the convolution box without its transforms by `mt_cv_box_le_conv`
  (`cvBoxCost … cF cO = cvBoxCost … 0 0 + 2 cF + cO`, `mn_cvBoxCost_split`), the ring header and
  `header` (`ring_header_length_le`); the scale by `mt_ch_scale_le`; the transfers and clears are
  linear in `T w`.
* `mn_clrA_cfg` (and `Cost.mt_band_clr_cfg` for `B̃₀`): in a file configured by a loader (`preCfgA`, `bandCfgB`), the
  registers the next first loader step clears hold at most `T w` symbols (from
  `mt_rsa_clr_load_le`, `mt_rsb_clear_le`, with `b^k r = o(T)`), so the base files `mnV₁`,
  `mnV₂`, `mnσ₁`, `mnσ₂` of the second and third runs meet the hypothesis of `mn_core_le`.
* `mn_srcP_le`, `mn_oppP_le`: `srcDirectPCost`, `oppDirectPCost` add the CRT layouts (`mt_crt_le_pre`), the
  conjugations (`mt_ch_conj_le`) and a transfer.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter IntegerMultBounds.MathlibTM2.Cost


attribute [local irreducible] mnT mnQ

noncomputable section

/-! ### Arithmetic helpers -/

/-- The sum of the terms against which the runs are matched. -/
def mnRunSum (n : ℕ) : ℝ :=
  totDirectCRT n + totResamp n + totConv n + (T n : ℝ) * totMp n + (T n : ℝ) * p n

lemma mn_runSum_parts {n : ℕ} (h : Big n) :
    0 ≤ totDirectCRT n ∧ 0 ≤ totResamp n ∧ 0 ≤ totConv n ∧ 0 ≤ (T n : ℝ) * totMp n ∧
      0 ≤ (T n : ℝ) * p n :=
  ⟨mt_directCRT_nonneg n, mt_resamp_nonneg n, tot_conv_nonneg h, mt_Tmp_nonneg n, mt_Tp_nonneg n⟩

/-- A bound `a ≤ c Y` by a part `Y` of a nonnegative sum `Σ` gives `a ≤ max c 0 · Σ`. -/
lemma mn_le_max_mul {a c Y Z : ℝ} (h : a ≤ c * Y) (hY : 0 ≤ Y) (hYZ : Y ≤ Z) :
    a ≤ max c 0 * Z := by
  have h1 : c * Y ≤ max c 0 * Y := mul_le_mul_of_nonneg_right (le_max_left _ _) hY
  have h2 : max c 0 * Y ≤ max c 0 * Z := mul_le_mul_of_nonneg_left hYZ (le_max_right _ _)
  linarith

/-- The transforms enter the convolution box additively. -/
lemma mn_cvBoxCost_split (p l w S M cF cO : ℕ) :
    cvBoxCost p l w S M cF cO = cvBoxCost p l w S M 0 0 + (2 * cF + cO) := by
  unfold cvBoxCost cvSynthCost
  ring

/-- The stored chirp descriptions: one block of `m + 1` symbols per entry `m`. -/
lemma mn_length_ldcBlocks {A : ℕ} (l : List ℕ) :
    (ldcBlocks (A := A) l).length = (l.map (· + 1)).sum := by
  induction l with
  | nil => simp [ldcBlocks]
  | cons m l ih =>
    simp only [ldcBlocks, List.flatMap_cons, List.length_append, List.length_replicate,
      List.length_singleton, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]

lemma mn_sum_ofFn_le {k : ℕ} (f : Fin k → ℕ) {c : ℕ} (hf : ∀ i, f i ≤ c) :
    ((List.ofFn f).map (· + 1)).sum ≤ k * (c + 1) := by
  rw [List.map_ofFn, List.sum_ofFn]
  calc ∑ i, (f i + 1) ≤ ∑ _i : Fin k, (c + 1) := Finset.sum_le_sum fun i _ => by
        have := hf i; omega
    _ = k * (c + 1) := by simp

/-- The stored descriptions of `t` and `s` hold at most `2 T` symbols each, eventually. -/
lemma mn_ldcBlocks_le :
    ∀ᶠ n in atTop, ∀ A : ℕ, (ldcBlocks (A := A) (List.ofFn (t n))).length ≤ 2 * T n ∧
      (ldcBlocks (A := A) (List.ofFn (s n))).length ≤ 2 * T n := by
  filter_upwards [eventually_big, mt_poly_r_le_T 1 1] with n h hT A
  have hdb := mt_d_le_b n
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hdr : d n * (r n + 1) ≤ 2 * T n := by
    have : d n * r n ≤ T n := by
      calc d n * r n ≤ 1 * b n ^ 1 * r n := by
            rw [pow_one, one_mul]; exact Nat.mul_le_mul_right _ hdb
        _ ≤ T n := hT
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [mn_length_ldcBlocks]
    exact (mn_sum_ofFn_le _ fun i => mt_t_le_r n i).trans hdr
  · rw [mn_length_ldcBlocks]
    exact (mn_sum_ofFn_le _ fun i => ((mt_s_lt_t h i).le.trans (mt_t_le_r n i))).trans hdr

/-- A linear term `a (X w) + c` with `X ≤ T`, `w ≤ cw p` is at most `(a cw + c) T p`. -/
lemma mn_lin_le {n X w cw a c : ℕ} (h : Big n) (hX : X ≤ T n) (hw : w ≤ cw * p n) :
    ((a * (X * w) + c : ℕ) : ℝ) ≤ ((a * cw + c : ℕ) : ℝ) * ((T n : ℝ) * p n) := by
  have := mt_ch_lin_le (L := X) (a := a) (c := 0) (e := c) h hX hw
  push_cast at this ⊢
  have e : (X : ℝ) * (a * w + 0) = a * (X * w) := by ring
  rw [e] at this
  linarith

/-! ### Configured files -/

/-- In a file configured for step `k` of `Ã`, the registers the first step of the next loader
clears hold at most `T w` symbols, eventually. -/
lemma mn_clrA_cfg (cw cW : ℕ) :
    ∀ᶠ n in atTop, ∀ {t₀ A : ℕ} (hd0 : 0 < d n) (w W : ℕ) (V : RsaV (RsaX t₀) A)
      (hd : Fin 5 → Fin t₀) (rest : List (Fin (A + 4))) (k : ℕ),
      11 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
      ∀ x ∈ preClrA hd, ((preCfgA V hd n w W hd0 rest k).get x).length ≤ T n * w := by
  filter_upwards [eventually_big, mt_poly_r_le_T (3600 * (2 + cw + cW) ^ 2) 2] with n h hT
  intro t₀ A hd0 w W V hd rest k hw11 hwc hWc x hx
  set Y := p n + 1 + w + W with hYdef
  have hp1 : 1 ≤ p n := by have := h.thirteen_le_p; omega
  obtain ⟨b1, b2, b3, b4, b5, b6, -, -, -, b10, b11⟩ :=
    mt_rsa_preDA h hd0 W k (Y := Y) (by omega) (by omega)
  have c2 := mt_rsa_clr_load_le V hd w (preDA n W hd0 k) (preRecsA n W hd0 (k + 1) ++ rest)
    b1 b2 b3 b4 b5 b6 (by omega : w ≤ Y) b10 b11 (by omega) Nat.one_le_two_pow
  have hmem := List.le_sum_of_mem (List.mem_map_of_mem
    (f := fun x => 2 * ((preLoadA V hd w (preDA n W hd0 k)
      (preRecsA n W hd0 (k + 1) ++ rest)).get x).length + 2) hx)
  have hY : Y ≤ (2 + cw + cW) * p n := by
    have e : (2 + cw + cW) * p n = p n + p n + cw * p n + cW * p n := by ring
    omega
  have hY2 : 100 * (r n * Y ^ 2) ≤ T n := by
    have h1 : Y ^ 2 ≤ ((2 + cw + cW) * p n) ^ 2 := Nat.pow_le_pow_left hY 2
    have e : ((2 + cw + cW) * p n) ^ 2 = 36 * (2 + cw + cW) ^ 2 * b n ^ 2 := by
      unfold p; ring
    calc 100 * (r n * Y ^ 2) ≤ 100 * (r n * (36 * (2 + cw + cW) ^ 2 * b n ^ 2)) := by
          rw [← e]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = 3600 * (2 + cw + cW) ^ 2 * b n ^ 2 * r n := by ring
      _ ≤ T n := hT
  have hT11 : 11 * T n ≤ T n * w := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hw11
  simp only [preCfgA]
  omega

/-! ### One run of the source transform -/

lemma mn_runSum_ge {n : ℕ} (h : Big n) :
    totResamp n + totDirectCRT n + (T n : ℝ) * p n ≤ mnRunSum n ∧
      (T n : ℝ) * totMp n ≤ mnRunSum n ∧ totConv n + (T n : ℝ) * totMp n ≤ mnRunSum n ∧
      (T n : ℝ) * p n ≤ mnRunSum n ∧ totDirectCRT n ≤ mnRunSum n ∧ totConv n ≤ mnRunSum n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mn_runSum_parts h
  unfold mnRunSum
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The small terms of one run: transfers and clears of the box, the stored descriptions, the
ring header. -/
lemma mn_core_small {n XW LT LS H cw w : ℕ} (h : Big n) (hXW : XW ≤ cw * (T n * p n))
    (hLT : LT ≤ 2 * T n) (hLS : LS ≤ 2 * T n) (hw : w ≤ cw * p n)
    (hH : H ≤ 2 * (p n + 2 ^ ℓ n + w)) :
    32 * XW + 32 + (6 * LT + 6) + (6 * LS + 6) + ldrHeaderCost (p n) (ℓ n) w + (2 * H + 2) ≤
      (60 * cw + 200) * (T n * p n) := by
  have hp1 : 1 ≤ p n := by have := h.thirteen_le_p; omega
  have hT1 : 1 ≤ T n := Nat.one_le_two_pow
  have hTp : T n ≤ T n * p n := Nat.le_mul_of_pos_right _ hp1
  have hpT : p n ≤ T n * p n := Nat.le_mul_of_pos_left _ hT1
  have hrT : 2 ^ ℓ n ≤ T n := mt_r_le_T h
  have hℓ := mt_ℓ_le_p h
  have hwT : w ≤ cw * (T n * p n) := hw.trans (Nat.mul_le_mul_left _ hpT)
  have e : (60 * cw + 200) * (T n * p n) = 60 * (cw * (T n * p n)) + 200 * (T n * p n) := by
    ring
  rw [e]
  unfold ldrHeaderCost
  omega

/-- **One run of `srcCore`** on base files whose first cleared registers hold at most `T w`
symbols: at most `C (totDirectCRT + totResamp + totConv + T M(p) + T p) + 2 cF + cO`. -/
lemma mn_core_le {K : ℕ} (cw cW : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n) (w W cF cO : ℕ)
      (V₀ : RsaV (RsaX 6) (prime + K)) (σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4)))
      (restA restB : List (Fin (prime + K + 4))),
      p n + 2 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
      (∀ x ∈ preClrA crtHd, (V₀.get x).length ≤ T n * w) →
      BandBase σ₀ w crtHd → (∀ r ∈ bandClrB crtHd, (σ₀ r).length ≤ T n * w) →
      (srcCoreCost mnM n w W cF cO hd0 V₀ σ₀ restA restB : ℝ) ≤
        C * mnRunSum n + ((2 * cF + cO : ℕ) : ℝ) := by
  obtain ⟨CA, hCA⟩ := mt_rsa_stage_le_linear mnT 6 K cw cW
  obtain ⟨CB, hCB⟩ := mt_band_stage_le_linear mnT 6 K cw cW
  obtain ⟨CK, hCK⟩ := mt_ch_kernel_le cw cW
  set c4 : ℝ := mtCM cw + 21 * cw + 28
  set c5 : ℝ := 6 * cw + 19
  set c6 : ℝ := mtCvC cw
  set c7 : ℝ := ((60 * cw + 200 : ℕ) : ℝ)
  refine ⟨max CA 0 + max CB 0 + max CK 0 + 2 * max c4 0 + max c5 0 + max c6 0 + max c7 0,
    by positivity, ?_⟩
  filter_upwards [eventually_big, hCA, hCB, hCK, mt_ch_chirpMul_le cw, mt_ch_scale_le cw,
    mt_cv_box_le_conv cw, mn_ldcBlocks_le] with n h hA hB hK hC hS hV hL
  intro hd0 w W cF cO V₀ σ₀ restA restB hpw hwc hWc hclrA hbB hclrB
  obtain ⟨g1, g2, g3, g4, -, -⟩ := mn_runSum_ge h
  obtain ⟨-, -, -, q4, q5⟩ := mn_runSum_parts h
  have q0 : 0 ≤ totResamp n + totDirectCRT n + (T n : ℝ) * p n := by
    obtain ⟨r1, r2, -, -, r5⟩ := mn_runSum_parts h; linarith
  have q3 : 0 ≤ totConv n + (T n : ℝ) * totMp n := by
    obtain ⟨-, -, r3, r4, -⟩ := mn_runSum_parts h; linarith
  have a1 := mn_le_max_mul (hA hd0 w W V₀ crtHd restA (by omega) hwc hWc hclrA) q0 g1
  have a2 := mn_le_max_mul (hB hd0 w W σ₀ crtHd restB (by omega) hwc hWc hbB
    (by have := IntegerMultBounds.Networks.Shared50ModularControl.prime_odd; omega) hclrB) q0 g1
  have a3 := mn_le_max_mul (hK w W (by omega) hwc hWc) q4 g2
  have a4 := mn_le_max_mul (hC w (by omega) hwc) q4 g2
  have a5 := mn_le_max_mul (hS w hwc) q5 g4
  have a6 := mn_le_max_mul (hV w hpw hwc) q3 g3
  obtain ⟨hLT, hLS⟩ := hL (prime + K)
  have hX : (∏ i, t n i) ≤ T n := (mt_prod_t h).le
  have hXW : (∏ i, t n i) * w ≤ cw * (T n * p n) := by
    calc (∏ i, t n i) * w ≤ T n * (cw * p n) := Nat.mul_le_mul hX hwc
      _ = cw * (T n * p n) := by ring
  have hH := IntegerMultBounds.Schoenhage.ring_header_length_le (p n) (2 ^ ℓ n) w
  have hsm := mn_core_small h hXW hLT hLS hwc hH
  have hsm' := (Nat.cast_le (α := ℝ)).2 hsm
  rw [Nat.cast_mul (60 * cw + 200), Nat.cast_mul (T n)] at hsm'
  have a7 := mn_le_max_mul (c := c7) hsm' q5 g4
  unfold srcCoreCost srcCostA srcCostK srcCostC srcCostV srcCostB
  rw [mn_cvBoxCost_split]
  simp only [mnM_hd]
  generalize (∏ i, t n i) * (cmulCost w + 21 * w + 8) + 20 = P1 at a4 ⊢
  generalize (∏ i, t n i) * (6 * w + 4 * gamma n + 14) + 4 = P2 at a5 ⊢
  generalize (∏ i, t n i) * w = XW at a7 ⊢
  push_cast at a1 a2 a3 a4 a5 a6 a7 ⊢
  calc _ ≤ max CA 0 * mnRunSum n + max CB 0 * mnRunSum n + max CK 0 * mnRunSum n +
        2 * (max c4 0 * mnRunSum n) + max c5 0 * mnRunSum n + max c6 0 * mnRunSum n +
        max c7 0 * mnRunSum n + (2 * (cF : ℝ) + cO) := by linarith
    _ = _ := by ring

/-- Match the actual direct CRT call at the source-stage dimensions. -/
lemma mn_direct_crt_le (Tm cw K : ℕ) :
    ∀ᶠ n in atTop, ∀ w : ℕ, w ≤ cw * p n → ∀ fwd : Bool,
      (srcDirectCrtCost (K := K) fwd Tm n w : ℝ) ≤
        mtCrtDirectEntryC Tm cw * totDirectCRT n := by
  filter_upwards [crtDirectSource_pipeline_le Tm cw K, eventually_big] with n h hb w hw fwd
  apply h (d n) w (srcAx n) (s n)
    (fun j => (crtMu (s n) (s_pairwise n) j : ZMod (s n j)).val) rfl
  · rw [← crtControl_fullWidth]
    exact mt_crt_pre_eq hb
  · exact fun j => (pre_log_t j).symm
  · exact fun j => (src_crt_hs hb j).2.le
  · intro j
    have : NeZero (s n j) := ⟨ne_of_gt (src_crt_hs hb j).1⟩
    exact (ZMod.val_lt _).le
  · exact hw

/-! ### The transforms -/

/-- **`srcDirectP` and `oppDirectP`** on base files whose first cleared registers hold at most `T w`
symbols: each at most `C (totDirectCRT + totResamp + totConv + T M(p) + T p) + 2 cF + cO`. -/
lemma mn_srcP_le {K : ℕ} (cw cW : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n) (w W cF cO : ℕ)
      (V₀ : RsaV (RsaX 6) (prime + K)) (σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4)))
      (restA restB : List (Fin (prime + K + 4))),
      p n + 2 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
      (∀ x ∈ preClrA crtHd, (V₀.get x).length ≤ T n * w) →
      BandBase σ₀ w crtHd → (∀ r ∈ bandClrB crtHd, (σ₀ r).length ≤ T n * w) →
      (srcDirectPCost mnM n w W cF cO hd0 V₀ σ₀ restA restB : ℝ) ≤
          C * mnRunSum n + ((2 * cF + cO : ℕ) : ℝ) ∧
        (oppDirectPCost mnM n w W cF cO hd0 V₀ σ₀ restA restB : ℝ) ≤
          C * mnRunSum n + ((2 * cF + cO : ℕ) : ℝ) := by
  obtain ⟨C0, hC0, hcore⟩ := mn_core_le (K := K) cw cW
  set c1 : ℝ := mtCrtDirectEntryC mnT cw
  set c2 : ℝ := ((4 * cw + 4 : ℕ) : ℝ)
  set c3 : ℝ := 5 * cw + 8
  set c4 : ℝ := ((2 * cw + 2 : ℕ) : ℝ)
  refine ⟨C0 + max c1 0 + max c2 0 + 2 * max c3 0 + 2 * max c4 0, by positivity, ?_⟩
  filter_upwards [eventually_big, hcore, mn_direct_crt_le mnT cw K, mt_ch_conj_le cw]
    with n h hco hcr hcj
  intro hd0 w W cF cO V₀ σ₀ restA restB hpw hwc hWc hclrA hbB hclrB
  obtain ⟨-, -, -, g4, g5, -⟩ := mn_runSum_ge h
  obtain ⟨q1, -, -, -, q5⟩ := mn_runSum_parts h
  have a0 := hco hd0 w W cF cO V₀ σ₀ restA restB hpw hwc hWc hclrA hbB hclrB
  have a1f := mn_le_max_mul (hcr w hwc true) q1 g5
  have a1i := mn_le_max_mul (hcr w hwc false) q1 g5
  have hX : (∏ i, t n i) ≤ T n := (mt_prod_t h).le
  have a2 := mn_le_max_mul (c := c2) (mn_lin_le (a := 4) (c := 4) h hX hwc) q5 g4
  have a3 := mn_le_max_mul (c := c3) (hcj w hwc) q5 g4
  have a4 := mn_le_max_mul (c := c4) (mn_lin_le (a := 2) (c := 2) h hX hwc) q5 g4
  refine ⟨?_, ?_⟩
  · unfold srcDirectPCost
    push_cast at a0 a1f a2 ⊢
    calc _ ≤ max c1 0 * mnRunSum n + max c2 0 * mnRunSum n +
          (C0 * mnRunSum n + (2 * (cF : ℝ) + cO)) := by linarith
      _ ≤ (C0 + max c1 0 + max c2 0 + 2 * max c3 0 + 2 * max c4 0) * mnRunSum n +
          (2 * (cF : ℝ) + cO) := by
        have : 0 ≤ (2 * max c3 0 + 2 * max c4 0) * mnRunSum n :=
          mul_nonneg (by positivity) (q5.trans g4)
        nlinarith
  · unfold oppDirectPCost srcConjCost
    push_cast at a0 a1i a3 a4 ⊢
    calc _ ≤ max c1 0 * mnRunSum n + 2 * (max c3 0 * mnRunSum n) +
          2 * (max c4 0 * mnRunSum n) + (C0 * mnRunSum n + (2 * (cF : ℝ) + cO)) := by
          linarith
      _ ≤ (C0 + max c1 0 + max c2 0 + 2 * max c3 0 + 2 * max c4 0) * mnRunSum n +
          (2 * (cF : ℝ) + cO) := by
        have : 0 ≤ max c2 0 * mnRunSum n := mul_nonneg (le_max_right _ _) (q5.trans g4)
        nlinarith

/-! ### The three runs -/

/-- **The three source-transform runs against `totDirectBound`**: eventually
`mnRuns ≤ C (totDirectCRT + totResamp + totConv + T M(p) + T p)`. -/
theorem mn_runs_le {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ)
    (Y : MnSyn K Lb w σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, (mnRuns D Y n : ℝ) ≤
      C * (IntegerMultBounds.MathlibTM2.Cost.totDirectCRT n + IntegerMultBounds.MathlibTM2.Cost.totResamp n + IntegerMultBounds.MathlibTM2.Cost.totConv n +
        (T n : ℝ) * IntegerMultBounds.MathlibTM2.Cost.totMp n + (T n : ℝ) * p n) := by
  obtain ⟨cw, cW, hratio⟩ := D.ratio
  obtain ⟨Cs, hCs⟩ := Y.cost
  obtain ⟨C1, hC1, hrun⟩ := mn_srcP_le (K := K) cw cW
  refine ⟨3 * C1 + 6 * max Cs 0, by positivity, ?_⟩
  filter_upwards [eventually_big, hratio, D.widths, D.clrA, D.clrB, hCs, hrun,
    mn_clrA_cfg cw cW, mt_band_clr_cfg cw cW, D.base] with n h hrt hwd hcA hcB hcs hr hcfgA hcfgB
    hbase
  obtain ⟨hwc, hWc⟩ := hrt
  obtain ⟨hgw, -, -⟩ := hwd
  change _ ≤ _ * mnRunSum n
  have hd0 : 0 < d n := h.one_le_d
  have hb := h.sixteen_le_b
  have hg : 4 ≤ Chirp.chirpGuard (d n) := by unfold Chirp.chirpGuard; omega
  have hpb : p n = 6 * b n := rfl
  have hpw : p n + 2 ≤ w n := by omega
  have h11 : 11 ≤ w n := by omega
  have h101 : 101 ≤ w n := by omega
  obtain ⟨-, -, -, -, -, g6⟩ := mn_runSum_ge h
  have hconv := tot_conv_nonneg h
  have hcs' := mn_le_max_mul hcs hconv g6
  have hS0 : 0 ≤ mnRunSum n := hconv.trans g6
  unfold mnRuns
  rw [dite_eq_left hd0]
  set RA := preRecsA (A := prime + K) n (D.Wt n) hd0 0 with hRA
  set RB := preRecsB (A := prime + K) n (D.Wt n) hd0 0 with hRB
  have hA3 : 3 ≤ prime + K := by have := IntegerMultBounds.Networks.Shared50ModularControl.prime_odd; omega
  have hb0 : BandBase (D.σ₀ n) (w n) crtHd := (hbase hd0).bBase
  have hb1 : BandBase (mnσ₁ D n hd0) (w n) crtHd := bandCfgB_base hb0 hA3 _
  have hb2 : BandBase (mnσ₂ D n hd0) (w n) crtHd := bandCfgB_base hb1 hA3 _
  have b1 := (hr hd0 (w n) (D.Wt n) (Y.cF n) (Y.cO n) (D.V₀ n) (D.σ₀ n) (RA ++ (RA ++ D.restA n))
    (RB ++ (RB ++ D.restB n)) hpw hwc hWc hcA hb0 hcB).1
  have b2 := (hr hd0 (w n) (D.Wt n) (Y.cF n) (Y.cO n) (mnV₁ D n hd0) (mnσ₁ D n hd0)
    (RA ++ D.restA n) (RB ++ D.restB n) hpw hwc hWc
    (hcfgA hd0 (w n) (D.Wt n) (D.V₀ n) crtHd (RA ++ (RA ++ D.restA n)) (d n - 1) h11 hwc hWc)
    hb1 (hcfgB hd0 (w n) (D.Wt n) (D.σ₀ n) crtHd (RB ++ (RB ++ D.restB n)) (d n - 1) h101 hwc
      hWc hb0 hA3)).1
  have b3 := (hr hd0 (w n) (D.Wt n) (Y.cF n) (Y.cO n) (mnV₂ D n hd0) (mnσ₂ D n hd0)
    (D.restA n) (D.restB n) hpw hwc hWc
    (hcfgA hd0 (w n) (D.Wt n) (mnV₁ D n hd0) crtHd (RA ++ D.restA n) (d n - 1) h11 hwc hWc)
    hb2 (hcfgB hd0 (w n) (D.Wt n) (mnσ₁ D n hd0) crtHd (RB ++ D.restB n) (d n - 1) h101 hwc
      hWc hb1 hA3)).2
  push_cast at b1 b2 b3 hcs' ⊢
  calc _ ≤ 3 * (C1 * mnRunSum n) + 6 * ((Y.cF n : ℝ) + Y.cO n) := by linarith
    _ ≤ 3 * (C1 * mnRunSum n) + 6 * (max Cs 0 * mnRunSum n) := by linarith
    _ = _ := by ring

end

end IntegerMultBounds.MathlibTM2.Fast.Main
