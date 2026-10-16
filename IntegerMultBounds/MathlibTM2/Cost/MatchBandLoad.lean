module

public import IntegerMultBounds.MathlibTM2.Cost.MatchResampB
public import IntegerMultBounds.MathlibTM2.Fast.BandStage

/-!
# Cost matching: the loader of the banded `B̃₀`

`mt_band_cp_le`: the step bound `bandCpB` of the band loader (`Fast/BandStage.lean`) at every
step is at most `42 T w + 300 T + 42 + mtBandU`, with `mtBandU = O((Tm + 1) r p^5)` the
polynomial part. The register lengths that enter the loader's cost are computed on the loader's
frames (`band_scr_sum`, `band_costE_eq`, `band_load_*`); every other term is a polynomial in
`Q = mtRsbQ D w` and `t + 1` (`band_cost*_le`, `band_preCost_le`). `mt_band_clr_cfg`: the
registers a loader clears in a band file hold at most `T w` symbols eventually.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds
  IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


section Columns

open IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.BandList

variable {P K wd s : ℕ} [NeZero s] {aZ : ZMod s → ℤ → ℤ}

theorem sum_colC_of {B : ℕ} : ∀ l : List (List ℤ), (∀ c ∈ l, c.length = B) →
    (l.map (List.length ∘ colC)).sum = l.length * B
  | [], _ => by simp
  | c :: l, h => by
    have h1 := h c (by simp)
    have h2 := sum_colC_of l fun x hx => h x (by simp [hx])
    simp only [List.map_cons, List.sum_cons, Function.comp, List.length_cons] at h2 ⊢
    rw [h2, colC, List.length_map, h1]; ring

theorem band_lc_cols (hP : 2 ≤ P) :
    ((bandLc P K wd s aZ).map (List.length ∘ colC)).sum = s * (2 * wd + 1) := by
  rw [sum_colC_of _ fun c hc => ?_, length_bandLc hP]
  have hfac := factorRowsZ_run P K (2 * wd + 1) hP (foldZ s wd aZ) (foldZ_band P s wd aZ) s
  rw [bandLc, bandFac, hfac, List.map_map] at hc
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hc
  simp

theorem band_uc_cols :
    ((bandUc P K wd s aZ).map (List.length ∘ colC)).sum = s * (2 * wd + 1) := by
  rw [sum_colC_of _ fun c hc => ?_, length_bandUc]
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hc
  simp [ucolZ]

end Columns

section Frames

variable {t₀ K : ℕ}

/-- The scratch registers cleared in step 3 of the loader. -/
theorem band_scr_sum (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandScrL.map fun r => 2 * (bandFB2a (bandFB1 σ hd w D rest) D w r).length + 2).sum =
      2 * (σ (.inl .tb)).length + 2 * (D.t + D.m + D.α + D.p + D.W + D.α * D.α + D.bWd +
        D.bB + (2 * D.bB + 1)) + 20 := by
  simp [bandScrL, bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1,
    bandFA, bandF0, preBankB, Function.update_apply, bandClrB, preHB]
  omega

/-- The clearing and moves of step 5 of the loader. -/
theorem band_costE_eq (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest l : List (Fin (prime + K + 4))) :
    bandCostE (bandFP (bandFB2b (bandFB2a (bandFB1 σ hd w D rest) D w) D w) D w l) =
      2 * (D.s * D.bB) + 2 * (2 * D.bWd) + 2 * (2 * D.bWd) + 2 * w +
        2 * ((D.bB + 1) * (2 * D.bB + 1) * w) + 2 * ((2 * D.bB + 1) * w) + 2 * (2 * D.bWd * w) +
        2 * w + 16 + 1 + (2 * (2 * D.t + 2) + (2 * (2 * w + 2) + (2 * (2 * w + 2) +
        ((2 * ((D.s + 1) / 2 * w) + 2) + ((2 * (D.s / 2) + 2) +
        (2 * ((D.s + 1) / 2 - D.s / 2) + 2)))))) := by
  simp [bandCostE, bandClrE, bandFP, bandFB2b, bandScrL, bandFB2a, bandFB1, bandFF2, bandFF2a,
    bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0, preBankB, Function.update_apply,
    bandClrB, preHB, length_preMaskE]
  ring_nf

/-! ### The registers of a loaded file -/

theorem band_load_msk (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .msk)).length = (σ (.inl .ac2)).length + D.t := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB, length_preMaskE]

theorem band_load_bo (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .bo)).length = ((bandLc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)).map
      (List.length ∘ colC)).sum * w := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_hf (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .hf)).length = ((bandUc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)).map
      (List.length ∘ colC)).sum * w := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_df (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .df)).length = (bandRcs D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)).length * w := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_dtab (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .dtab)).length = D.s * w := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]
  exact Or.inl (length_rsbArr _)

theorem band_load_padc (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .padc)).length = (D.t - D.s) * w := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_sn (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .sn)).length = D.s := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_mwn (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .mwn)).length = (σ (.inl (.cm .wn))).length + 2 * D.bWd * w := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_m2wn (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .m2wn)).length = D.s / 2 := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_m2n (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .m2n)).length = D.bB := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_smwn (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .smwn)).length = w := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_tswn (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .tswn)).length = (D.s + 1) / 2 * w := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_kn (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .kn)).length = (D.s + 1) / 2 - D.s / 2 := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_ms (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .ms)).length = 0 := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_bx (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .bx)).length = w := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_pn (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl (.cm .pn))).length = D.bP := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_tb (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .tb)).length = 0 := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_ac2 (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl .ac2)).length = 0 := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_wn (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    (bandLoad σ hd w D rest (.inl (.cm .wn))).length = (σ (.inl (.cm .wn))).length := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB]

theorem band_load_hb (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) (k : Fin 5) :
    (bandLoad σ hd w D rest (preHB hd k)).length = (rsbBank (A := prime + K) hd (D.hs w)
      (reg (hd k))).length := by
  have hb : ∀ k, ∃ k', reg (hd k') = reg (hd k) := fun k => ⟨k, rfl⟩
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL,
    bandFB2a, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0,
    preBankB, bandClrB, preHB, hb]

end Frames

section Poly

variable {t₀ K : ℕ}

/-! ### The loader terms as polynomials -/

theorem band_mono {S T1 u q : ℕ} (hS : 1 ≤ S) (hT : 1 ≤ T1) (hu : 1 ≤ u) (hq : 1 ≤ q)
    {a b c k : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hk : k ≤ 5) :
    S ^ a * T1 ^ b * u ^ c * q ^ k ≤ S * T1 * u * q ^ 5 := by
  have h1 : S ^ a ≤ S := by simpa using Nat.pow_le_pow_right hS ha
  have h2 : T1 ^ b ≤ T1 := by simpa using Nat.pow_le_pow_right hT hb
  have h3 : u ^ c ≤ u := by simpa using Nat.pow_le_pow_right hu hc
  have h4 : q ^ k ≤ q ^ 5 := Nat.pow_le_pow_right hq hk
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4

theorem band_costF1_le (D : PreAxB) {T w q u S T1 : ℕ} (hm : D.m ≤ q) (_hα : D.α ≤ q)
    (hp : D.p ≤ q) (_hW : D.W ≤ q) (_hw : w ≤ q) (hs : D.s ≤ u) (_ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) (_hR : rmulCost T w ≤ 288 * S * T1 * q ^ 3) :
    bandCostF1 D ≤ 207 * (S * T1 * u * q ^ 5) := by
  simp only [bandCostF1, 
    
    
    PreAxB.bWd, PreAxB.bB]
  calc _ ≤ 4 * q + 4 + (4 * q + 4) + (4 * (8 * q) + 4) + 1 + (4 * (2 * (8 * q) + 1) + 4) + 1 + (4 * (2
          * (8 * q) + 1) + 4) + 1 + (4 * u + 4) := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

theorem band_costVM_le (D : PreAxB) {T w q u S T1 : ℕ} (hm : D.m ≤ q) (hα : D.α ≤ q)
    (hp : D.p ≤ q) (hW : D.W ≤ q) (hw : w ≤ q) (hs : D.s ≤ u) (ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) (_hR : rmulCost T w ≤ 288 * S * T1 * q ^ 3) :
    preVMCost 60 D.W w [D.bP, D.s, D.t, D.α, D.bWd, D.bB + 1 + D.s, 2 * D.bB + 1, D.bB]
      (bandKFold D) ((D.bB + 1 + D.s) * (2 * D.bB + 1) * w) ≤ 943711899 * (S * T1 * u * q ^ 5) := by
  simp only [
    
    preVMCost, bandKFold, tblC,
    PreAxB.bP, PreAxB.bWd, PreAxB.bB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc _ ≤ 4 * q + 4 + (4 * q + 4) + (60 * (4 * q + 4) + 1) + (5 * q * (4 * q + 10) + 6 * q + 10 + (u *
          (4 * q + 10) + 6 * q + 10 + (u * (4 * q + 10) + 6 * q + 10 + (q * (4 * q + 10) + 6 * q + 10
          + (8 * q * (4 * q + 10) + 6 * q + 10 + ((2 * (8 * q) + 1 + 1 + u) * (4 * q + 10) + 6 * q +
          10 + ((2 * (2 * (8 * q) + 1) + 1) * (4 * q + 10) + 6 * q + 10 + ((2 * (8 * q) + 1) * (4 * q
          + 10) + 6 * q + 10 + 0))))))) + 1) + ((1 + (150 * (5 * q) + 400) + 8 + (1 + (5 * q * (1 + 1
          + 2) + 2)) + (1 + ((2 * (8 * q) + 1 + 1 + u) * (11 + 2 + (1 + ((2 * (2 * (8 * q) + 1) + 1) *
          (310 * (5 * q) + 201 + 1 + 2) + 2)) + 1 + 2) + 2))) * (32 * (q + 4) ^ 2 + 8 * q) + 2 * ((2 *
          (8 * q) + 1 + 1 + u) * (2 * (2 * (8 * q) + 1) + 1) * q) + 2) + (60 * (2 * q + 2) + 2 * q + 2
          * q + 31) := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

theorem band_costF2_le (D : PreAxB) {T w q u S T1 : ℕ} (hm : D.m ≤ q) (hα : D.α ≤ q)
    (_hp : D.p ≤ q) (_hW : D.W ≤ q) (hw : w ≤ q) (hs : D.s ≤ u) (_ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) (_hR : rmulCost T w ≤ 288 * S * T1 * q ^ 3) :
    bandCostF2 D w ≤ 13635 * (S * T1 * u * q ^ 5) := by
  simp only [bandCostF2, bandCostF2a, bandCostF2b, bandCostF2c, bandCostF2d, 
    
    
    PreAxB.bWd, PreAxB.bB]
  calc _ ≤ 2 * (2 * (8 * q) + 1 + 1 + u) + 2 + (4 * (2 * (8 * q) + 1) + 4 + (4 * (2 * (8 * q) + 1) + 4
          + (4 * (8 * q) + 4))) + (2 * (8 * q) * (4 * q + 7) + 2 * (2 * (8 * q)) + 4 + (2 * (2 * (8 *
          q) + 1) * (4 * q + 7) + 2 * (2 * (2 * (8 * q) + 1)) + 4 + ((2 * (2 * (8 * q) + 1) + 1) * (4
          * q + 7) + 2 * (2 * (2 * (8 * q) + 1) + 1) + 4)) + (4 * (2 * (8 * q) + 1) + 4 + (1 + ((2 *
          (8 * q) + 1 + 1) * (4 * (2 * (2 * (8 * q) + 1) + 1) + 7) + 2 * (2 * (8 * q) + 1 + 1) + 4 +
          ((2 * (8 * q) + 1 + 1) * (2 * (2 * (8 * q) + 1) + 1) * (4 * q + 7) + 2 * ((2 * (8 * q) + 1 +
          1) * (2 * (2 * (8 * q) + 1) + 1)) + 4 + (2 * (2 * (8 * q) + 1 + 1) + 2 + (2 * ((2 * (8 * q)
          + 1 + 1) * (2 * (2 * (8 * q) + 1) + 1)) + 2))))) + (4 * q + 4 + (q * (4 * q + 7) + 2 * q + 4
          + (2 * q + 2 + (4 * (q * q) + 4 + (4 * q + 4))))))) := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

theorem band_costF3_le (D : PreAxB) {T w q u S T1 : ℕ} (hm : D.m ≤ q) (_hα : D.α ≤ q)
    (hp : D.p ≤ q) (hW : D.W ≤ q) (hw : w ≤ q) (_hs : D.s ≤ u) (_ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) (_hR : rmulCost T w ≤ 288 * S * T1 * q ^ 3) :
    bandCostF3 D w ≤ 24992 * (S * T1 * u * q ^ 5) := by
  simp only [bandCostF3,
    
    preVMCost, bandKH, tblC,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc _ ≤ 4 * q + 4 + (1 + (4 * 1 + 4 + (4 * q + 4 + (4 * q + 4) + (48 * (4 * q + 4) + 1) + ((5 * q) *
          (4 * q + 10) + 6 * q + 10 + 0 + 1) + ((3 + (4 * (5 * q) + 5 + 2)) * (32 * (q + 4) ^ 2 + 8 *
          q) + 2 * q + 2) + (48 * (2 * q + 2) + 2 * q + 2 * q + 31) + (2 * (5 * q) + 2 + (2 * 1 +
          2))))) := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

theorem band_costB2a_le (D : PreAxB) {T w q u S T1 : ℕ} (hm : D.m ≤ q) (hα : D.α ≤ q)
    (hp : D.p ≤ q) (hW : D.W ≤ q) (hw : w ≤ q) (hs : D.s ≤ u) (ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) (_hR : rmulCost T w ≤ 288 * S * T1 * q ^ 3) :
    bandCostB2a D w ≤ 69374 * (S * T1 * u * q ^ 5) := by
  simp only [
    bandCostB2a, 
    preVMCost, bandKH, preKM, tblC,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc _ ≤ 4 * u + 4 + (4 * u + 4 + ((u) * (4 * q + 7) + 2 * (u) + 4 + (2 * (u) + 2))) + (1 + (4 * q +
          4 + (4 * 1 + 4) + (48 * (4 * q + 4) + 1) + (u * (4 * q + 10) + 6 * q + 10 + (u * (4 * q +
          10) + 6 * q + 10 + 0) + 1) + ((7 + (1 + (u * (6 + 1 + 2) + 2))) * (32 * (q + 4) ^ 2 + 8 * 1)
          + 2 * u + 2) + (48 * (2 * q + 2) + 2 * q + 2 * 1 + 31) + (2 * u + 2 + (2 * u + 2 + (2 * 1 +
          2)))) + (4 * q + 4 + (4 * q + 4 + (4 * q + 4) + (48 * (4 * q + 4) + 1) + (9 * q * (4 * q +
          10) + 6 * q + 10 + 0 + 1) + ((3 + (4 * (9 * q) + 5 + 2)) * (32 * (q + 4) ^ 2 + 8 * q) + 2 *
          q + 2) + (48 * (2 * q + 2) + 2 * q + 2 * q + 31) + (2 * (9 * q) + 2)) + (4 * q + 4 + (1 + (4
          * (q * q) + 4 + (4 * q + 4 + (4 * q + 4) + (48 * (4 * q + 4) + 1) + ((q + 1) * (4 * q + 10)
          + 6 * q + 10 + 0 + 1) + ((3 + (4 * (q + 1) + 5 + 2)) * (32 * (q + 4) ^ 2 + 8 * q) + 2 * q +
          2) + (48 * (2 * q + 2) + 2 * q + 2 * q + 31) + (2 * (q + 1) + 2)))) + (4 * u + 4 + (1 + (4 *
          (u + 1) + 4 + ((u) * (4 * q + 7) + 2 * ((u)) + 4 + (4 * u + 4 + (4 * ((u)) + 4 + (2 * (1) +
          2 + (2 * (u + 1) + 2))))))))))) := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

theorem band_costB2b_le (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) {T w q u S T1 : ℕ} (_hm : D.m ≤ q) (hα : D.α ≤ q)
    (hp : D.p ≤ q) (hW : D.W ≤ q) (hw : w ≤ q) (hs : D.s ≤ u) (ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) (hR : rmulCost T w ≤ 288 * S * T1 * q ^ 3) :
    bandCostB2b T σ D w ≤ 885034 * (S * T1 * u * q ^ 5) + (List.map (fun r => 2 * (σ r).length + 2) bandScrL).sum := by
  simp only [
    bandCostB2b, 
    preVMCost, bandKH, preKD, tblC,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc _ ≤ 4 * q + 4 + (4 * q + 4) + (48 * (4 * q + 4) + 1) + (u * (4 * q + 10) + 6 * q + 10 + (u * (4
          * q + 10) + 6 * q + 10 + (q * (4 * q + 10) + 6 * q + 10 + (q * (4 * q + 10) + 6 * q + 10 +
          0))) + 1) + ((u * (310 * q + 123) + (160 * q + 450)) * (32 * (q + 4) ^ 2 + 8 * q) + 2 * (u *
          q) + 2) + (48 * (2 * q + 2) + 2 * q + 2 * q + 31) + (4 * q + 4 + (1 + (4 * q + 4 + (4 * q +
          4) + (48 * (4 * q + 4) + 1) + ((9 * q + 1) * (4 * q + 10) + 6 * q + 10 + 0 + 1) + ((3 + (4 *
          (9 * q + 1) + 5 + 2)) * (32 * (q + 4) ^ 2 + 8 * q) + 2 * q + 2) + (48 * (2 * q + 2) + 2 * q
          + 2 * q + 31) + (2 * (9 * q + 1) + 2))) + (u * ((288 * S * T1 * q ^ 3) + 6 * q + 8) + 6 + (2
          * (u * q) + 2) + ((List.map (fun r => 2 * (σ r).length + 2) bandScrL).sum + 1 + 2 * q + 2))) := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

theorem band_costPrep_le (D : PreAxB) {T w q u S T1 : ℕ} (hm : D.m ≤ q) (hα : D.α ≤ q)
    (_hp : D.p ≤ q) (_hW : D.W ≤ q) (hw : w ≤ q) (hs : D.s ≤ u) (_ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) (hR : rmulCost T w ≤ 288 * S * T1 * q ^ 3) :
    bandAxisPrepCost T w (2 * D.bWd) D.bK D.s ≤ 358262 * (S * T1 * u * q ^ 5) := by
  simp only [
    bandAxisPrepCost, bandFacStepCost, bandNewtonStepCost, bandFacRowCost,
    bandFwdStepCost, bandTStepCost, bandAxisOrgCost, 
    PreAxB.bWd, PreAxB.bK]
  calc _ ≤ 4 * ((2 * (8 * q) + 1 + 1) * (2 * (2 * (8 * q) + 1) + 1) * q) + 4 + (2 * ((2 * (8 * q) + 1 +
          1) * (2 * (2 * (8 * q) + 1) + 1) * q) + 2) + (u * (100 * (2 * (8 * q) + 1 + 1) * (2 * (8 *
          q) + 1 + 1) * q + 200 + (4 * (q * q) * (2 * (288 * S * T1 * q ^ 3) + 80 * q + 120 + 6) + 4)
          + ((2 * (8 * q) + 1) * ((288 * S * T1 * q ^ 3) + 30 * q + 40 + (2 * (2 * (8 * q) + 1) *
          ((288 * S * T1 * q ^ 3) + 40 * q + 60) + 30 * q + 60) + 4 * (2 * (2 * (8 * q) + 1) * q) + 4
          * q + 8 + 6) + 4) + 6) + 4) + (2 * ((2 * (8 * q) + 1 + 1) * (2 * (2 * (8 * q) + 1) + 1) * q)
          + 2) + (200 * (u + 2 * (8 * q) + 2) * (2 * (8 * q) + 2) * q + 2 * (4 * (q * q)) + 200 + (u *
          (40 * (2 * (8 * q) + 2) * (2 * (8 * q) + 2) * q + 40 * (2 * (8 * q)) + 100 + 6) + 4 + (2 *
          ((2 * (8 * q) + 1) * (2 * (8 * q) + 1) * q) + 2) + (2 * (u * (2 * (8 * q) + 1) * q) + 2) +
          (2 * (u * (2 * (8 * q) + 1) * q) + 2))) := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

theorem band_polyE_le (D : PreAxB) {w q u S T1 : ℕ} (hm : D.m ≤ q) (_hα : D.α ≤ q)
    (_hp : D.p ≤ q) (_hW : D.W ≤ q) (hw : w ≤ q) (hs : D.s ≤ u) (ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) :
    2 * (D.s * D.bB) + 2 * (2 * D.bWd) + 2 * (2 * D.bWd) + 2 * w + 2 * ((D.bB + 1) * (2 * D.bB +
    1) * w) + 2 * ((2 * D.bB + 1) * w) + 2 * (2 * D.bWd * w) + 2 * w + 16 + 1 + (2 * (2 * D.t +
    2) + (2 * (2 * w + 2) + (2 * (2 * w + 2) + ((2 * ((D.s + 1) / 2 * w) + 2) + ((2 * (D.s / 2)
    + 2) + (2 * ((D.s + 1) / 2 - D.s / 2) + 2)))))) ≤ 1517 * (S * T1 * u * q ^ 5) := by
  simp only [PreAxB.bB, PreAxB.bWd]
  calc _ ≤ 2 * (u * (2 * (8 * q) + 1)) + 2 * (2 * (8 * q)) + 2 * (2 * (8 * q)) + 2 * q + 2 * (((2 * (8
          * q) + 1) + 1) * (2 * (2 * (8 * q) + 1) + 1) * q) + 2 * ((2 * (2 * (8 * q) + 1) + 1) * q) +
          2 * (2 * (8 * q) * q) + 2 * q + 16 + 1 + (2 * (2 * u + 2) + (2 * (2 * q + 2) + (2 * (2 * q +
          2) + ((2 * ((u) * q) + 2) + ((2 * ((u)) + 2) + (2 * (1) + 2)))))) := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

theorem band_polyScr_le (D : PreAxB) {w q u S T1 : ℕ} (hm : D.m ≤ q) (hα : D.α ≤ q)
    (hp : D.p ≤ q) (hW : D.W ≤ q) (_hw : w ≤ q) (_hs : D.s ≤ u) (ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) :
    2 * (D.t + D.m + D.α + D.p + D.W + D.α * D.α + D.bWd + D.bB + (2 * D.bB + 1)) + 20 ≤ 152 * (S * T1 * u * q ^ 5) := by
  simp only [PreAxB.bB, PreAxB.bWd]
  calc _ ≤ 2 * (u + q + q + q + q + q * q + (8 * q) + (2 * (8 * q) + 1) + (2 * (2 * (8 * q) + 1) + 1))
          + 20 := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

/-- **The loader of one axis** as a polynomial: the cleared registers of the previous file,
the scratch register `tb`, `100 (P + G)` for the record fields and headers, and
`10^9 S (T + 1) (t + 1) Q^5` for everything else. -/
theorem band_preCost_le (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) {T q u S T1 : ℕ}
    (hm : D.m ≤ q) (hα : D.α ≤ q) (hp : D.p ≤ q) (hW : D.W ≤ q) (hw : w ≤ q) (hL : D.L ≤ q)
    (hLd : D.Ld ≤ q) (hs : D.s ≤ u) (ht : D.t ≤ u) (hq : 1 ≤ q) (hu : 1 ≤ u) (hS : 1 ≤ S)
    (hT : 1 ≤ T1) (hR : rmulCost T w ≤ 288 * S * T1 * q ^ 3) :
    bandPreCost T σ hd w D rest ≤ ((bandClrB hd).map fun r => 2 * (σ r).length + 2).sum +
      2 * (σ (.inl .tb)).length + 100 * (D.P + D.G) + 10 ^ 9 * (S * T1 * u * q ^ 5) := by
  have hY1 : u + q ≤ 2 * (S * T1 * u * q ^ 5) := by
    have h1 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have h2 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    simp only [pow_zero, pow_one, one_mul, mul_one] at h1 h2
    omega
  have hA : bandCostA σ hd w D ≤ ((bandClrB hd).map fun r => 2 * (σ r).length + 2).sum +
      21 * (D.P + D.G) + 200 * (u + q) := by
    simp only [bandCostA, preHdrCostB, PreAxB.fields, List.sum_cons, List.sum_nil]
    omega
  have hF1 := band_costF1_le D hm hα hp hW hw hs ht hq hu hS hT hR
  have hVM := band_costVM_le D hm hα hp hW hw hs ht hq hu hS hT hR
  have hF2 := band_costF2_le D hm hα hp hW hw hs ht hq hu hS hT hR
  have hF3 := band_costF3_le D hm hα hp hW hw hs ht hq hu hS hT hR
  have hB2a := band_costB2a_le D hm hα hp hW hw hs ht hq hu hS hT hR
  have hB2b := band_costB2b_le (bandFB2a (bandFB1 σ hd w D rest) D w) D hm hα hp hW hw hs ht hq hu
    hS hT hR
  have hPrep := band_costPrep_le D hm hα hp hW hw hs ht hq hu hS hT hR
  have hE := band_polyE_le D hm hα hp hW hw hs ht hq hu hS hT
  have hScr := band_polyScr_le D (w := w) hm hα hp hW hw hs ht hq hu hS hT
  rw [band_scr_sum] at hB2b
  unfold bandPreCost bandCostB1
  rw [band_costE_eq]
  omega
theorem band_polyClr_le (D : PreAxB) {w q u S T1 : ℕ} (hm : D.m ≤ q) (hp : D.p ≤ q)
    (hw : w ≤ q) (hL : D.L ≤ q) (hLd : D.Ld ≤ q) (hs : D.s ≤ u) (ht : D.t ≤ u) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hS : 1 ≤ S) (hT : 1 ≤ T1) :
    D.t + 2 * (D.s * (2 * (8 * D.m) + 1) * w) + 2 * (D.s * w) + (D.t - D.s) * w + D.s + (w + 2 *
    (8 * D.m) * w) + D.s / 2 + (2 * (8 * D.m) + 1) + w + (D.s + 1) / 2 * w + ((D.s + 1) / 2 -
    D.s / 2) + w + 5 * D.p + 75 * w + 25 * D.L + 25 * D.Ld + 30 ≤ 238 * (S * T1 * u * q ^ 5) := by
  calc _ ≤ u + 2 * (u * (2 * (8 * q) + 1) * q) + 2 * (u * q) + (u) * q + u + (q + 2 * (8 * q) * q) +
          (u) + (2 * (8 * q) + 1) + q + (u) * q + (1) + q + 5 * q + 75 * q + 25 * q + 25 * q + 30 := by
        gcongr <;> omega
    _ ≤ _ := by
      have f0000 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0001 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0002 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0003 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0004 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0005 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0010 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0011 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0012 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0013 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0014 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0015 := band_mono hS hT hu hq (a := 0) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0100 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0101 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0102 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0103 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0104 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0105 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0110 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0111 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0112 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0113 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0114 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f0115 := band_mono hS hT hu hq (a := 0) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1000 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1001 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1002 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1003 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1004 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1005 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1010 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1011 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1012 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1013 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1014 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1015 := band_mono hS hT hu hq (a := 1) (b := 0) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1100 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1101 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1102 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1103 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1104 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1105 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 0) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1110 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1111 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1112 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1113 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1114 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have f1115 := band_mono hS hT hu hq (a := 1) (b := 1) (c := 1) (k := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ring_nf
      ring_nf at f0000 f0001 f0002 f0003 f0004 f0005 f0010 f0011 f0012 f0013 f0014 f0015 f0100 f0101 f0102 f0103 f0104 f0105 f0110 f0111 f0112 f0113 f0114 f0115 f1000 f1001 f1002 f1003 f1004 f1005 f1010 f1011 f1012 f1013 f1014 f1015 f1100 f1101 f1102 f1103 f1104 f1105 f1110 f1111 f1112 f1113 f1114 f1115
      linarith

theorem band_clr_arith {t s m p L Ld P G w X1 X2 X3 X4 X5 Y1 Y2 B0 B1 B2 B3 B4 : ℕ}
    (h0 : B0 ≤ 1 + 5 * (P + G + 3 * w + L + Ld)) (h1 : B1 ≤ 1 + 5 * (P + G + 3 * w + L + Ld))
    (h2 : B2 ≤ 1 + 5 * (P + G + 3 * w + L + Ld)) (h3 : B3 ≤ 1 + 5 * (P + G + 3 * w + L + Ld))
    (h4 : B4 ≤ 1 + 5 * (P + G + 3 * w + L + Ld)) :
    2 * (0 + t) + 2 + (2 * X1 + 2 + (2 * X1 + 2 + (2 * X2 + 2 + (2 * X2 + 2 + (2 * X3 + 2 +
      (2 * s + 2 + (2 * (w + X4) + 2 + (2 * Y1 + 2 + (2 * (2 * (8 * m) + 1) + 2 +
      (2 * w + 2 + (2 * X5 + 2 + (2 * Y2 + 2 + (2 * 0 + 2 + (2 * w + 2 +
      (2 * (5 * p) + 2 + (2 * B0 + 2 + (2 * B1 + 2 + (2 * B2 + 2 + (2 * B3 + 2 +
      (2 * B4 + 2 + 0)))))))))))))))))))) ≤
    50 * (P + G) + 2 * (t + 2 * X1 + 2 * X2 + X3 + s + (w + X4) + Y1 + (2 * (8 * m) + 1) +
      w + X5 + Y2 + w + 5 * p + 75 * w + 25 * L + 25 * Ld + 30) := by
  simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  linarith

/-- **The cleared registers of a loaded file**: `50 (P + G)` for the interchange headers and a
polynomial for the tables and counters. -/
theorem band_load_clr_le (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4)))
    (hac2 : σ (.inl .ac2) = []) (hwn : (σ (.inl (.cm .wn))).length = w) (hp1 : 1 ≤ D.p) :
    ((bandClrB hd).map fun r => 2 * (bandLoad σ hd w D rest r).length + 2).sum ≤
      50 * (D.P + D.G) + 2 * (D.t + 2 * (D.s * (2 * (8 * D.m) + 1) * w) + 2 * (D.s * w) + (D.t - D.s) * w + D.s + (w + 2 * (8 * D.m) * w) + D.s / 2 + (2 * (8 * D.m) + 1) + w + (D.s + 1) / 2 * w + ((D.s + 1) / 2 - D.s / 2) + w + 5 * D.p + 75 * w + 25 * D.L + 25 * D.Ld + 30) := by
  have hP : 2 ≤ D.bP := by simp only [PreAxB.bP]; omega
  have hb : ∀ k, (rsbBank (A := prime + K) hd (D.hs w) (reg (hd k))).length ≤
      1 + 5 * (D.P + D.G + 3 * w + D.L + D.Ld) := by
    intro k
    have h1 := mt_rsb_bank_length_le (A := prime + K) hd (D.hs w) (reg (hd k))
    have h2 := mt_rsb_hs_sum_le D.P D.G (3 * w) D.L D.Ld
    have e : (∑ k, (D.hs w k).length) =
        ∑ k, (sxBits (BinaryInterchangeRun.values D.P D.G (3 * w) D.L D.Ld k)).length := rfl
    omega
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  simp only [bandClrB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [band_load_msk, band_load_bo, band_load_hf, band_load_df, band_load_dtab, band_load_padc,
    band_load_sn, band_load_mwn, band_load_m2wn, band_load_m2n, band_load_smwn, band_load_tswn,
    band_load_kn, band_load_ms, band_load_bx, band_load_pn, band_load_hb, band_load_hb,
    band_load_hb, band_load_hb, band_load_hb, band_lc_cols hP, band_uc_cols, length_bandRcs hP,
    hac2, hwn, List.length_nil]
  simp only [PreAxB.bP, PreAxB.bWd, PreAxB.bB]
  generalize D.s * (2 * (8 * D.m) + 1) * w = X1
  generalize D.s * w = X2
  generalize (D.t - D.s) * w = X3
  generalize 2 * (8 * D.m) * w = X4
  generalize (D.s + 1) / 2 * w = X5
  generalize (rsbBank (A := prime + K) hd (D.hs w) (reg (hd 0))).length = B0 at h0 ⊢
  generalize (rsbBank (A := prime + K) hd (D.hs w) (reg (hd 1))).length = B1 at h1 ⊢
  generalize (rsbBank (A := prime + K) hd (D.hs w) (reg (hd 2))).length = B2 at h2 ⊢
  generalize (rsbBank (A := prime + K) hd (D.hs w) (reg (hd 3))).length = B3 at h3 ⊢
  generalize (rsbBank (A := prime + K) hd (D.hs w) (reg (hd 4))).length = B4 at h4 ⊢
  exact band_clr_arith h0 h1 h2 h3 h4

end Poly

/-! ### The pipeline records -/

section Pipeline

variable {n : ℕ} {t₀ K : ℕ}

theorem mLogLog_le_cube (m : ℕ) : mLogLog m ≤ m ^ 3 := by
  unfold mLogLog
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp
  have h1 : Nat.log 2 m + 1 ≤ m := Nat.log_lt_self 2 (by omega)
  have h2 : Nat.log 2 (Nat.log 2 m) + 1 ≤ m := by
    rcases Nat.eq_zero_or_pos (Nat.log 2 m) with h3 | h3
    · rw [h3]; simp; omega
    · have := Nat.log_lt_self 2 (show Nat.log 2 m ≠ 0 by omega); omega
  calc m * (Nat.log 2 m + 1) * (Nat.log 2 (Nat.log 2 m) + 1) ≤ m * m * m :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    _ = m ^ 3 := by ring

/-- The product cost as a cubic in an upper bound `q ≥ w`. -/
theorem band_rmul_le {T w q : ℕ} (hw : w ≤ q) (hq : 1 ≤ q) :
    rmulCost T w ≤ 288 * (ssMulConst + 1) * (T + 1) * q ^ 3 := by
  unfold rmulCost
  have h1 : mLogLog w ≤ q ^ 3 := (mLogLog_le_cube w).trans (Nat.pow_le_pow_left hw 3)
  have h2 : ssMulConst * (T + 1) * mLogLog w ≤ (ssMulConst + 1) * (T + 1) * q ^ 3 :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) h1
  have h3 : q ≤ q ^ 3 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 3 := Nat.pow_le_pow_right hq (by norm_num)
  have hS : 2 ≤ ssMulConst + 1 := by
    have : 627 ≤ ssMulConst := by unfold ssMulConst; omega
    omega
  have h4 : 2 * q ^ 3 ≤ (ssMulConst + 1) * (T + 1) * q ^ 3 :=
    Nat.mul_le_mul_right _ (le_trans hS (Nat.le_mul_of_pos_right _ (by omega)))
  have e : 288 * (ssMulConst + 1) * (T + 1) * q ^ 3 =
      288 * ((ssMulConst + 1) * (T + 1) * q ^ 3) := by ring
  omega

/-- The bound of the polynomial loader terms of every axis at length `n`. -/
def mtBandU (n Tm cw cW : ℕ) : ℕ :=
  4 * 10 ^ 9 * (ssMulConst + 1) * (Tm + 1) * r n * ((cW + cw + 6) * p n) ^ 5

theorem band_preDB_facts (h : Big n) (hd0 : 0 < d n) {w W cw cW : ℕ} (hwc : w ≤ cw * p n)
    (hWc : W ≤ cW * p n) (k : ℕ) :
    (preDB n W hd0 k).s ≤ (preDB n W hd0 k).t ∧ (preDB n W hd0 k).P ≤ T n ∧
      (preDB n W hd0 k).G ≤ T n ∧ 1 ≤ (preDB n W hd0 k).p ∧
      (preDB n W hd0 k).t + 1 ≤ 2 * r n ∧ mtRsbQ (preDB n W hd0 k) w ≤ (cW + cw + 6) * p n := by
  obtain ⟨hP, hG⟩ := mt_rsb_PG_le h (rsbAx hd0 k)
  have hst := (mt_s_lt_t h (rsbAx hd0 k)).le
  have htr := mt_t_le_r n (rsbAx hd0 k)
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hp13 := h.thirteen_le_p
  have hfw := Mult.FastB0.fastWindow_le_third (two_le_alpha h.1) hp13
  have hα := mt_alpha_le_p h
  have hl1 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n (rsbAx hd0 k)
  have hl2 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n (rsbAx hd0 0)
  have hlp := mt_ℓ_le_p h
  refine ⟨hst, hP, hG, by simp only [preDB]; omega, by simp only [preDB]; omega, ?_⟩
  simp only [mtRsbQ, preDB]
  nlinarith

/-- The polynomial unit of one axis against `mtBandU`. -/
theorem band_unit_le (h : Big n) (hd0 : 0 < d n) {Tm w W cw cW : ℕ} (hwc : w ≤ cw * p n)
    (hWc : W ≤ cW * p n) (k : ℕ) :
    2 * 10 ^ 9 * ((ssMulConst + 1) * (Tm + 1) * ((preDB n W hd0 k).t + 1) *
      mtRsbQ (preDB n W hd0 k) w ^ 5) ≤ mtBandU n Tm cw cW := by
  obtain ⟨-, -, -, -, ht, hQ⟩ := band_preDB_facts h hd0 hwc hWc (w := w) k
  have h1 : (ssMulConst + 1) * (Tm + 1) * ((preDB n W hd0 k).t + 1) *
      mtRsbQ (preDB n W hd0 k) w ^ 5 ≤
      (ssMulConst + 1) * (Tm + 1) * (2 * r n) * ((cW + cw + 6) * p n) ^ 5 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) (Nat.pow_le_pow_left hQ 5)
  have e : mtBandU n Tm cw cW =
      2 * 10 ^ 9 * ((ssMulConst + 1) * (Tm + 1) * (2 * r n) * ((cW + cw + 6) * p n) ^ 5) := by
    unfold mtBandU; ring
  rw [e]
  exact Nat.mul_le_mul_left _ h1

/-- **One step of the loader** at the pipeline records. -/
theorem band_step_le (h : Big n) (hd0 : 0 < d n) {Tm w W cw cW : ℕ} (hwc : w ≤ cw * p n)
    (hWc : W ≤ cW * p n) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (rest : List (Fin (prime + K + 4))) (k : ℕ) :
    bandPreCost Tm σ hd w (preDB n W hd0 k) rest ≤
      ((bandClrB hd).map fun r => 2 * (σ r).length + 2).sum + 2 * (σ (.inl .tb)).length +
        200 * T n + 10 ^ 9 * ((ssMulConst + 1) * (Tm + 1) * ((preDB n W hd0 k).t + 1) *
          mtRsbQ (preDB n W hd0 k) w ^ 5) := by
  obtain ⟨hst, hP, hG, -, -, -⟩ := band_preDB_facts h hd0 hwc hWc (w := w) k
  have hq : 1 ≤ mtRsbQ (preDB n W hd0 k) w := by simp only [mtRsbQ]; omega
  have key := band_preCost_le σ hd w (preDB n W hd0 k) rest (T := Tm) (q := mtRsbQ (preDB n W hd0 k) w) (u := (preDB n W hd0 k).t + 1)
    (S := ssMulConst + 1) (T1 := Tm + 1) (by simp only [mtRsbQ]; omega)
    (by simp only [mtRsbQ]; omega) (by simp only [mtRsbQ]; omega) (by simp only [mtRsbQ]; omega)
    (by simp only [mtRsbQ]; omega) (by simp only [mtRsbQ]; omega) (by simp only [mtRsbQ]; omega)
    (by omega) (by omega) hq (by omega) (by omega) (by omega)
    (band_rmul_le (by simp only [mtRsbQ]; omega) hq |>.trans (le_of_eq (by ring)))
  refine key.trans ?_
  have : 100 * ((preDB n W hd0 k).P + (preDB n W hd0 k).G) ≤ 200 * T n := by omega
  omega

/-- A file of the band stage at step `k` is a loaded base file. -/
theorem bandCfgB_load {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} {hd : Fin 5 → Fin t₀}
    {w W : ℕ} {hd0 : 0 < d n} {rest : List (Fin (prime + K + 4))} (hbase : BandBase σ₀ w hd)
    (hA3 : 3 ≤ prime + K) (k : ℕ) :
    ∃ σ, BandBase σ w hd ∧ bandCfgB σ₀ hd n w W hd0 rest k =
      bandLoad σ hd w (preDB n W hd0 k) (preRecsB n W hd0 (k + 1) ++ rest) := by
  cases k with
  | zero => exact ⟨σ₀, hbase, rfl⟩
  | succ j => exact ⟨bandCfgB σ₀ hd n w W hd0 rest j, bandCfgB_base hbase hA3 j, rfl⟩

/-- The cleared registers of the file of step `k`. -/
theorem band_cfg_clr_le (h : Big n) (hd0 : 0 < d n) {w W cw cW : ℕ} (hwc : w ≤ cw * p n)
    (hWc : W ≤ cW * p n) {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {hd : Fin 5 → Fin t₀} {rest : List (Fin (prime + K + 4))} (hbase : BandBase σ₀ w hd)
    (hA3 : 3 ≤ prime + K) (k : ℕ) {S T1 : ℕ} (hS : 1 ≤ S) (hT : 1 ≤ T1) :
    ((bandClrB hd).map fun r => 2 * (bandCfgB σ₀ hd n w W hd0 rest k r).length + 2).sum ≤
      100 * T n + 476 * (S * T1 * ((preDB n W hd0 k).t + 1) * mtRsbQ (preDB n W hd0 k) w ^ 5) := by
  obtain ⟨σ, hσ, e⟩ := bandCfgB_load (W := W) (hd0 := hd0) (rest := rest) hbase hA3 k
  obtain ⟨hst, hP, hG, hp1, -, -⟩ := band_preDB_facts h hd0 hwc hWc (w := w) k
  rw [e]
  have h1 := band_load_clr_le σ hd w (preDB n W hd0 k) (preRecsB n W hd0 (k + 1) ++ rest) hσ.free.ac2 hσ.wn hp1
  have hq : 1 ≤ mtRsbQ (preDB n W hd0 k) w := by simp only [mtRsbQ]; omega
  have h2 := band_polyClr_le (preDB n W hd0 k) (w := w) (q := mtRsbQ (preDB n W hd0 k) w) (u := (preDB n W hd0 k).t + 1) (by simp only [mtRsbQ]; omega)
    (by simp only [mtRsbQ]; omega) (by simp only [mtRsbQ]; omega) (by simp only [mtRsbQ]; omega)
    (by simp only [mtRsbQ]; omega) (by omega) (by omega) hq (by omega) hS hT
  omega

/-- **The cost of the band loader at every step**: the cleared registers of the base file
(at most `T w` symbols each) at step `0`, `O(T)` for the record fields and headers, and the
polynomial `mtBandU` for the tables, counters and the axis factorization. -/
theorem mt_band_cp_le (h : Big n) (hd0 : 0 < d n) {Tm w W cw cW : ℕ} (hwc : w ≤ cw * p n)
    (hWc : W ≤ cW * p n) (hA3 : 3 ≤ prime + K) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (hd : Fin 5 → Fin t₀) (rest : List (Fin (prime + K + 4))) (hbase : BandBase σ₀ w hd)
    (hσ₀ : ∀ r ∈ bandClrB hd, (σ₀ r).length ≤ T n * w) (k : ℕ) :
    bandCpB Tm σ₀ hd n w W hd0 rest k ≤ 42 * (T n * w) + 300 * T n + 42 + mtBandU n Tm cw cW := by
  cases k with
  | zero =>
    have hs := band_step_le h hd0 (Tm := Tm) hwc hWc σ₀ hd (preRecsB n W hd0 1 ++ rest) 0
    have hU := band_unit_le h hd0 (Tm := Tm) hwc hWc (w := w) 0
    have hclr : ((bandClrB hd).map fun r => 2 * (σ₀ r).length + 2).sum ≤
        21 * (2 * (T n * w) + 2) := by
      have := List.sum_le_length_nsmul ((bandClrB hd).map fun r => 2 * (σ₀ r).length + 2)
        (2 * (T n * w) + 2) (by
          intro x hx
          obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
          have := hσ₀ r hr
          omega)
      simpa [bandClrB] using this
    rw [hbase.free.tb] at hs
    simp only [bandCpB, List.length_nil] at hs ⊢
    omega
  | succ j =>
    have hs := band_step_le h hd0 (Tm := Tm) hwc hWc (bandCfgB σ₀ hd n w W hd0 rest j) hd
      (preRecsB n W hd0 (j + 2) ++ rest) (j + 1)
    have hU := band_unit_le h hd0 (Tm := Tm) hwc hWc (w := w) (j + 1)
    have hU' := band_unit_le h hd0 (Tm := Tm) hwc hWc (w := w) j
    have hc := band_cfg_clr_le h hd0 hwc hWc (rest := rest) hbase hA3 j (S := ssMulConst + 1)
      (T1 := Tm + 1) (by omega) (by omega)
    obtain ⟨σ, -, e⟩ := bandCfgB_load (W := W) (hd0 := hd0) (rest := rest) hbase hA3 j
    have htb : (bandCfgB σ₀ hd n w W hd0 rest j (.inl .tb)).length = 0 := by
      rw [e, band_load_tb]
    rw [htb] at hs
    simp only [bandCpB]
    omega

/-- **The cleared registers of a band file are short**: eventually, in a file configured for
step `k` of the band stage, the registers the next loader clears hold at most `T w` symbols. -/
theorem mt_band_clr_cfg (cw cW : ℕ) :
    ∀ᶠ n in atTop, ∀ {t₀ K : ℕ} (hd0 : 0 < d n) (w W : ℕ)
      (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
      (rest : List (Fin (prime + K + 4))) (k : ℕ),
      101 ≤ w → w ≤ cw * p n → W ≤ cW * p n → BandBase σ w hd → 3 ≤ prime + K →
      ∀ x ∈ bandClrB hd, (bandCfgB σ hd n w W hd0 rest k x).length ≤ T n * w := by
  filter_upwards [eventually_big, mt_poly_r_le_T (952 * (cW + cw + 6) ^ 5 * 6 ^ 5) 5]
    with n h hT
  intro t₀ K hd0 w W σ hd rest k hw hwc hWc hbase hA3 x hx
  have hc := band_cfg_clr_le h hd0 hwc hWc (rest := rest) hbase hA3 k (S := 1) (T1 := 1) le_rfl
    le_rfl
  obtain ⟨-, -, -, -, ht, hQ⟩ := band_preDB_facts h hd0 hwc hWc (w := w) k
  have hmem := List.le_sum_of_mem (List.mem_map_of_mem
    (f := fun r => 2 * (bandCfgB σ hd n w W hd0 rest k r).length + 2) hx)
  have hY : 476 * (1 * 1 * ((preDB n W hd0 k).t + 1) * mtRsbQ (preDB n W hd0 k) w ^ 5) ≤ T n := by
    calc 476 * (1 * 1 * ((preDB n W hd0 k).t + 1) * mtRsbQ (preDB n W hd0 k) w ^ 5) ≤
        476 * ((2 * r n) * ((cW + cw + 6) * (6 * b n)) ^ 5) := by
          rw [one_mul, one_mul]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul ht (Nat.pow_le_pow_left hQ 5))
      _ = 952 * (cW + cw + 6) ^ 5 * 6 ^ 5 * b n ^ 5 * r n := by ring
      _ ≤ T n := hT
  have hT101 : 101 * T n ≤ T n * w := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hw
  omega

end Pipeline

end IntegerMultBounds.MathlibTM2.Cost
