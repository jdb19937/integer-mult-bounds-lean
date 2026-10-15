module

public import IntegerMultBounds.MathlibTM2.Cost.DirectScale
public import IntegerMultBounds.MathlibTM2.Fast.PrepA

/-!
# Cost matching: the resampling `Ã` with its loader

`rsaStage_exec` (`Fast/PrepA.lean`) runs `Ã` along every axis of the padded box with the loader
`preA` in
`rsaAllCost Tm t₀ w m d t hd0 (rsaPipeData n (preHsA n w hd0)) hd (preCpA V₀ hd n w W hd0 rest) T`
steps, `m = windowA p α`, on a host of `Tm` stacks. `mt_rsa_stage_le_linear` bounds it eventually by
`C (totResamp + totDirectCRT + T p)`, with `C` depending on `Tm`, `t₀`, `cw`, `cW` only, for
`1 ≤ w ≤ cw p`, `W ≤ cW p` and the registers cleared by the first loader step of length at most
`T w`.

| piece | `ℕ` bound | term |
|---|---|---|
| lines of one axis (`rsaAxisCost`) | `T ((2m+1)(rmulCost + 13w + 17) + 60w + 8L + 80) + 4` (`mt_rsa_axis_le`) | `totResamp`, from `2m + 1 ≤ 4 α √p` (`mt_rsa_window_real`) |
| interchange with the last axis | `swapConst · 3 T w · ℓ^τ + 1` each (`mt_rsa_swap_le`), `2 (d - 1)` of them | `totDirectCRT`: `d T w ℓ^τ ≤ cw T p d (1 + ℓ^τ)` |
| loader after the first axis (`preCostA`) | `62 T + 1600200 r Y^4` (`mt_rsa_cp_succ_le`), `Y = (cw + cW + 2)(p + 1)` | `O(d T)` in `totResamp`; `O(d r Y^4) = o(T)` |
| first loader step | `28 T w + 29 + 42 T + 1600000 r Y^4` (`mt_rsa_cp_zero_le`) | `totResamp`, `T p` |
| banks, headers, swap overheads | `O(T Y)` per step (`mt_rsa_term_nat`) | `totResamp` |

The loader's `O(T)` per axis comes from the unary fields `P`, `G` (products of axis lengths,
up to `T`) that it reads and turns into interchange headers. The tables cost
`preKA D · tblC W w ≤ 1485104 r Y^4` atoms-times-steps per axis (`mt_rsa_preCost_le`), and
`mt_poly_r_le_T` puts `d r Y^4 ≤ B^5 r` below `T`.

**Misfit.** The `2 (d - 1)` interchanges of axis `i` with the last axis cost
`Θ(d T w ℓ^τ)` in total. This is not `O(totResamp)`: `totResamp = d T p^{1/2} α M(p)` and
`ℓ^τ / (p^{1/2+δ} α) ≈ (B/d)^τ / (6^{5/8} 12^{1/4} B^{7/8} d^{1/2}) → ∞` (`ℓ ≈ B/d`,
`α ≈ (12 d² B)^{1/4}`, `d = B^{2^{-30}}`). The sharp routing charge is `O(totDirectCRT) = O(T p d (1 + ℓ^τ))`.
`mt_rsa_stage_le` retains the old quadratic envelope as a compatibility wrapper.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds
  IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-! ### The lines -/

/-- One line of `Ã`: at most `t ((2m + 1)(rmulCost + 13 w + 17) + 58 w + 8 L + 78)` steps. -/
theorem mt_rsa_line_le (T w s t m L : ℕ) (hst : s ≤ t) (hms : m ≤ s) (ht : 1 ≤ t) :
    rsaLineCost T w s t m L ≤
      t * ((2 * m + 1) * (rmulCost T w + 13 * w + 17) + 58 * w + 8 * L + 78) := by
  unfold rsaLineCost rsaRowsCost rsaRowCost rsaTermsCost rsaTermCost
  generalize rmulCost T w = R
  obtain ⟨a, rfl⟩ : ∃ a, s = m + a := ⟨s - m, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, t = m + a + c := ⟨t - (m + a), by omega⟩
  rw [show m + a - m = a by omega, show m + a + c - (m + a) = c by omega]
  ring_nf
  nlinarith [Nat.zero_le (m * w), Nat.zero_le (a * w), Nat.zero_le (c * w), Nat.zero_le (m * L)]

/-- One axis of `Ã` on a box of `N` records: at most
`N ((2m + 1)(rmulCost + 13 w + 17) + 60 w + 8 L + 80) + 4` steps. -/
theorem mt_rsa_axis_le (T w s t m L N : ℕ) (hst : s ≤ t) (hms : m ≤ s) (ht : 1 ≤ t) :
    rsaAxisCost T w s t m L (N / t) ≤
      N * ((2 * m + 1) * (rmulCost T w + 13 * w + 17) + 60 * w + 8 * L + 80) + 4 := by
  have h1 := mt_rsa_line_le T w s t m L hst hms ht
  have hB : N / t * t ≤ N := Nat.div_mul_le_self N t
  unfold rsaAxisCost
  set X := (2 * m + 1) * (rmulCost T w + 13 * w + 17) + 58 * w + 8 * L + 78 with hX
  generalize N / t = B at hB ⊢
  have h2 : B * (rsaLineCost T w s t m L + 2) ≤ B * (t * X + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : B * (t * X + 2) + 2 * (B * t * w) ≤ B * t * (X + 2 * w + 2) := by
    have : B ≤ B * t := Nat.le_mul_of_pos_right _ ht
    nlinarith
  have h4 : B * t * (X + 2 * w + 2) ≤ N * (X + 2 * w + 2) := Nat.mul_le_mul_right _ hB
  calc _ ≤ N * (X + 2 * w + 2) + 4 := by omega
    _ = _ := by rw [hX]; ring

/-! ### Banks and the loader -/

section Loader

variable {t₀ A : ℕ}

/-- A bank register holds at most one header and a separator. -/
theorem mt_rsa_bank_le (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool) (j : Fin (swapT t₀)) :
    (rsaBank hd hs j : List (Fin (A + 4))).length ≤ 1 + ∑ k, (hs k).length := by
  unfold rsaBank
  split_ifs with h
  · simp only [List.length_cons, List.length_map]
    have := Finset.single_le_sum (f := fun k => (hs k).length) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (Classical.choose h))
    omega
  · simp

/-- The bank of `swapT t₀` registers holds at most `swapT t₀ (1 + Σ |hs k|)` symbols. -/
theorem mt_rsa_bankSum_le (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool) :
    ∑ j, (rsaBank hd hs j : List (Fin (A + 4))).length ≤
      swapT t₀ * (1 + ∑ k, (hs k).length) := by
  calc ∑ j, (rsaBank hd hs j : List (Fin (A + 4))).length ≤
      ∑ _j : Fin (swapT t₀), (1 + ∑ k, (hs k).length) :=
        Finset.sum_le_sum fun j _ => mt_rsa_bank_le hd hs j
    _ = swapT t₀ * (1 + ∑ k, (hs k).length) := by simp

/-- The canonical headers of `values P G B h d` have at most `P + G + B + h + d` bits. -/
theorem mt_rsa_hsSum_le (P G B h d : ℕ) :
    ∑ k, (sxBits (BinaryInterchangeRun.values P G B h d k)).length ≤ P + G + B + h + d := by
  calc ∑ k, (sxBits (BinaryInterchangeRun.values P G B h d k)).length ≤
      ∑ k, BinaryInterchangeRun.values P G B h d k :=
        Finset.sum_le_sum fun k _ => mt_length_sxBits_le _
    _ = P + G + B + h + d := by
        simp [Fin.sum_univ_five, BinaryInterchangeRun.values]



/-- **One loader step** on any register file: the cleared registers, `42 N` for the unary
fields `P`, `G ≤ N`, and `1600000 r Y^4` for everything else (the table program's
`preKA D · tblC W w ≤ 1485104 r Y^4` above all), when the axis lengths are at most `r` and the
other fields, `w` and `W` at most `Y`. -/
theorem mt_rsa_preCost_le (V : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxA)
    {N r Y : ℕ} (ht : D.t ≤ r) (hs : D.s ≤ D.t) (hm : D.m ≤ Y) (hq : D.q ≤ Y) (hL : D.L ≤ Y)
    (hLd : D.Ld ≤ Y) (hα : D.α ≤ Y) (hp : D.p ≤ Y) (hW : D.W ≤ Y) (hw : w ≤ Y) (hP : D.P ≤ N)
    (hG : D.G ≤ N) (hY : 1 ≤ Y) (hr : 1 ≤ r) :
    preCostA V hd w D ≤ (((preClrA hd).map fun x => 2 * (V.get x).length + 2).sum + 1) +
      42 * N + 1600000 * (r * Y ^ 4) := by
  have hY4 : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ hY
  have hYY : Y ≤ Y ^ 2 := by nlinarith
  have hY2 : Y ^ 2 ≤ Y ^ 4 := Nat.pow_le_pow_right hY (by norm_num)
  have hY1 : Y ≤ Y ^ 4 := hYY.trans hY2
  have hrr : r ≤ r * Y ^ 4 := Nat.le_mul_of_pos_right _ hY4
  have hr1 : r * Y ≤ r * Y ^ 4 := Nat.mul_le_mul_left _ hY1
  have hr2 : r * Y ^ 2 ≤ r * Y ^ 4 := Nat.mul_le_mul_left _ hY2
  have hYr : Y ^ 4 ≤ r * Y ^ 4 := Nat.le_mul_of_pos_left _ hr
  have hrY : r * Y ≤ r * Y ^ 2 := Nat.mul_le_mul_left _ hYY
  have hr0 : r ≤ r * Y ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hY0 : Y ^ 2 ≤ r * Y ^ 2 := Nat.le_mul_of_pos_left _ hr
  -- the table program
  have hK : preKA D ≤ 1838 * (r * Y ^ 2) := by
    unfold preKA
    have h1 : D.t * (2 * D.m + 1) ≤ r * (3 * Y) := Nat.mul_le_mul ht (by omega)
    have h2 : D.t * (2 * D.m + 1) * (310 * D.p + 110) ≤ r * (3 * Y) * (420 * Y) :=
      Nat.mul_le_mul h1 (by omega)
    have e : r * (3 * Y) * (420 * Y) = 1260 * (r * Y ^ 2) := by ring
    omega
  have hC : tblC D.W w ≤ 808 * Y ^ 2 := by unfold tblC; nlinarith
  have hKC : preKA D * tblC D.W w ≤ 1485104 * (r * Y ^ 4) := by
    calc _ ≤ 1838 * (r * Y ^ 2) * (808 * Y ^ 2) := Nat.mul_le_mul hK hC
      _ = 1485104 * (r * Y ^ 4) := by ring
  have hE : D.t * (2 * D.m + 1) * w ≤ 3 * (r * Y ^ 2) := by
    calc D.t * (2 * D.m + 1) * w ≤ r * (3 * Y) * Y :=
          Nat.mul_le_mul (Nat.mul_le_mul ht (by omega)) hw
      _ = 3 * (r * Y ^ 2) := by ring
  have hlens : ([D.s, D.t, D.α, D.m, D.p].map fun k => k * (4 * D.W + 10) + 6 * D.W + 10).sum ≤
      200 * (r * Y ^ 2) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have g1 : D.s * (4 * D.W + 10) ≤ r * (14 * Y) := Nat.mul_le_mul (by omega) (by omega)
    have g2 : D.t * (4 * D.W + 10) ≤ r * (14 * Y) := Nat.mul_le_mul ht (by omega)
    have g3 : D.α * (4 * D.W + 10) ≤ Y * (14 * Y) := Nat.mul_le_mul hα (by omega)
    have g4 : D.m * (4 * D.W + 10) ≤ Y * (14 * Y) := Nat.mul_le_mul hm (by omega)
    have g5 : D.p * (4 * D.W + 10) ≤ Y * (14 * Y) := Nat.mul_le_mul hp (by omega)
    have e1 : r * (14 * Y) = 14 * (r * Y) := by ring
    have e2 : Y * (14 * Y) = 14 * Y ^ 2 := by ring
    omega
  have hVM : preVMCost 48 D.W w [D.s, D.t, D.α, D.m, D.p] (preKA D) (D.t * (2 * D.m + 1) * w) ≤
      1500000 * (r * Y ^ 4) := by
    unfold preVMCost
    omega
  -- the counters
  have hNum : preNumCost D w ≤ 100 * (r * Y ^ 2) := by
    unfold preNumCost
    have g1 : D.s * (4 * w + 7) + (D.t - D.s) * (4 * w + 7) ≤ r * (11 * Y) := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' hs]; exact Nat.mul_le_mul ht (by omega)
    have g2 : D.m * (4 * w + 7) ≤ Y * (11 * Y) := Nat.mul_le_mul hm (by omega)
    have g3 : D.s * (4 * D.L + 10) ≤ r * (14 * Y) := Nat.mul_le_mul (by omega) (by omega)
    have e1 : r * (11 * Y) = 11 * (r * Y) := by ring
    have e2 : Y * (11 * Y) = 11 * Y ^ 2 := by ring
    have e3 : r * (14 * Y) = 14 * (r * Y) := by ring
    omega
  have hHdr : preHdrCost D w ≤ 32 * N + 90 * Y + 31 := by unfold preHdrCost; omega
  have hF : D.fields.sum ≤ 2 * r + 7 * Y + 2 * N := by
    simp only [PreAxA.fields, List.sum_cons, List.sum_nil]; omega
  unfold preCostA
  omega

/-- A header register of a loaded file. -/
theorem mt_rsa_hdr_len_le (xr : RsaX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxA) (k : Fin 5) :
    (preBankA xr hd (D.hs w) (.sw (reg (hd k)))).length ≤ 1 + (D.P + D.G + 3 * w + D.L + D.Ld) := by
  simp only [preBankA]
  rw [if_pos ⟨k, rfl⟩]
  exact (mt_rsa_bank_le hd (D.hs w) _).trans (by
    have := mt_rsa_hsSum_le D.P D.G (3 * w) D.L D.Ld
    simp only [PreAxA.hs]
    omega)

/-- The registers cleared by the next loader step, in a file loaded with `D`: at most
`20 N + 200 r Y^2` steps. -/
theorem mt_rsa_clr_load_le (V : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxA)
    (rest : List (Fin (A + 4))) {N r Y : ℕ} (ht : D.t ≤ r) (hs : D.s ≤ D.t) (hm : D.m ≤ Y)
    (hq : D.q ≤ Y) (hL : D.L ≤ Y) (hLd : D.Ld ≤ Y) (hw : w ≤ Y) (hP : D.P ≤ N) (hG : D.G ≤ N)
    (hY : 1 ≤ Y) (hr : 1 ≤ r) :
    ((preClrA hd).map fun x => 2 * ((preLoadA V hd w D rest).get x).length + 2).sum + 1 ≤
      20 * N + 200 * (r * Y ^ 2) := by
  have h0 := mt_rsa_hdr_len_le V.xr hd w D 0
  have h1 := mt_rsa_hdr_len_le V.xr hd w D 1
  have h2 := mt_rsa_hdr_len_le V.xr hd w D 2
  have h3 := mt_rsa_hdr_len_le V.xr hd w D 3
  have h4 := mt_rsa_hdr_len_le V.xr hd w D 4
  simp only [preClrA, preHA, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, preLoadA,
    RsaV.get, Function.update_apply, reduceCtorEq, if_false, if_true, tblStreamA_cstream,
    length_cstream, length_rsaTabL, List.length_replicate, length_binSyms]
  have hYY : Y ≤ Y ^ 2 := by nlinarith
  have hr0 : r ≤ r * Y ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hY0 : Y ^ 2 ≤ r * Y ^ 2 := Nat.le_mul_of_pos_left _ hr
  have g1 : D.t * (2 * D.m + 1) * w ≤ 3 * (r * Y ^ 2) := by
    calc D.t * (2 * D.m + 1) * w ≤ r * (3 * Y) * Y :=
          Nat.mul_le_mul (Nat.mul_le_mul ht (by omega)) hw
      _ = 3 * (r * Y ^ 2) := by ring
  have g2 : D.s * w + (D.t - D.s) * w ≤ r * Y ^ 2 := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' hs]
    exact (Nat.mul_le_mul ht hw).trans (Nat.mul_le_mul_left _ hYY)
  have g3 : D.m * w ≤ Y ^ 2 := by rw [sq]; exact Nat.mul_le_mul hm hw
  omega


end Loader

/-! ### The interchanges -/

/-- The product of the axis lengths before `i` is at most the box. -/
theorem mt_rsa_pre_le {d : ℕ} (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (i : ℕ) :
    rsaPre t i ≤ ∏ j, t j := by
  rw [← List.prod_ofFn]
  exact (List.take_sublist _ _).prod_le_prod fun a ha => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha; exact ht j

/-- The product of the axis lengths between `i` and the last axis is at most the box. -/
theorem mt_rsa_mid_le {d : ℕ} (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (i : ℕ) :
    rsaMid t i ≤ ∏ j, t j := by
  rw [← List.prod_ofFn]
  exact ((List.dropLast_sublist _).trans (List.drop_sublist _ _)).prod_le_prod fun a ha => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha; exact ht j

/-- The volume of the interchange of axis `i` with the last axis. -/
theorem mt_rsa_vol {d : ℕ} (t : Fin d → ℕ) (i : Fin d) (hi : (i : ℕ) + 1 < d) :
    rsaPre t i * t i * rsaMid t i * t ⟨d - 1, by omega⟩ = ∏ j, t j := by
  rw [← rsaPre_mul t i, rsaSuf_last t i hi]; ring

/-- Both interchange dimensions are positive. -/
theorem mt_rsa_pre_pos {d : ℕ} (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (i : Fin d)
    (hi : (i : ℕ) + 1 < d) : 0 < rsaPre t i ∧ 0 < rsaMid t i := by
  have hpos : 0 < ∏ j, t j := Finset.prod_pos fun j _ => ht j
  rw [← mt_rsa_vol t i hi] at hpos
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩ <;>
    simp [h0] at hpos

section Pipeline

variable {n : ℕ} {t₀ : ℕ}

/-- One interchange of the `Ã` stage costs at most `swapConst · 3 T w · ℓ^τ + 1`. -/
theorem mt_rsa_swap_le (h : Big n) {w : ℕ} (hw : 1 ≤ w) (i : Fin (d n))
    (hi : (i : ℕ) + 1 < d n) {h₁ h₂ : ℕ} (hs : Fin 5 → List Bool)
    (h12 : 2 ^ h₁ * 2 ^ h₂ = t n i * t n ⟨d n - 1, by omega⟩) (hh₁ : h₁ ≤ ℓ n)
    (hh₂ : h₂ ≤ ℓ n) (hle₁ : h₁ ≤ h₂ + 1) (hle₂ : h₂ ≤ h₁ + 1)
    (hv : ∀ k, Counter.value (hs k) =
      BinaryInterchangeRun.values (rsaPre (t n) i) (rsaMid (t n) i) (3 * w) h₁ h₂ k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) :
    (BinaryInterchangeRun.cost (rsaPre (t n) i) (rsaMid (t n) i) (3 * w) h₁ h₂ hs : ℝ) ≤
      swapConst * (T n * (3 * w) : ℕ) * (ℓ n : ℝ) ^ Parameters.tau + 1 := by
  have ht : ∀ j, 1 ≤ t n j := fun j => mt_t_pos n j
  obtain ⟨hP, hG⟩ := mt_rsa_pre_pos (t n) ht i hi
  have hl : 1 ≤ ℓ n := by have := h.two_le_ℓ; omega
  have h1 := mt_swap_le hs hP hG (by omega) hle₁ hle₂ hv hc hh₁ hh₂ hl
  have e : rsaPre (t n) i * 2 ^ h₁ * rsaMid (t n) i * 2 ^ h₂ * (3 * w) = T n * (3 * w) := by
    rw [← mt_prod_t h, ← mt_rsa_vol (t n) i hi]
    calc rsaPre (t n) i * 2 ^ h₁ * rsaMid (t n) i * 2 ^ h₂ * (3 * w) =
        rsaPre (t n) i * rsaMid (t n) i * (2 ^ h₁ * 2 ^ h₂) * (3 * w) := by ring
      _ = _ := by rw [h12]; ring
  rwa [e] at h1


/-- `m = windowA p α ≤ p`. -/
theorem mt_rsa_window_le (h : Big n) : windowA (p n) (alpha n) ≤ p n :=
  (IntegerMultBounds.MathlibTM2.Mult.Pipeline.windowA_spec (IntegerMultBounds.MathlibTM2.Mult.Pipeline.alpha_sq_lt_p h)).2.2

/-- The fields of the loader records of the pipeline: lengths below `r`, small values below
any `Y ≥ p + 1`, products below `T`. -/
theorem mt_rsa_preDA (h : Big n) (hd0 : 0 < d n) (W k : ℕ) {Y : ℕ} (hY : p n + 1 ≤ Y)
    (hW : W ≤ Y) :
    (preDA n W hd0 k).t ≤ r n ∧ (preDA n W hd0 k).s ≤ (preDA n W hd0 k).t ∧
      (preDA n W hd0 k).m ≤ Y ∧ (preDA n W hd0 k).q ≤ Y ∧ (preDA n W hd0 k).L ≤ Y ∧
      (preDA n W hd0 k).Ld ≤ Y ∧ (preDA n W hd0 k).α ≤ Y ∧ (preDA n W hd0 k).p ≤ Y ∧
      (preDA n W hd0 k).W ≤ Y ∧ (preDA n W hd0 k).P ≤ T n ∧ (preDA n W hd0 k).G ≤ T n := by
  have ht : ∀ j, 1 ≤ t n j := fun j => mt_t_pos n j
  have hl := mt_ℓ_le_p h
  have hα := mt_alpha_le_p h
  have hm := mt_rsa_window_le h
  have hL1 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n (rsaStepAx hd0 k)
  have hL2 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n (rsaStepAx hd0 0)
  refine ⟨mt_t_le_r n _, (mt_s_lt_t h _).le, by simp only [preDA]; omega, ?_, by simp only [preDA]; omega,
    by simp only [preDA]; omega, by simp only [preDA]; omega, by simp only [preDA]; omega,
    by simp only [preDA]; omega, ?_, ?_⟩
  · simp only [preDA]; split_ifs <;> omega
  · simp only [preDA]; rw [← mt_prod_t h]; exact mt_rsa_pre_le _ ht _
  · simp only [preDA]; rw [← mt_prod_t h]; exact mt_rsa_mid_le _ ht _

/-- The loader steps after the first: `cp (k + 1) ≤ 62 T + 1600200 r Y^4`. -/
theorem mt_rsa_cp_succ_le {K : ℕ} (h : Big n) (hd0 : 0 < d n) (w W : ℕ)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (hd : Fin 5 → Fin t₀) (rest : List (Fin (prime + K + 4)))
    {Y : ℕ} (hY : p n + 1 ≤ Y) (hw : w ≤ Y) (hW : W ≤ Y) (k : ℕ) :
    preCpA V₀ hd n w W hd0 rest (k + 1) ≤ 62 * T n + 1600200 * (r n * Y ^ 4) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := mt_rsa_preDA h hd0 W (k + 1) hY hW
  obtain ⟨b1, b2, b3, b4, b5, b6, -, -, -, b10, b11⟩ := mt_rsa_preDA h hd0 W k hY hW
  have hY1 : 1 ≤ Y := by omega
  have hr : 1 ≤ r n := Nat.one_le_two_pow
  have c1 := mt_rsa_preCost_le (preCfgA V₀ hd n w W hd0 rest k) hd w (preDA n W hd0 (k + 1))
    a1 a2 a3 a4 a5 a6 a7 a8 a9 hw a10 a11 hY1 hr
  have c2 := mt_rsa_clr_load_le V₀ hd w (preDA n W hd0 k) (preRecsA n W hd0 (k + 1) ++ rest)
    b1 b2 b3 b4 b5 b6 hw b10 b11 hY1 hr
  have c3 : r n * Y ^ 2 ≤ r n * Y ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by norm_num))
  simp only [preCpA, preCfgA] at c1 ⊢
  omega

/-- The first loader step: `cp 0 ≤ (cleared registers of V₀) + 42 T + 1600000 r Y^4`. -/
theorem mt_rsa_cp_zero_le {K : ℕ} (h : Big n) (hd0 : 0 < d n) (w W : ℕ)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (hd : Fin 5 → Fin t₀) (rest : List (Fin (prime + K + 4)))
    {Y : ℕ} (hY : p n + 1 ≤ Y) (hw : w ≤ Y) (hW : W ≤ Y)
    (hV : ∀ x ∈ preClrA hd, (V₀.get x).length ≤ T n * w) :
    preCpA V₀ hd n w W hd0 rest 0 ≤ 28 * (T n * w) + 29 + 42 * T n + 1600000 * (r n * Y ^ 4) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := mt_rsa_preDA h hd0 W 0 hY hW
  have hY1 : 1 ≤ Y := by omega
  have hr : 1 ≤ r n := Nat.one_le_two_pow
  have c1 := mt_rsa_preCost_le V₀ hd w (preDA n W hd0 0) a1 a2 a3 a4 a5 a6 a7 a8 a9 hw a10 a11 hY1 hr
  have c2 : ((preClrA hd).map fun x => 2 * (V₀.get x).length + 2).sum ≤
      ((preClrA hd).map fun _ => 2 * (T n * w) + 2).sum :=
    List.sum_le_sum fun x hx => by have := hV x hx; omega
  have c3 : ((preClrA hd).map fun _ => 2 * (T n * w) + 2).sum = 14 * (2 * (T n * w) + 2) := by
    simp [preClrA]; ring
  simp only [preCpA] at c1 ⊢
  omega


/-- One step of the stage (loader, two interchanges, the lines, header exchanges) with the
interchange costs `c₁`, `c₂` left symbolic. -/
theorem mt_rsa_term_nat {Tm w s ti m L N c₁ c₂ b₁ b₂ e cp Y r : ℕ} (hst : s ≤ ti) (hms : m ≤ s)
    (hti : 1 ≤ ti) (hb₁ : b₁ ≤ swapT t₀ * (1 + 2 * N + 5 * Y))
    (hb₂ : b₂ ≤ swapT t₀ * (1 + 2 * N + 5 * Y)) (he : e ≤ 2 * Y + 2)
    (hcp : cp ≤ 62 * N + 1600200 * (r * Y ^ 4)) (hw : w ≤ Y) (hL : L ≤ Y) (hY : 1 ≤ Y)
    (hN : 1 ≤ N) :
    cp + rsaStepCost Tm t₀ w s ti m L N c₁ c₂ b₁ b₂ e + 3 ≤
      (Tm + 12 * swapT t₀ + 5) * c₁ + (Tm + 12 * swapT t₀ + 5) * c₂ +
        N * ((2 * m + 1) * (rmulCost Tm w + 13 * w + 17)) + 110 * (swapT t₀ * (N * Y)) +
        400 * (N * Y) + 4 * (Tm * (N * Y)) + 1600200 * (r * Y ^ 4) := by
  have hax := mt_rsa_axis_le Tm w s ti m L N hst hms hti
  unfold rsaStepCost rsaSwapCost
  generalize swapT t₀ = S at *
  have hNY : 1 ≤ N * Y := Nat.one_le_iff_ne_zero.2 (by positivity)
  have f1 : S * N ≤ S * (N * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hY)
  have f2 : S * Y ≤ S * (N * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hN)
  have f3 : S ≤ S * (N * Y) := Nat.le_mul_of_pos_right _ hNY
  have f4 : Tm ≤ Tm * (N * Y) := Nat.le_mul_of_pos_right _ hNY
  have f5 : N ≤ N * Y := Nat.le_mul_of_pos_right _ hY
  have f6 : Y ≤ N * Y := Nat.le_mul_of_pos_left _ hN
  have f7 : N * w ≤ N * Y := Nat.mul_le_mul_left _ hw
  have f8 : N * L ≤ N * Y := Nat.mul_le_mul_left _ hL
  have g1 : S * (1 + 2 * N + 5 * Y) = S + 2 * (S * N) + 5 * (S * Y) := by ring
  have g2 : N * ((2 * m + 1) * (rmulCost Tm w + 13 * w + 17) + 60 * w + 8 * L + 80) =
      N * ((2 * m + 1) * (rmulCost Tm w + 13 * w + 17)) + 60 * (N * w) + 8 * (N * L) + 80 * N := by
    ring
  omega


/-- `2 m + 1 ≤ 4 α √p` for the window `m = windowA p α` of `Ã`. -/
theorem mt_rsa_window_real (h : Big n) :
    (2 * (windowA (p n) (alpha n) : ℝ) + 1) ≤ 4 * ((p n : ℝ) ^ (1 / 2 : ℝ) * alpha n) := by
  have hα : (2 : ℝ) ≤ alpha n := by exact_mod_cast two_le_alpha h.1
  have hp := mt_one_le_p h
  have h1 : (Nat.sqrt (p n * alpha n ^ 2) : ℝ) ≤ Real.sqrt ((p n * alpha n ^ 2 : ℕ) : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have h2 : Real.sqrt ((p n * alpha n ^ 2 : ℕ) : ℝ) = (p n : ℝ) ^ (1 / 2 : ℝ) * alpha n := by
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _), Real.sqrt_eq_rpow]
  have h3 : (1 : ℝ) ≤ (p n : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hp (by norm_num)
  have h4 : (2 : ℝ) ≤ (p n : ℝ) ^ (1 / 2 : ℝ) * alpha n := by nlinarith
  unfold windowA
  push_cast
  linarith

/-- A natural number below `X + 1` is at most `⌈X⌉ + 1`. -/
theorem mt_rsa_ceil_le {c : ℕ} {X : ℝ} (h : (c : ℝ) ≤ X + 1) : c ≤ ⌈X⌉₊ + 1 := by
  have := Nat.le_ceil X
  exact_mod_cast (show (c : ℝ) ≤ (⌈X⌉₊ : ℝ) + 1 by linarith)


/-- The `ℕ` form of the stage bound: `d` steps of at most `2 Q ⌈X⌉ + G` each. -/
theorem mt_rsa_nat_le {K : ℕ} (Tm cw cW : ℕ) (h : Big n) (hd0 : 0 < d n) (w W : ℕ)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (hd : Fin 5 → Fin t₀) (rest : List (Fin (prime + K + 4)))
    (hw : 1 ≤ w) (hwc : w ≤ cw * p n) (hWc : W ≤ cW * p n)
    (hV : ∀ x ∈ preClrA hd, (V₀.get x).length ≤ T n * w) :
    rsaAllCost (K := K) Tm t₀ w (windowA (p n) (alpha n)) (d n) (t n) hd0
        (rsaPipeData n (preHsA n w hd0)) hd (preCpA V₀ hd n w W hd0 rest) (∏ i, t n i) ≤
      d n * ((∏ i, t n i) * ((2 * windowA (p n) (alpha n) + 1) * (rmulCost Tm w + 13 * w + 17)) +
          110 * (swapT t₀ * ((∏ i, t n i) * ((cw + cW + 2) * (p n + 1)))) +
          400 * ((∏ i, t n i) * ((cw + cW + 2) * (p n + 1))) +
          4 * (Tm * ((∏ i, t n i) * ((cw + cW + 2) * (p n + 1)))) +
          1600200 * (r n * ((cw + cW + 2) * (p n + 1)) ^ 4)) +
        d n * (2 * ((Tm + 12 * swapT t₀ + 5) *
          (⌈swapConst * (T n * (3 * w) : ℕ) * (ℓ n : ℝ) ^ Parameters.tau⌉₊ + 1))) +
        2 * d n + 4 := by
  set Y := (cw + cW + 2) * (p n + 1) with hYdef
  set N := ∏ i, t n i with hNdef
  set m := windowA (p n) (alpha n) with hm
  set Xn := ⌈swapConst * (T n * (3 * w) : ℕ) * (ℓ n : ℝ) ^ Parameters.tau⌉₊ + 1 with hXn
  set G := N * ((2 * m + 1) * (rmulCost Tm w + 13 * w + 17)) + 110 * (swapT t₀ * (N * Y)) +
    400 * (N * Y) + 4 * (Tm * (N * Y)) + 1600200 * (r n * Y ^ 4) with hG
  have hp1 : 1 ≤ p n := by have := h.thirteen_le_p; omega
  have hY1 : p n + 1 ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have hwY : w ≤ Y := hwc.trans (Nat.mul_le_mul (by omega) (by omega))
  have hWY : W ≤ Y := hWc.trans (Nat.mul_le_mul (by omega) (by omega))
  have hN : N = T n := mt_prod_t h
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_two_pow
  have hlY : ℓ n ≤ Y := (mt_ℓ_le_p h).trans (by omega)
  have hNY : 1 ≤ N * Y := Nat.one_le_iff_ne_zero.2 (by positivity)
  -- the first axis and the first loader step
  have h0 : preCpA V₀ hd n w W hd0 rest 0 +
      rsaAxisCost Tm w (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 0)).s
        (t n (rsaStepAx hd0 0)) m (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 0)).Lb
        (N / t n (rsaStepAx hd0 0)) ≤ G := by
    have c1 := mt_rsa_cp_zero_le h hd0 w W V₀ hd rest hY1 hwY hWY hV
    have c2 := mt_rsa_axis_le Tm w (s n (rsaStepAx hd0 0)) (t n (rsaStepAx hd0 0)) m
      (Nat.log 2 (t n (rsaStepAx hd0 0))) N (mt_s_lt_t h _).le (pre_windowA_le_s h _)
      (mt_t_pos n _)
    have hL : Nat.log 2 (t n (rsaStepAx hd0 0)) ≤ Y :=
      (IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n _).trans hlY
    have f1 : N * w ≤ N * Y := Nat.mul_le_mul_left _ hwY
    have f2 : N * Nat.log 2 (t n (rsaStepAx hd0 0)) ≤ N * Y := Nat.mul_le_mul_left _ hL
    have f3 : N ≤ N * Y := Nat.le_mul_of_pos_right _ (by omega)
    have g2 : N * ((2 * m + 1) * (rmulCost Tm w + 13 * w + 17) + 60 * w +
        8 * Nat.log 2 (t n (rsaStepAx hd0 0)) + 80) =
        N * ((2 * m + 1) * (rmulCost Tm w + 13 * w + 17)) + 60 * (N * w) +
          8 * (N * Nat.log 2 (t n (rsaStepAx hd0 0))) + 80 * N := by ring
    rw [← hN] at c1
    simp only [rsaPipeData]
    omega
  -- the other steps
  have hstep : ∀ j ∈ Finset.range (d n - 1),
      preCpA V₀ hd n w W hd0 rest (j + 1) +
        rsaStepCost Tm t₀ w (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 (j + 1))).s
          (t n (rsaStepAx hd0 (j + 1))) m
          (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 (j + 1))).Lb N
          (BinaryInterchangeRun.cost (rsaPre (t n) (rsaStepAx hd0 (j + 1)))
            (rsaMid (t n) (rsaStepAx hd0 (j + 1))) (3 * w)
            (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 (j + 1))).Lb
            (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 0)).Lb
            (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 (j + 1))).hs)
          (BinaryInterchangeRun.cost (rsaPre (t n) (rsaStepAx hd0 (j + 1)))
            (rsaMid (t n) (rsaStepAx hd0 (j + 1))) (3 * w)
            (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 0)).Lb
            (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 (j + 1))).Lb
            (fun k => (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 (j + 1))).hs
              (Equiv.swap 3 4 k)))
          (∑ i, (rsaBank hd (rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 (j + 1))).hs i :
            List (Fin (prime + K + 4))).length)
          (∑ i, (rsaBank hd (fun k => (rsaPipeData n (preHsA n w hd0)
            (rsaStepAx hd0 (j + 1))).hs (Equiv.swap 3 4 k)) i :
            List (Fin (prime + K + 4))).length)
          (((rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 (j + 1))).hs 3).length +
            ((rsaPipeData n (preHsA n w hd0) (rsaStepAx hd0 (j + 1))).hs 4).length + 2) + 3 ≤
        2 * ((Tm + 12 * swapT t₀ + 5) * Xn) + G := by
    intro j hj
    have hj' : j + 1 < d n := by simp at hj; omega
    set ax := rsaStepAx hd0 (j + 1) with hax_def
    set a0 := rsaStepAx hd0 0 with ha0_def
    have hax : (ax : ℕ) + 1 < d n := by simp only [hax_def, rsaStepAx]; omega
    have ha0 : a0 = ⟨d n - 1, by omega⟩ := Fin.ext (by simp [ha0_def, rsaStepAx])
    have hsx : s n ax ≤ t n ax := (mt_s_lt_t h ax).le
    have hmx : m ≤ s n ax := pre_windowA_le_s h ax
    have htx : 1 ≤ t n ax := mt_t_pos n ax
    have ht : ∀ i, 1 ≤ t n i := fun i => mt_t_pos n i
    have hLb : Nat.log 2 (t n ax) ≤ ℓ n := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n ax
    have hLd : Nat.log 2 (t n a0) ≤ ℓ n := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n a0
    have hLd' : Nat.log 2 (t n a0) = ℓ n := pre_log_last h hd0
    have hLb' : ℓ n ≤ Nat.log 2 (t n ax) + 1 := by
      rcases pre_log_t (n := n) ax with e | e <;> omega
    have hPx : rsaPre (t n) ax ≤ N := mt_rsa_pre_le _ ht _
    have hGx : rsaMid (t n) ax ≤ N := mt_rsa_mid_le _ ht _
    have hsum : ∑ k, (preHsA n w hd0 ax k).length ≤ 2 * N + 5 * Y := by
      have := mt_rsa_hsSum_le (rsaPre (t n) ax) (rsaMid (t n) ax) (3 * w) (Nat.log 2 (t n ax))
        (Nat.log 2 (t n a0))
      refine le_trans this ?_
      omega
    have hsum' : ∑ k, (preHsA n w hd0 ax (Equiv.swap 3 4 k)).length =
        ∑ k, (preHsA n w hd0 ax k).length :=
      Equiv.sum_comp (Equiv.swap 3 4) (fun k => (preHsA n w hd0 ax k).length)
    have hb₁ := (mt_rsa_bankSum_le (A := prime + K) hd (preHsA n w hd0 ax)).trans
      (Nat.mul_le_mul_left (swapT t₀) (show 1 + ∑ k, (preHsA n w hd0 ax k).length ≤
        1 + 2 * N + 5 * Y by omega))
    have hb₂ := (mt_rsa_bankSum_le (A := prime + K) hd
      (fun k => preHsA n w hd0 ax (Equiv.swap 3 4 k))).trans
      (Nat.mul_le_mul_left (swapT t₀) (show 1 + ∑ k, (preHsA n w hd0 ax (Equiv.swap 3 4 k)).length ≤
        1 + 2 * N + 5 * Y by omega))
    have he : (preHsA n w hd0 ax 3).length + (preHsA n w hd0 ax 4).length + 2 ≤ 2 * Y + 2 := by
      have e3 : (preHsA n w hd0 ax 3).length ≤ Nat.log 2 (t n ax) := mt_length_sxBits_le _
      have e4 : (preHsA n w hd0 ax 4).length ≤ Nat.log 2 (t n a0) := mt_length_sxBits_le _
      omega
    have hcp := mt_rsa_cp_succ_le h hd0 w W V₀ hd rest hY1 hwY hWY j
    rw [← hN] at hcp
    have h12 : 2 ^ Nat.log 2 (t n ax) * 2 ^ Nat.log 2 (t n a0) =
        t n ax * t n ⟨d n - 1, by omega⟩ := by
      rw [← IntegerMultBounds.MathlibTM2.Mult.Pipeline.t_pow_log, ← IntegerMultBounds.MathlibTM2.Mult.Pipeline.t_pow_log, ha0]
    have hc₁ := mt_rsa_ceil_le (mt_rsa_swap_le h hw ax hax (preHsA n w hd0 ax) h12 hLb hLd
      (by omega) (by omega) (fun k => value_sxBits _) (fun k => canonical_sxBits _))
    have hc₂ := mt_rsa_ceil_le (mt_rsa_swap_le h hw ax hax
      (fun k => preHsA n w hd0 ax (Equiv.swap 3 4 k)) (by rw [mul_comm, h12]) hLd hLb
      (by omega) (by omega)
      (fun k => by simp only [preHsA]; rw [value_sxBits, rsa_values_swap34])
      (fun k => canonical_sxBits _))
    have hterm := mt_rsa_term_nat (t₀ := t₀) (Tm := Tm) (c₁ :=
        BinaryInterchangeRun.cost (rsaPre (t n) ax) (rsaMid (t n) ax) (3 * w)
          (Nat.log 2 (t n ax)) (Nat.log 2 (t n a0)) (preHsA n w hd0 ax))
      (c₂ := BinaryInterchangeRun.cost (rsaPre (t n) ax) (rsaMid (t n) ax) (3 * w)
          (Nat.log 2 (t n a0)) (Nat.log 2 (t n ax)) (fun k => preHsA n w hd0 ax (Equiv.swap 3 4 k)))
      hsx hmx htx hb₁ hb₂ he hcp hwY (hLb.trans hlY) (by omega) hN1
    have q1 := Nat.mul_le_mul_left (Tm + 12 * swapT t₀ + 5) hc₁
    have q2 := Nat.mul_le_mul_left (Tm + 12 * swapT t₀ + 5) hc₂
    rw [← hXn] at q1 q2
    simp only [rsaPipeData]
    omega
  calc rsaAllCost (K := K) Tm t₀ w m (d n) (t n) hd0 (rsaPipeData n (preHsA n w hd0)) hd
        (preCpA V₀ hd n w W hd0 rest) N ≤
      G + (∑ _j ∈ Finset.range (d n - 1), (2 * ((Tm + 12 * swapT t₀ + 5) * Xn) + G) +
        2 * (d n - 1) + 4) := by
        unfold rsaAllCost
        exact Nat.add_le_add h0 (Nat.add_le_add_right (Nat.add_le_add_right
          (Finset.sum_le_sum hstep) _) _)
    _ ≤ d n * G + d n * (2 * ((Tm + 12 * swapT t₀ + 5) * Xn)) + 2 * d n + 4 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        obtain ⟨e, he⟩ : ∃ e, d n = e + 1 := ⟨d n - 1, by omega⟩
        rw [he, Nat.add_sub_cancel]
        nlinarith


end Pipeline

/-! ### The real arithmetic of the assembly, over abstract reals -/

theorem mt_rsa_linA {R w cw p M CM : ℝ} (hR : R ≤ CM * M) (hw : w ≤ cw * p) (hpM : p ≤ M)
    (hM : 1 ≤ M) (hcw : 0 ≤ cw) : R + 13 * w + 17 ≤ (CM + 13 * cw + 17) * M := by
  have : cw * p ≤ cw * M := mul_le_mul_of_nonneg_left hpM hcw
  nlinarith

theorem mt_rsa_P1 {D T a b u K M : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T) (ha0 : 0 ≤ a) (ha : a ≤ 4 * u)
    (hb0 : 0 ≤ b) (hb : b ≤ K * M) :
    D * (T * (a * b)) ≤ 4 * K * (D * (T * u * M)) := by
  have h1 : a * b ≤ (4 * u) * (K * M) := mul_le_mul ha hb hb0 (by linarith)
  have h2 : T * (a * b) ≤ T * ((4 * u) * (K * M)) := mul_le_mul_of_nonneg_left h1 hT
  have h3 := mul_le_mul_of_nonneg_left h2 hD
  have e : D * (T * ((4 * u) * (K * M))) = 4 * K * (D * (T * u * M)) := by ring
  linarith

theorem mt_rsa_P2 {D T Y CY p Res : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T) (hY : Y ≤ 2 * CY * p)
    (hdTp : D * (T * p) ≤ Res) (hCY : 0 ≤ CY) : D * (T * Y) ≤ 2 * CY * Res := by
  have h1 : T * Y ≤ T * (2 * CY * p) := mul_le_mul_of_nonneg_left hY hT
  have h2 := mul_le_mul_of_nonneg_left h1 hD
  have h3 := mul_le_mul_of_nonneg_left hdTp (by linarith : 0 ≤ 2 * CY)
  have e : D * (T * (2 * CY * p)) = 2 * CY * (D * (T * p)) := by ring
  linarith

theorem mt_rsa_dTp {D T p M Res : ℝ} (h : D * T * M ≤ Res) (hp : p ≤ M) (hD : 0 ≤ D)
    (hT : 0 ≤ T) : D * (T * p) ≤ Res := by
  have : D * (T * p) ≤ D * (T * M) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hT) hD
  have e : D * (T * M) = D * T * M := by ring
  linarith

theorem mt_rsa_dres {D T M Res : ℝ} (h : D * T * M ≤ Res) (hT : 1 ≤ T) (hM : 1 ≤ M)
    (hD : 0 ≤ D) : D ≤ Res := by
  have h1 : 1 ≤ T * M := by nlinarith
  have h2 : D * 1 ≤ D * (T * M) := mul_le_mul_of_nonneg_left h1 hD
  have e : D * (T * M) = D * T * M := by ring
  linarith

theorem mt_rsa_Xb {X sw T w cw p τl : ℝ} (hX : X = sw * (T * (3 * w)) * τl) (hsw : 0 ≤ sw)
    (hτ : 0 ≤ τl) (hT : 0 ≤ T) (hw : w ≤ cw * p) : X ≤ 3 * sw * cw * (T * p * τl) := by
  have h1 : T * (3 * w) ≤ 3 * cw * (T * p) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hsw) hτ
  rw [hX]
  calc sw * (T * (3 * w)) * τl ≤ sw * (3 * cw * (T * p)) * τl := h2
    _ = 3 * sw * cw * (T * p * τl) := by ring

theorem mt_rsa_dCRT {D T p τl Crt : ℝ} (hD : 1 ≤ D) (hcrt : Crt = T * p * D ^ 2 + T * p * D ^ 2 * τl)
    (hTp : 0 ≤ T * p) (hτ : 0 ≤ τl) : D * (T * p * τl) ≤ Crt := by
  have h1 : D ≤ D ^ 2 := by nlinarith
  have h2 : 0 ≤ T * p * τl := mul_nonneg hTp hτ
  have h3 : D * (T * p * τl) ≤ D ^ 2 * (T * p * τl) := mul_le_mul_of_nonneg_right h1 h2
  have h4 : 0 ≤ T * p * D ^ 2 := mul_nonneg hTp (sq_nonneg D)
  rw [hcrt]
  nlinarith

theorem mt_rsa_P4 {D Q Xc X sw cw Z Crt Res : ℝ} (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hXc : Xc ≤ X + 1)
    (hX : X ≤ 3 * sw * cw * Z) (hc : 0 ≤ 6 * Q * sw * cw) (hZ : D * Z ≤ Crt) (hres : D ≤ Res) :
    D * (2 * (Q * (Xc + 1))) ≤ 6 * Q * sw * cw * Crt + 4 * Q * Res := by
  have h1 : Xc + 1 ≤ 3 * sw * cw * Z + 2 := by linarith
  have h2 : D * (2 * (Q * (Xc + 1))) ≤ D * (2 * (Q * (3 * sw * cw * Z + 2))) := by
    have := mul_le_mul_of_nonneg_left h1 hQ
    nlinarith
  have h3 : D * (2 * (Q * (3 * sw * cw * Z + 2))) = 6 * Q * sw * cw * (D * Z) + 4 * Q * D := by
    ring
  have h4 := mul_le_mul_of_nonneg_left hZ hc
  have h5 := mul_le_mul_of_nonneg_left hres (by linarith : 0 ≤ 4 * Q)
  linarith

theorem mt_rsa_final {cost D A L Y4 V Res Crt Tp Tt Q sw cw K1 CY c3 : ℝ}
    (hR : cost ≤ A + c3 * L + 1600200 * Y4 + V + 2 * D + 4)
    (hA : A ≤ 4 * K1 * Res) (hL : L ≤ 2 * CY * Res) (hc3 : 0 ≤ c3) (hY4 : 1600200 * Y4 ≤ Tt)
    (hTt : Tt ≤ Tp) (hV : V ≤ 6 * Q * sw * cw * Crt + 4 * Q * Res) (hD : D ≤ Res)
    (hRes : 0 ≤ Res) (hCrt : 0 ≤ Crt) (hTp : 0 ≤ Tp) (hQ : 0 ≤ Q) (hK1 : 0 ≤ K1) (hCY : 0 ≤ CY)
    (hc : 0 ≤ 6 * Q * sw * cw) (hD1 : 1 ≤ D) :
    cost ≤ (6 * Q * sw * cw + 4 * Q + 4 * K1 + 2 * CY * c3 + 8) * (Res + Crt + Tp) := by
  have hL' := mul_le_mul_of_nonneg_left hL hc3
  have r1 : 0 ≤ (6 * Q * sw * cw + 2) * Res := mul_nonneg (by linarith) hRes
  have r2 : 0 ≤ (4 * Q + 4 * K1 + 2 * CY * c3 + 8) * Crt :=
    mul_nonneg (by nlinarith) hCrt
  have r3 : 0 ≤ (6 * Q * sw * cw + 4 * Q + 4 * K1 + 2 * CY * c3 + 7) * Tp :=
    mul_nonneg (by nlinarith) hTp
  have e : (6 * Q * sw * cw + 4 * Q + 4 * K1 + 2 * CY * c3 + 8) * (Res + Crt + Tp) =
      (4 * K1 + c3 * (2 * CY) + 4 * Q + 6) * Res + 6 * Q * sw * cw * Crt + Tp +
        ((6 * Q * sw * cw + 2) * Res + (4 * Q + 4 * K1 + 2 * CY * c3 + 8) * Crt +
          (6 * Q * sw * cw + 4 * Q + 4 * K1 + 2 * CY * c3 + 7) * Tp) := by ring
  have e2 : c3 * (2 * CY * Res) = c3 * (2 * CY) * Res := by ring
  rw [e]
  linarith

/-! ### The stage -/

/-- **The `Ã` stage with its loader against `totBound`.** On a host of `Tm` stacks, with the
interchange bank of `t₀` header registers, coefficient width `1 ≤ w ≤ cw p`, table word size
`W ≤ cW p`, and the registers cleared by the first loader step of length at most `T w`, the
step bound of `rsaStage_exec` is eventually at most `C (totResamp + totCRT + T p)` with
`C = 6 Q swapConst cw + 4 Q + 4 K₁ + 2 (cw + cW + 2)(110 swapT t₀ + 400 + 4 Tm) + 8`,
`Q = Tm + 12 swapT t₀ + 5`, `K₁ = mtCM Tm cw + 13 cw + 17`: the line work
`d T (2m + 1) rmulCost` is `O(totResamp)`, the `2 (d - 1)` interchanges with the last axis are
`O(d T w ℓ^τ) = O(totCRT)`, the loader is `O(d T)` (unary `P`, `G`) plus `O(d r B^4) = o(T)`
for the tables, and the first loader step clears at most `14 (2 T w + 2)` symbols. -/
theorem mt_rsa_stage_le_route (route : ℕ → ℝ)
    (hroute : ∀ n, Big n → totDirectCRT n ≤ route n) (Tm t₀ K cw cW : ℕ) : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n)
    (w W : ℕ) (V₀ : RsaV (RsaX t₀) (prime + K)) (hd : Fin 5 → Fin t₀)
    (rest : List (Fin (prime + K + 4))),
    1 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
    (∀ x ∈ preClrA hd, (V₀.get x).length ≤ T n * w) →
    (rsaAllCost (K := K) Tm t₀ w (windowA (p n) (alpha n)) (d n) (t n) hd0
        (rsaPipeData n (preHsA n w hd0)) hd (preCpA V₀ hd n w W hd0 rest) (∏ i, t n i) : ℝ) ≤
      C * (totResamp n + route n + T n * p n) := by
  set S := swapT t₀ with hS
  set CY := cw + cW + 2 with hCY
  set Q : ℝ := (Tm : ℝ) + 12 * S + 5 with hQ
  set K1 : ℝ := mtCM Tm cw + 13 * cw + 17 with hK1
  refine ⟨6 * Q * swapConst * cw + 4 * Q + 4 * K1 + 2 * CY * (110 * S + 400 + 4 * Tm) + 8, ?_⟩
  filter_upwards [eventually_big, mt_poly_r_le_T (1600200 * (7 * CY) ^ 4) 5] with n h hsmall
  intro hd0 w W V₀ hd rest hw hwc hWc hV
  have hnat := mt_rsa_nat_le Tm cw cW h hd0 w W V₀ hd rest hw hwc hWc hV
  rw [mt_prod_t h] at hnat ⊢
  set X : ℝ := swapConst * (T n * (3 * w) : ℕ) * (ℓ n : ℝ) ^ Parameters.tau with hX
  have hX0 : 0 ≤ X := by
    have := mt_swapConst_nonneg
    have := Real.rpow_nonneg (Nat.cast_nonneg (ℓ n)) Parameters.tau
    positivity
  have hXc : (⌈X⌉₊ : ℝ) ≤ X + 1 := (Nat.ceil_lt_add_one hX0).le
  generalize ⌈X⌉₊ = Xc at hnat hXc
  set m := windowA (p n) (alpha n) with hm
  set R := rmulCost Tm w with hRdef
  set Y := CY * (p n + 1) with hY
  -- the small part
  have hb1 : 1 ≤ b n := by have := h.sixteen_le_b; omega
  have hYb : Y ≤ 7 * CY * b n := by
    rw [hY]
    have : p n + 1 ≤ 7 * b n := by unfold p; omega
    calc CY * (p n + 1) ≤ CY * (7 * b n) := Nat.mul_le_mul_left _ this
      _ = 7 * CY * b n := by ring
  have hsm : 1600200 * (d n * (r n * Y ^ 4)) ≤ T n := by
    have h1 : Y ^ 4 ≤ (7 * CY * b n) ^ 4 := Nat.pow_le_pow_left hYb 4
    have h2 : d n * (r n * Y ^ 4) ≤ b n * (r n * (7 * CY * b n) ^ 4) :=
      Nat.mul_le_mul (mt_d_le_b n) (Nat.mul_le_mul_left _ h1)
    have e : b n * (r n * (7 * CY * b n) ^ 4) = (7 * CY) ^ 4 * b n ^ 5 * r n := by ring
    calc 1600200 * (d n * (r n * Y ^ 4)) ≤ 1600200 * ((7 * CY) ^ 4 * b n ^ 5 * r n) := by
          rw [← e]; exact Nat.mul_le_mul_left _ h2
      _ = 1600200 * (7 * CY) ^ 4 * b n ^ 5 * r n := by ring
      _ ≤ T n := hsmall
  have hsm' : (1600200 : ℝ) * (d n * (r n * (Y : ℝ) ^ 4)) ≤ T n := by exact_mod_cast hsm
  rw [← hS] at hnat
  clear_value S
  have hR := (Nat.cast_le (α := ℝ)).2 hnat
  push_cast at hR
  generalize ((rsaAllCost (K := K) Tm t₀ w m (d n) (t n) hd0 (rsaPipeData n (preHsA n w hd0))
      hd (preCpA V₀ hd n w W hd0 rest) (T n) : ℕ) : ℝ) = cost at hR ⊢
  clear hnat hsmall hsm hV hYb
  have hp1 := mt_one_le_p h
  have hT1 := mt_one_le_T n
  have hMp1 := mt_one_le_mp h
  have hpM := mt_p_le_mp h
  have hT0 : (0 : ℝ) ≤ T n := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ p n := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ d n := Nat.cast_nonneg _
  have hd1 : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hcw0 : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hsw0 := mt_swapConst_nonneg
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hTm0 : (0 : ℝ) ≤ Tm := Nat.cast_nonneg _
  have hCY0 : (0 : ℝ) ≤ CY := Nat.cast_nonneg _
  have hQ0 : 0 ≤ Q := by rw [hQ]; linarith
  have hCM0 := mt_CM_nonneg Tm cw
  have hK10 : 0 ≤ K1 := by rw [hK1]; linarith
  have hτ : (0 : ℝ) ≤ (ℓ n : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hm0 : (0 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hRw0 : (0 : ℝ) ≤ (R : ℝ) + 13 * w + 17 := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ w := Nat.cast_nonneg _
    linarith
  set u : ℝ := (p n : ℝ) ^ (1 / 2 : ℝ) * alpha n with hu
  have hwin : (2 * (m : ℝ) + 1) ≤ 4 * u := mt_rsa_window_real h
  have hRm : (R : ℝ) ≤ mtCM Tm cw * totMp n := mt_rmul_le Tm h hw hwc
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hA : (R : ℝ) + 13 * w + 17 ≤ K1 * totMp n := by
    rw [hK1]; exact mt_rsa_linA hRm hw' hpM hMp1 hcw0
  have hres : totResamp n = d n * (T n * u * totMp n) := by rw [totResamp, hu]; ring
  have hMp0 : 0 ≤ totMp n := tot_mp_nonneg n
  have hres0 : 0 ≤ totResamp n := mt_resamp_nonneg n
  have hcrt0 : 0 ≤ route n := (mt_directCRT_nonneg n).trans (hroute n h)
  have hTp0 : 0 ≤ (T n : ℝ) * p n := mt_Tp_nonneg n
  have P1 : (d n : ℝ) * (T n * ((2 * m + 1) * (R + 13 * w + 17))) ≤ 4 * K1 * totResamp n := by
    rw [hres]; exact mt_rsa_P1 hD0 hT0 hm0 hwin hRw0 hA
  have hdTMp := mt_dTmp_le_resamp h
  have hdTp : (d n : ℝ) * (T n * p n) ≤ totResamp n := mt_rsa_dTp hdTMp hpM hD0 hT0
  have hYr : (Y : ℝ) ≤ 2 * CY * p n := by
    rw [hY]; push_cast
    have : (p n : ℝ) + 1 ≤ 2 * p n := by linarith
    have := mul_le_mul_of_nonneg_left this hCY0
    linarith
  have P2 : (d n : ℝ) * (T n * Y) ≤ 2 * CY * totResamp n := mt_rsa_P2 hD0 hT0 hYr hdTp hCY0
  have hXb : X ≤ 3 * swapConst * cw * (T n * p n * (ℓ n : ℝ) ^ Parameters.tau) :=
    mt_rsa_Xb (by rw [hX]; push_cast; ring) hsw0 hτ hT0 hw'
  have hdCRT : (d n : ℝ) * (T n * p n * (ℓ n : ℝ) ^ Parameters.tau) ≤ route n :=
    (mt_directCRT_swap_le n).trans (hroute n h)
  have hdres : (d n : ℝ) ≤ totResamp n := mt_rsa_dres hdTMp hT1 hMp1 hD0
  have hc : 0 ≤ 6 * Q * swapConst * cw := by
    have := mul_nonneg (mul_nonneg hQ0 hsw0) hcw0
    linarith
  have P4 : (d n : ℝ) * (2 * (Q * (Xc + 1))) ≤
      6 * Q * swapConst * cw * route n + 4 * Q * totResamp n :=
    mt_rsa_P4 hD0 hQ0 hXc hXb hc hdCRT hdres
  have hTTp : (T n : ℝ) ≤ T n * p n := by
    have := mul_le_mul_of_nonneg_left hp1 hT0
    linarith
  have hcoef : 0 ≤ 110 * (S : ℝ) + 400 + 4 * Tm := by linarith
  refine mt_rsa_final (L := (d n : ℝ) * (T n * Y)) (Y4 := d n * (r n * (Y : ℝ) ^ 4))
    (V := (d n : ℝ) * (2 * (Q * (Xc + 1)))) (D := d n) ?_ P1 P2 hcoef hsm' hTTp P4 hdres hres0
    hcrt0 hTp0 hQ0 hK10 hCY0 hc hd1
  calc cost ≤ _ := hR
    _ = _ := by rw [hQ]; ring

/-- Compatibility with the previous quadratic routing envelope. -/
theorem mt_rsa_stage_le (Tm t₀ K cw cW : ℕ) : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n)
    (w W : ℕ) (V₀ : RsaV (RsaX t₀) (prime + K)) (hd : Fin 5 → Fin t₀)
    (rest : List (Fin (prime + K + 4))),
    1 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
    (∀ x ∈ preClrA hd, (V₀.get x).length ≤ T n * w) →
    (rsaAllCost (K := K) Tm t₀ w (windowA (p n) (alpha n)) (d n) (t n) hd0
        (rsaPipeData n (preHsA n w hd0)) hd (preCpA V₀ hd n w W hd0 rest) (∏ i, t n i) : ℝ) ≤
      C * (totResamp n + totCRT n + T n * p n) :=
  mt_rsa_stage_le_route totCRT (fun _ h => mt_directCRT_le_old h) Tm t₀ K cw cW

/-- The existing resampling program uses only linearly many axis interchanges. -/
theorem mt_rsa_stage_le_linear (Tm t₀ K cw cW : ℕ) : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n)
    (w W : ℕ) (V₀ : RsaV (RsaX t₀) (prime + K)) (hd : Fin 5 → Fin t₀)
    (rest : List (Fin (prime + K + 4))),
    1 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
    (∀ x ∈ preClrA hd, (V₀.get x).length ≤ T n * w) →
    (rsaAllCost (K := K) Tm t₀ w (windowA (p n) (alpha n)) (d n) (t n) hd0
        (rsaPipeData n (preHsA n w hd0)) hd (preCpA V₀ hd n w W hd0 rest) (∏ i, t n i) : ℝ) ≤
      C * (totResamp n + totDirectCRT n + T n * p n) :=
  mt_rsa_stage_le_route totDirectCRT (fun _ _ => le_rfl) Tm t₀ K cw cW

end IntegerMultBounds.MathlibTM2.Cost
