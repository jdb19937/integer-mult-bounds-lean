module

public import IntegerMultBounds.MathlibTM2.Fast.DistSrc
public import IntegerMultBounds.MathlibTM2.Fast.DistCost

/-!
# The cost of the converter at the pipeline widths

`dsMainCost n = dsWidCost n + dsSrcCost n (dsW n) (dsWW n)`: the width program (two table
steps, `dsWidCost`) and the converter `dsSrc` (`Fast/DistSrc.lean`) at `w = dsW n`,
`Wt = dsWW n` (`Fast/DistWidth.lean`).

`ds_mainCost_le`: eventually `dsMainCost n ≤ 10^10 n + 10^10 (b n + 1)^5`.

With `B = b n + 1`, `W = pmW n ≤ 20 B`, `C = tblC W W ≤ 18600 B²`, the pieces are of three
kinds: unary pushes of values bounded by `T` (the record fields `t_i, s_i, P_i, G_i`, the chirp
streams, `r`), each tick `O(W)` steps, together `O(W T) = O(n)` (`pm_W_T_le`); tables and
searches of `r · poly(B)` steps (the CRT offsets `μ_j < s_j ≤ 2 r + 23`, the twist tables of `r`
entries, `B = r w` and `W_L = r w + …`), eventually below `T` (`ds_poly_r_le_T`, the local form
of `Cost/MatchBase.mt_poly_r_le_T`); and everything else, polynomial in `B` (`ds_main_bound`:
`dsMainCost n ≤ 10^4 (W T) + 10^10 (B³ r) + 10^10 B^5` under `Big n`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli IntegerMultBounds.MathlibTM2.Fast Filter

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- The step bound of the width program: `w = dsW n` by a code of at most `8` atoms and
`Wt = dsWW n` by a code of at most `40` atoms, each pushed in unary. -/
def dsWidCost (n : ℕ) : ℕ := dsStepCost (pmW n) 8 (dsW n) + dsStepCost (pmW n) 40 (dsWW n)

/-- The step bound of the whole distribution machine at the pipeline widths. -/
noncomputable def dsMainCost (n : ℕ) : ℕ := dsWidCost n + dsSrcCost n (dsW n) (dsWW n)

/-! ### A polynomial in `b` times `r` is eventually below `T` -/

section Poly

variable {n : ℕ}

theorem ds_T_split (h : Big n) :
    T n = 2 ^ (logT n - ℓ n) * r n ∧ b n ≤ 4 * (logT n - ℓ n) := by
  have hd := h.2
  have h1 := dℓ_lt h.one_le_d
  have h2 := h.logT_bounds
  have hdb : d n ≤ b n := d_le_b n
  have h16 : 16 * ℓ n ≤ d n * ℓ n := Nat.mul_le_mul_right _ hd
  have hl : ℓ n ≤ logT n := by omega
  refine ⟨?_, by omega⟩
  unfold T r
  rw [← pow_add, Nat.sub_add_cancel hl]

/-- **A polynomial in `b` times `r` is eventually below `T`.** -/
theorem ds_poly_r_le_T (A k : ℕ) : ∀ᶠ n in atTop, A * b n ^ k * r n ≤ T n := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (eventually_mul_pow_le_two_pow (A * 4 ^ k) k)
  filter_upwards [eventually_big, tendsto_b.eventually_ge_atTop (4 * M₀)] with n h hb
  obtain ⟨hT, hm⟩ := ds_T_split h
  set m := logT n - ℓ n
  have hmM : M₀ ≤ m := by omega
  have h1 : A * b n ^ k ≤ 2 ^ m :=
    calc A * b n ^ k ≤ A * (4 * m) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm k)
      _ = A * 4 ^ k * m ^ k := by rw [mul_pow]; ring
      _ ≤ 2 ^ m := hM₀ m hmM
  rw [hT]
  exact Nat.mul_le_mul_right _ h1

end Poly

/-! ### Bounds on the parameters -/

section Basic

variable {n : ℕ}

theorem ds_pmW_le (n : ℕ) : pmW n ≤ 20 * (b n + 1) := by
  have := pm_size_le (n := n); unfold pmW; omega

theorem ds_g_le (n : ℕ) : Chirp.chirpGuard (d n) ≤ 5 * (b n + 1) := by
  have := pm_g_le n; omega

theorem ds_gamma_le (hn : 2 ≤ n) : gamma n ≤ 34 * (b n + 1) ^ 3 := by
  have hα := pm_alpha_le hn
  have hd := d_le_b n
  have h1 : alpha n ^ 2 ≤ 16 * b n ^ 2 := by
    calc alpha n ^ 2 ≤ (4 * b n) ^ 2 := Nat.pow_le_pow_left hα 2
      _ = 16 * b n ^ 2 := by ring
  have h2 : b n ≤ b n + 1 := by omega
  have h3 : b n ^ 2 ≤ (b n + 1) ^ 2 := Nat.pow_le_pow_left h2 2
  unfold gamma
  calc d n * (2 * alpha n ^ 2 + 2) ≤ (b n + 1) * (2 * (16 * (b n + 1) ^ 2) + 2 * (b n + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (by nlinarith)
    _ = 34 * (b n + 1) ^ 3 := by ring

theorem ds_numHalf_le (hn : 2 ≤ n) : numHalf n ≤ 3 * (b n + 1) ^ 2 := by
  have hd := d_le_b n
  have hℓ := pm_ℓ_le hn
  unfold numHalf
  calc d n * ℓ n - logT n ≤ d n * ℓ n := Nat.sub_le _ _
    _ ≤ (b n + 1) * (3 * (b n + 1)) := Nat.mul_le_mul (by omega) (by omega)
    _ = 3 * (b n + 1) ^ 2 := by ring

theorem ds_topN_le (w : ℕ) : dsTopN w ≤ 4 * w + 1 := by
  unfold dsTopN
  rcases Nat.eq_zero_or_pos w with h | h
  · subst h; simp
  · have h1 : 1 ≤ 2 * w := by omega
    have hs : 1 ≤ Nat.size (2 * w) := Nat.size_pos.2 (by omega)
    have h2 : 2 ^ (Nat.size (2 * w) - 1) ≤ 2 * w := Nat.lt_size.1 (by omega)
    have e : 2 ^ Nat.size (2 * w) = 2 * 2 ^ (Nat.size (2 * w) - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem ds_topK_le (w : ℕ) : dsTopK w ≤ 6 * w + 7 := by
  unfold dsTopK
  have : Nat.size (2 * w) ≤ 2 * w := Nat.size_le.2 Nat.lt_two_pow_self
  omega

theorem ds_r_le_T (hn : 2 ≤ n) : r n ≤ T n := by
  have h1 := ds_d_mul_r_le hn
  have h2 := one_le_d hn
  calc r n ≤ d n * r n := Nat.le_mul_of_pos_left _ h2
    _ ≤ T n := h1

theorem ds_tblCw_le (hn : 2 ≤ n) : tblC (dsWW n) (dsW n) ≤ 1400000 * (b n + 1) ^ 2 := by
  have h1 := ds_dsWW_le hn
  have h2 := ds_dsW_le hn
  have hB : 1 ≤ b n + 1 := by omega
  unfold tblC
  have h3 : (dsWW n + 4) ^ 2 ≤ (204 * (b n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h4 : b n + 1 ≤ (b n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  nlinarith

end Basic

/-! ### Arithmetic over plain variables -/

section Arith

/-- A unary push of a value `x ≤ a B` at word size `W ≤ 20 B`. -/
theorem ds_un_le {W x B a : ℕ} (hB : 1 ≤ B) (hW : W ≤ 20 * B) (hx : x ≤ a * B) :
    W * (4 * x + 11) + 2 * x + 6 ≤ (82 * a + 228) * B ^ 2 := by
  have h1 : W * (4 * x + 11) ≤ 20 * B * (4 * (a * B) + 11) := Nat.mul_le_mul hW (by omega)
  have hB2 : B ≤ B ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : a * B ≤ a * B ^ 2 := Nat.mul_le_mul_left _ hB2
  nlinarith

/-- A unary push of a value `x ≤ a B³`. -/
theorem ds_un_le₃ {W x B a : ℕ} (hB : 1 ≤ B) (hW : W ≤ 20 * B) (hx : x ≤ a * B ^ 3) :
    W * (4 * x + 11) + 2 * x + 6 ≤ (82 * a + 228) * B ^ 4 := by
  have h1 : W * (4 * x + 11) ≤ 20 * B * (4 * (a * B ^ 3) + 11) := Nat.mul_le_mul hW (by omega)
  have hB2 : B ≤ B ^ 4 := Nat.le_self_pow (by norm_num) _
  have h3 : a * B ^ 3 ≤ a * B ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB (by norm_num))
  have e : 20 * B * (4 * (a * B ^ 3) + 11) = 80 * a * B ^ 4 + 220 * B := by ring
  nlinarith

/-- A unary push of `r` times a constant: `x ≤ a r`. -/
theorem ds_un_le_r {W x B a r : ℕ} (hB : 1 ≤ B) (hW : W ≤ 20 * B) (hx : x ≤ a * r) :
    W * (4 * x + 11) + 2 * x + 6 ≤ (82 * a) * (B ^ 3 * r) + 226 * B := by
  have h1 : W * (4 * x + 11) ≤ 20 * B * (4 * (a * r) + 11) := Nat.mul_le_mul hW (by omega)
  have hB3 : B ≤ B ^ 3 := Nat.le_self_pow (by norm_num) _
  have h3 : a * r ≤ a * (B ^ 3 * r) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by positivity))
  have h4 : B * (a * r) ≤ a * (B ^ 3 * r) := by
    calc B * (a * r) ≤ B ^ 3 * (a * r) := Nat.mul_le_mul_right _ hB3
      _ = a * (B ^ 3 * r) := by ring
  have e : 20 * B * (4 * (a * r) + 11) = 80 * (B * (a * r)) + 220 * B := by ring
  nlinarith

/-- A table step of `K` atoms pushing a value `x ≤ a B`. -/
theorem ds_stepCost_le {W K x B a : ℕ} (hB : 1 ≤ B) (hW : W ≤ 20 * B)
    (hC : tblC W W ≤ 18600 * B ^ 2) (hx : x ≤ a * B) :
    dsStepCost W K x ≤ ((K + 7) * 18600 + 82 * a + 228) * B ^ 2 := by
  unfold dsStepCost
  have h1 := ds_un_le hB hW hx
  have h2 : (K + 7) * tblC W W ≤ (K + 7) * (18600 * B ^ 2) := Nat.mul_le_mul_left _ hC
  nlinarith

/-- A table step of `K` atoms pushing a value `x ≤ a B²`. -/
theorem ds_stepCost_le₂ {W K x B a : ℕ} (hB : 1 ≤ B) (hW : W ≤ 20 * B)
    (hC : tblC W W ≤ 18600 * B ^ 2) (hx : x ≤ a * B ^ 2) :
    dsStepCost W K x ≤ ((K + 7) * 18600 + 82 * a + 228) * B ^ 3 := by
  unfold dsStepCost
  have h1 : W * (4 * x + 11) ≤ 20 * B * (4 * (a * B ^ 2) + 11) := Nat.mul_le_mul hW (by omega)
  have hB3 : B ≤ B ^ 3 := Nat.le_self_pow (by norm_num) _
  have hB23 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB (by norm_num)
  have h3 : a * B ^ 2 ≤ a * B ^ 3 := Nat.mul_le_mul_left _ hB23
  have h2 : (K + 7) * tblC W W ≤ (K + 7) * (18600 * B ^ 2) := Nat.mul_le_mul_left _ hC
  have h4 : (K + 7) * (18600 * B ^ 2) ≤ (K + 7) * (18600 * B ^ 3) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hB23)
  have e : 20 * B * (4 * (a * B ^ 2) + 11) = 80 * a * B ^ 3 + 220 * B := by ring
  nlinarith

/-- The atom count of the twist table over plain variables. -/
theorem ds_twist_aux {r p w B : ℕ} (hB : 1 ≤ B) (hp : p ≤ 6 * B) (hw : w ≤ 9 * B) :
    r * (39 * p + 626) + 200 * p + 4 * w + 1503 ≤ 860 * (B * r) + 2739 * B := by
  have h1 : r * (39 * p + 626) ≤ r * (860 * B) := Nat.mul_le_mul_left _ (by omega)
  have e : r * (860 * B) = 860 * (B * r) := by ring
  rw [e] at h1
  linarith

/-- The axis loop of phase 1 over plain variables. -/
theorem ds_ar_loop₁ {d W C r T Tr Wt B : ℕ} (hB : 1 ≤ B) (hd : d ≤ B) (hdr : d * r ≤ T)
    (hdTr : d * Tr ≤ T) (hW1 : W ≤ 20 * B) (hC : C ≤ 18600 * B ^ 2) (hWt : Wt ≤ 200 * B) :
    d * (28 * C + (4 * W + 2) * (11 * r + 95 + 4 * Tr + 2 * Wt + 63 * B ^ 2) +
      25 * (11 * W + 8) + 4) ≤ 15 * ((4 * W + 2) * T) + 50000 * B ^ 4 + 530000 * B ^ 3 := by
  obtain ⟨h2, h3, h4⟩ := ds_ar_pow B hB
  have e : d * (28 * C + (4 * W + 2) * (11 * r + 95 + 4 * Tr + 2 * Wt + 63 * B ^ 2) +
      25 * (11 * W + 8) + 4) = (4 * W + 2) * (11 * (d * r) + 4 * (d * Tr)) +
      d * ((4 * W + 2) * (95 + 2 * Wt + 63 * B ^ 2)) + d * (28 * C + 25 * (11 * W + 8) + 4) := by
    ring
  have p1 : (4 * W + 2) * (11 * (d * r) + 4 * (d * Tr)) ≤ (4 * W + 2) * (15 * T) :=
    Nat.mul_le_mul_left _ (by omega)
  have p2 : d * ((4 * W + 2) * (95 + 2 * Wt + 63 * B ^ 2)) ≤ 50000 * B ^ 4 := by
    have h1 : 4 * W + 2 ≤ 82 * B := by omega
    have h2 : 95 + 2 * Wt + 63 * B ^ 2 ≤ 558 * B ^ 2 := by omega
    calc d * ((4 * W + 2) * (95 + 2 * Wt + 63 * B ^ 2)) ≤ B * (82 * B * (558 * B ^ 2)) :=
          Nat.mul_le_mul hd (Nat.mul_le_mul h1 h2)
      _ = 45756 * B ^ 4 := by ring
      _ ≤ 50000 * B ^ 4 := by omega
  have p3 : d * (28 * C + 25 * (11 * W + 8) + 4) ≤ 530000 * B ^ 3 := by
    have h1 : 28 * C + 25 * (11 * W + 8) + 4 ≤ 530000 * B ^ 2 := by omega
    calc d * (28 * C + 25 * (11 * W + 8) + 4) ≤ B * (530000 * B ^ 2) := Nat.mul_le_mul hd h1
      _ = 530000 * B ^ 3 := by ring
  have e2 : (4 * W + 2) * (15 * T) = 15 * ((4 * W + 2) * T) := by ring
  omega

end Arith

/-! ### The phases -/

section Phases

variable {n : ℕ}

theorem ds_dsL_le (i : ℕ) : dsL n i ≤ ℓ n := by
  unfold dsL; split_ifs <;> omega

theorem ds_fa_le (v : Fin pmNV → ℕ) : (dsFA.map v).sum ≤ (dsVarsL.map v).sum := by
  rw [ds_vars_sum]; simp [dsFA]; omega

theorem ds_fb_le (v : Fin pmNV → ℕ) : (dsFB.map v).sum ≤ (dsVarsL.map v).sum := by
  rw [ds_vars_sum]; simp [dsFB]; omega

/-- The sum of the pushes of one iteration of phase 1. -/
theorem ds_vars_cost₁ (W : ℕ) (v : Fin pmNV → ℕ) :
    (dsVarsL₁.map fun x => W * (4 * v x + 11) + 2 * v x + 8).sum =
      (4 * W + 2) * ((dsVarsL.map v).sum + v 34 + v 35) + 25 * (11 * W + 8) := by
  rw [dsVarsL₁, List.map_append, List.sum_append, ds_vars_cost]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem ds_loopCost₁_le (hn : 2 ≤ n) (Wt : ℕ) :
    dsLoopCost₁ n Wt ≤ d n * (28 * tblC (pmW n) (pmW n) + (4 * pmW n + 2) *
      (11 * r n + 95 + 4 * (T n / r n) + 2 * Wt + 63 * (b n + 1) ^ 2) +
        25 * (11 * pmW n + 8) + 4) + 2 * d n + 4 := by
  unfold dsLoopCost₁
  have hℓ := pm_ℓ_le hn
  have hB : ℓ n ≤ 3 * (b n + 1) ^ 2 := by
    have : b n + 1 ≤ (b n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have h : ∑ i ∈ Finset.range (d n), (28 * tblC (pmW n) (pmW n) +
      ((dsVarsL₁.map fun x => pmW n * (4 * dsAV n Wt i x + 11) + 2 * dsAV n Wt i x + 8).sum + 1)
        + 3) ≤ ∑ _i ∈ Finset.range (d n), (28 * tblC (pmW n) (pmW n) + (4 * pmW n + 2) *
      (11 * r n + 95 + 4 * (T n / r n) + 2 * Wt + 63 * (b n + 1) ^ 2) +
        25 * (11 * pmW n + 8) + 4) := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [ds_vars_cost₁]
    have h34 : dsAV n Wt i 34 = dsL n i := by simp [dsAV, pmNV]
    have h35 : dsAV n Wt i 35 = dsS n i := by simp [dsAV, pmNV]
    rw [h34, h35]
    have h1 := ds_ax_vals hn (Finset.mem_range.1 hi) Wt
    have h2 := ds_dsL_le (n := n) i
    have h3 := dsS_le hn (Finset.mem_range.1 hi)
    have := Nat.mul_le_mul_left (4 * pmW n + 2)
      (show (dsVarsL.map (dsAV n Wt i)).sum + dsL n i + dsS n i ≤
        11 * r n + 95 + 4 * (T n / r n) + 2 * Wt + 63 * (b n + 1) ^ 2 by omega)
    omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  omega

theorem ds_recLenA_le (hn : 2 ≤ n) (Wt : ℕ) :
    dsRecLenA n Wt ≤ d n * (9 * r n + 80 + 4 * (T n / r n) + 2 * Wt + 60 * (b n + 1) ^ 2) := by
  unfold dsRecLenA
  have h : ∑ i ∈ Finset.range (d n), ((dsFA.map (dsAV n Wt i)).sum + 11) ≤
      ∑ _i ∈ Finset.range (d n), (9 * r n + 80 + 4 * (T n / r n) + 2 * Wt + 60 * (b n + 1) ^ 2) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 := ds_ax_vals hn (Finset.mem_range.1 hi) Wt
    have h2 := ds_fa_le (dsAV n Wt i)
    omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  exact h

theorem ds_recLenB_le (hn : 2 ≤ n) (Wt : ℕ) :
    dsRecLenB n Wt ≤ d n * (9 * r n + 80 + 4 * (T n / r n) + 2 * Wt + 60 * (b n + 1) ^ 2) := by
  unfold dsRecLenB
  have h : ∑ i ∈ Finset.range (d n), ((dsFB.map (dsAV n Wt i)).sum + 10) ≤
      ∑ _i ∈ Finset.range (d n), (9 * r n + 80 + 4 * (T n / r n) + 2 * Wt + 60 * (b n + 1) ^ 2) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 := ds_ax_vals hn (Finset.mem_range.1 hi) Wt
    have h2 := ds_fb_le (dsAV n Wt i)
    omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  exact h

/-- The record lengths: `O(T)` plus a polynomial. -/
theorem ds_recLen_le (hn : 2 ≤ n) {Wt : ℕ} (hWt : Wt ≤ 200 * (b n + 1)) :
    dsRecLenA n Wt ≤ 13 * T n + 540 * (b n + 1) ^ 3 ∧
      dsRecLenB n Wt ≤ 13 * T n + 540 * (b n + 1) ^ 3 := by
  have hA := ds_recLenA_le hn Wt
  have hB := ds_recLenB_le hn Wt
  have hdr := ds_d_mul_r_le hn
  have hTr : d n * (T n / r n) ≤ T n := by
    have := ds_d_mul_r_le hn
    have hr := ds_two_le_r hn
    calc d n * (T n / r n) ≤ d n * (T n / r n) + T n % r n := Nat.le_add_right _ _
      _ ≤ (T n / r n) * r n + T n % r n := by
          have : d n ≤ r n := ds_d_le_r hn
          have := Nat.mul_le_mul_right (T n / r n) this
          nlinarith
      _ = T n := Nat.div_add_mod' _ _
  have hd := d_le_b n
  have hB1 : 1 ≤ b n + 1 := by omega
  have h2 : b n + 1 ≤ (b n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : (b n + 1) ^ 2 ≤ (b n + 1) ^ 3 := Nat.pow_le_pow_right hB1 (by norm_num)
  have e : ∀ x, d n * (9 * r n + 80 + 4 * x + 2 * Wt + 60 * (b n + 1) ^ 2) =
      9 * (d n * r n) + 4 * (d n * x) + d n * (80 + 2 * Wt + 60 * (b n + 1) ^ 2) := fun x => by
    ring
  have hp : d n * (80 + 2 * Wt + 60 * (b n + 1) ^ 2) ≤ 540 * (b n + 1) ^ 3 := by
    have : 80 + 2 * Wt + 60 * (b n + 1) ^ 2 ≤ 540 * (b n + 1) ^ 2 := by omega
    calc d n * (80 + 2 * Wt + 60 * (b n + 1) ^ 2) ≤ (b n + 1) * (540 * (b n + 1) ^ 2) :=
          Nat.mul_le_mul (by omega) this
      _ = 540 * (b n + 1) ^ 3 := by ring
  rw [e] at hA hB
  omega

/-- The CRT loop: `d` iterations with the offset search of `O(r)` atoms. -/
theorem ds_crtCost_le (hn : 2 ≤ n) :
    dsCrtCost n ≤ d n * ((10 * r n + 152) * tblC (pmW n) (pmW n) + pmW n * (8 * r n + 103) +
      4 * r n + 58) + 2 * d n + 4 := by
  unfold dsCrtCost
  have h : ∑ i ∈ Finset.range (d n), ((dsCK₁ n + 17) * tblC (pmW n) (pmW n) +
      ((pmW n * (4 * dsMu n i + 11) + 2 * dsMu n i + 8) + 1) + 3) ≤
      ∑ _i ∈ Finset.range (d n), ((10 * r n + 152) * tblC (pmW n) (pmW n) +
        pmW n * (8 * r n + 103) + 4 * r n + 58) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 := dsMu_lt n i (Finset.mem_range.1 hi)
    have h2 := dsS_le hn (Finset.mem_range.1 hi)
    have h3 : pmW n * (4 * dsMu n i + 11) ≤ pmW n * (8 * r n + 103) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : dsCK₁ n + 17 = 10 * r n + 152 := by unfold dsCK₁; ring
    rw [e]
    omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  omega

end Phases

/-! ### The bound -/

section Main

variable {n : ℕ}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **The cost of the converter under `Big n`**, with the `r`-terms kept:
`dsMainCost n ≤ 10^4 (W T) + 10^10 (B³ r) + 10^10 B^5`, `W = pmW n`, `B = b n + 1`. -/
theorem ds_main_bound (hbig : Big n) :
    dsMainCost n ≤ 10 ^ 4 * (pmW n * T n) + 10 ^ 10 * ((b n + 1) ^ 3 * r n) +
      10 ^ 10 * (b n + 1) ^ 5 := by
  have hn := hbig.1
  have hB1 : 1 ≤ b n + 1 := by omega
  have hB2 : b n + 1 ≤ (b n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hB3 : (b n + 1) ^ 2 ≤ (b n + 1) ^ 3 := Nat.pow_le_pow_right hB1 (by norm_num)
  have hB4 : (b n + 1) ^ 3 ≤ (b n + 1) ^ 4 := Nat.pow_le_pow_right hB1 (by norm_num)
  have hB5 : (b n + 1) ^ 4 ≤ (b n + 1) ^ 5 := Nat.pow_le_pow_right hB1 (by norm_num)
  have hW : pmW n ≤ 20 * (b n + 1) := ds_pmW_le n
  have hW1 : 1 ≤ pmW n := by have := pmW_ge n; omega
  have hC : tblC (pmW n) (pmW n) ≤ 18600 * (b n + 1) ^ 2 := ds_tblC_le n
  have hw : dsW n ≤ 9 * (b n + 1) := by have := ds_dsW_le hn; omega
  have hWt : dsWW n ≤ 200 * (b n + 1) := ds_dsWW_le hn
  have hp : p n ≤ 6 * (b n + 1) := by unfold p; omega
  have hg : Chirp.chirpGuard (d n) ≤ 5 * (b n + 1) := ds_g_le n
  have hℓ : ℓ n ≤ 3 * (b n + 1) := by have := pm_ℓ_le hn; omega
  have hlogT : logT n ≤ 3 * (b n + 1) := by have := pm_logT_le hn; omega
  have hd : d n ≤ b n + 1 := by have := d_le_b n; omega
  have hK : K n ≤ b n + 1 := by have := K_le_d n; omega
  have hγ : gamma n ≤ 34 * (b n + 1) ^ 3 := ds_gamma_le hn
  have hnh : numHalf n ≤ 3 * (b n + 1) ^ 2 := ds_numHalf_le hn
  have hrT : r n ≤ T n := ds_r_le_T hn
  have hdr : d n * r n ≤ T n := ds_d_mul_r_le hn
  have hTr : T n / r n ≤ T n := Nat.div_le_self _ _
  have hT : T n ≤ pmW n * T n := Nat.le_mul_of_pos_left _ hW1
  have hdTr : d n * (T n / r n) ≤ T n := by
    have hr := ds_two_le_r hn
    calc d n * (T n / r n) ≤ d n * (T n / r n) + T n % r n := Nat.le_add_right _ _
      _ ≤ (T n / r n) * r n + T n % r n := by
          have : d n ≤ r n := ds_d_le_r hn
          have := Nat.mul_le_mul_right (T n / r n) this
          nlinarith
      _ = T n := Nat.div_add_mod' _ _
  have hr1 : r n ≤ (b n + 1) ^ 3 * r n := Nat.le_mul_of_pos_left _ (by positivity)
  have hBr : (b n + 1) * r n ≤ (b n + 1) ^ 3 * r n := Nat.mul_le_mul_right _ (by omega)
  have hB2r : (b n + 1) ^ 2 * r n ≤ (b n + 1) ^ 3 * r n := Nat.mul_le_mul_right _ hB3
  have hTw : tblC (dsWW n) (dsW n) ≤ 1400000 * (b n + 1) ^ 2 := ds_tblCw_le hn
  -- the width program
  have hWid : dsWidCost n ≤ 1300000 * (b n + 1) ^ 2 := by
    unfold dsWidCost
    have h1 := ds_stepCost_le (K := 8) hB1 hW hC hw
    have h2 := ds_stepCost_le (K := 40) hB1 hW hC hWt
    omega
  -- phase 1
  have hP1 : dsP1Cost n (dsWW n) ≤ 1200 * (pmW n * T n) + 2000000 * (b n + 1) ^ 4 := by
    unfold dsP1Cost
    have hl := ds_loopCost₁_le hn (dsWW n)
    have hl2 := ds_ar_loop₁ (T := T n) (Tr := T n / r n) hB1 hd hdr hdTr hW hC hWt
    have hrec := ds_recLen_le hn hWt
    have hst := ds_sum_t hn
    have hss := ds_sum_s hn
    have h1 : dsWW n * (4 * pmW n + 10) ≤ 200 * (b n + 1) * (4 * (20 * (b n + 1)) + 10) :=
      Nat.mul_le_mul hWt (by omega)
    have h2 : pmW n * (4 * d n + 11) ≤ 20 * (b n + 1) * (4 * (b n + 1) + 11) :=
      Nat.mul_le_mul hW (by omega)
    have e1 : 200 * (b n + 1) * (4 * (20 * (b n + 1)) + 10) =
        16000 * (b n + 1) ^ 2 + 2000 * (b n + 1) := by ring
    have e2 : 20 * (b n + 1) * (4 * (b n + 1) + 11) = 80 * (b n + 1) ^ 2 + 220 * (b n + 1) := by
      ring
    have e3 : 15 * ((4 * pmW n + 2) * T n) = 60 * (pmW n * T n) + 30 * T n := by ring
    omega
  -- phase C
  have hPC : dsPCCost n ≤ 200 * (pmW n * T n) + 3000000 * ((b n + 1) ^ 3 * r n) +
      4000000 * (b n + 1) ^ 3 := by
    unfold dsPCCost
    have hc := ds_crtCost_le hn
    have hcd : d n * ((10 * r n + 152) * tblC (pmW n) (pmW n) + pmW n * (8 * r n + 103) +
        4 * r n + 58) ≤
        10 * ((b n + 1) ^ 3 * r n) * 18600 + 152 * 18600 * (b n + 1) ^ 3 +
          160 * ((b n + 1) ^ 3 * r n) + 2060 * (b n + 1) ^ 3 +
          4 * ((b n + 1) ^ 3 * r n) + 58 * (b n + 1) := by
      have e : d n * ((10 * r n + 152) * tblC (pmW n) (pmW n) + pmW n * (8 * r n + 103) +
          4 * r n + 58) =
          10 * (d n * r n * tblC (pmW n) (pmW n)) + 152 * (d n * tblC (pmW n) (pmW n)) +
            8 * (d n * pmW n * r n) + 103 * (d n * pmW n) + 4 * (d n * r n) + 58 * d n := by ring
      have q1 : d n * r n * tblC (pmW n) (pmW n) ≤ (b n + 1) * r n * (18600 * (b n + 1) ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hd) hC
      have e1 : (b n + 1) * r n * (18600 * (b n + 1) ^ 2) = ((b n + 1) ^ 3 * r n) * 18600 := by
        ring
      have q2 : d n * tblC (pmW n) (pmW n) ≤ (b n + 1) * (18600 * (b n + 1) ^ 2) :=
        Nat.mul_le_mul hd hC
      have e2 : (b n + 1) * (18600 * (b n + 1) ^ 2) = 18600 * (b n + 1) ^ 3 := by ring
      have q3 : d n * pmW n * r n ≤ (b n + 1) * (20 * (b n + 1)) * r n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hd hW)
      have e3 : (b n + 1) * (20 * (b n + 1)) * r n = 20 * ((b n + 1) ^ 2 * r n) := by ring
      have q4 : d n * pmW n ≤ (b n + 1) * (20 * (b n + 1)) := Nat.mul_le_mul hd hW
      have e4 : (b n + 1) * (20 * (b n + 1)) = 20 * (b n + 1) ^ 2 := by ring
      have q5 : d n * r n ≤ (b n + 1) * r n := Nat.mul_le_mul_right _ hd
      rw [e]
      omega
    have h1 := ds_un_le (W := pmW n) (a := 3) hB1 hW hlogT
    have h2 : (14 * pmW n + 14) ≤ 294 * (b n + 1) := by omega
    omega
  -- phase 2a
  have hP2a : dsP2aCost n (dsW n) (dsWW n) ≤ 100 * ((b n + 1) ^ 3 * r n) +
      20000000 * (b n + 1) ^ 4 := by
    unfold dsP2aCost
    have hu : ((dsP2un (t₀ := 0)).map fun e =>
        pmW n * (4 * pmVal n e.1 + 11) + 2 * pmVal n e.1 + 6).sum ≤
        100 * ((b n + 1) ^ 3 * r n) + 100000 * (b n + 1) ^ 4 := by
      simp only [dsP2un, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [show pmVal n (2 : Fin pmNV).val = p n from rfl,
        show pmVal n (21 : Fin pmNV).val = Chirp.chirpGuard (d n) from rfl,
        show pmVal n (7 : Fin pmNV).val = ℓ n from rfl,
        show pmVal n (14 : Fin pmNV).val = gamma n from rfl,
        show pmVal n (28 : Fin pmNV).val = p n + Chirp.chirpGuard (d n) from rfl,
        show pmVal n (8 : Fin pmNV).val = r n from rfl,
        show pmVal n (4 : Fin pmNV).val = K n from rfl]
      have a1 := ds_un_le (W := pmW n) (a := 6) hB1 hW hp
      have a2 := ds_un_le (W := pmW n) (a := 5) hB1 hW hg
      have a3 := ds_un_le (W := pmW n) (a := 3) hB1 hW hℓ
      have a4 := ds_un_le₃ (W := pmW n) (a := 34) hB1 hW hγ
      have a5 := ds_un_le (W := pmW n) (a := 11) hB1 hW
        (show p n + Chirp.chirpGuard (d n) ≤ 11 * (b n + 1) by omega)
      have a6 := ds_un_le_r (W := pmW n) (a := 1) (B := b n + 1) hB1 hW
        (show r n ≤ 1 * r n by omega)
      have a7 := ds_un_le (W := pmW n) (a := 1) hB1 hW (show K n ≤ 1 * (b n + 1) by omega)
      omega
    have s1 : dsW n * (4 * pmW n + 10) ≤ 9 * (b n + 1) * (4 * (20 * (b n + 1)) + 10) :=
      Nat.mul_le_mul hw (by omega)
    have e1 : 9 * (b n + 1) * (4 * (20 * (b n + 1)) + 10) =
        720 * (b n + 1) ^ 2 + 90 * (b n + 1) := by ring
    have s2 := ds_stepCost_le (K := 3) (a := 1) hB1 hW hC (show d n - 1 ≤ 1 * (b n + 1) by omega)
    have s3 := ds_stepCost_le (K := 1) (a := 3) hB1 hW hC
      (show logT n - ℓ n ≤ 3 * (b n + 1) by omega)
    have s4 := ds_stepCost_le (K := 1) (a := 9) hB1 hW hC
      (show dsW n - gamma n ≤ 9 * (b n + 1) by omega)
    have s5 := ds_stepCost_le (K := 2) (a := 9) hB1 hW hC
      (show dsW n - (logT n - ℓ n) ≤ 9 * (b n + 1) by omega)
    have s6 := ds_stepCost_le (K := 2) (a := 7) hB1 hW hC (show p n + 1 ≤ 7 * (b n + 1) by omega)
    have s7 := ds_stepCost_le (K := 3) (a := 13) hB1 hW hC
      (show p n + Chirp.chirpGuard (d n) + 2 ≤ 13 * (b n + 1) by omega)
    have htn := ds_topN_le (dsW n)
    have htk := ds_topK_le (dsW n)
    have s8 : dsStepCost (pmW n) (dsTopK (dsW n)) (dsTopN (dsW n)) ≤ 2000000 * (b n + 1) ^ 3 := by
      unfold dsStepCost
      have q1 : (dsTopK (dsW n) + 7) * tblC (pmW n) (pmW n) ≤
          (61 * (b n + 1) + 7) * (18600 * (b n + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) hC
      have e : (61 * (b n + 1) + 7) * (18600 * (b n + 1) ^ 2) =
          1134600 * (b n + 1) ^ 3 + 130200 * (b n + 1) ^ 2 := by ring
      have q2 := ds_un_le (W := pmW n) (a := 37) hB1 hW
        (show dsTopN (dsW n) ≤ 37 * (b n + 1) by omega)
      omega
    omega
  -- phase 2b
  have hP2b : dsP2bCost n (dsW n) ≤ 400 * ((b n + 1) ^ 3 * r n) + 10000000 * (b n + 1) ^ 4 := by
    unfold dsP2bCost
    have s1 := ds_stepCost_le (K := 4) (a := 9) hB1 hW hC
      (show dsW n - (p n + 2) ≤ 9 * (b n + 1) by omega)
    have s2 := ds_stepCost_le (K := 3) (a := 8) hB1 hW hC (show p n + 2 ≤ 8 * (b n + 1) by omega)
    have s3 : dsW n * (4 * r n + 7) ≤ 9 * (b n + 1) * (4 * r n + 7) := Nat.mul_le_mul_right _ hw
    have e3 : 9 * (b n + 1) * (4 * r n + 7) = 36 * ((b n + 1) * r n) + 63 * (b n + 1) := by ring
    have s4 : r n * dsW n ≤ r n * (9 * (b n + 1)) := Nat.mul_le_mul_left _ hw
    have e4 : r n * (9 * (b n + 1)) = 9 * ((b n + 1) * r n) := by ring
    have hN : (logT n - ℓ n) ^ 2 + (logT n - ℓ n) + 4 ≤ 16 * (b n + 1) ^ 2 := by
      have : (logT n - ℓ n) ^ 2 ≤ (3 * (b n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (3 * (b n + 1)) ^ 2 = 9 * (b n + 1) ^ 2 := by ring
      omega
    have s5 := ds_stepCost_le₂ (K := 7) (a := 16) hB1 hW hC hN
    have s6 : dsStepBCost (pmW n) (dsEK n) (dsWL n (dsW n)) ≤
        200 * ((b n + 1) ^ 3 * r n) + 800000 * (b n + 1) ^ 4 := by
      unfold dsStepBCost dsEK dsWL
      have q1 : (4 * (d n - 1) + 4 * numHalf n + 14 + 7) * tblC (pmW n) (pmW n) ≤
          (37 * (b n + 1) ^ 2) * (18600 * (b n + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) hC
      have e1 : (37 * (b n + 1) ^ 2) * (18600 * (b n + 1) ^ 2) = 688200 * (b n + 1) ^ 4 := by ring
      have q2 : r n * dsW n ≤ r n * (9 * (b n + 1)) := Nat.mul_le_mul_left _ hw
      omega
    omega
  -- phase 2c
  have hP2c : dsP2cCost n (dsW n) (dsWW n) ≤ 3000000000 * ((b n + 1) ^ 3 * r n) +
      9000000000 * (b n + 1) ^ 3 := by
    unfold dsP2cCost
    have ht : dsTwistCost (dsWW n) (dsW n) (p n) (r n) ≤
        1300000000 * ((b n + 1) ^ 3 * r n) + 4000000000 * (b n + 1) ^ 3 := by
      unfold dsTwistCost
      have q1 : p n * (4 * dsWW n + 10) ≤ 6 * (b n + 1) * (4 * (200 * (b n + 1)) + 10) :=
        Nat.mul_le_mul hp (by omega)
      have e1 : 6 * (b n + 1) * (4 * (200 * (b n + 1)) + 10) =
          4800 * (b n + 1) ^ 2 + 60 * (b n + 1) := by ring
      have q2 : r n * (4 * dsWW n + 10) ≤ r n * (810 * (b n + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      have e2 : r n * (810 * (b n + 1)) = 810 * ((b n + 1) * r n) := by ring
      have q3 : dsW n * (4 * dsWW n + 10) ≤ 9 * (b n + 1) * (4 * (200 * (b n + 1)) + 10) :=
        Nat.mul_le_mul hw (by omega)
      have e3 : 9 * (b n + 1) * (4 * (200 * (b n + 1)) + 10) =
          7200 * (b n + 1) ^ 2 + 90 * (b n + 1) := by ring
      have q4 : (r n * (39 * p n + 626) + 200 * p n + 4 * dsW n + 1503) * tblC (dsWW n) (dsW n) ≤
          (860 * ((b n + 1) * r n) + 2739 * (b n + 1)) * (1400000 * (b n + 1) ^ 2) := by
        exact Nat.mul_le_mul (ds_twist_aux hB1 hp hw) hTw
      have e4 : (860 * ((b n + 1) * r n) + 2739 * (b n + 1)) * (1400000 * (b n + 1) ^ 2) =
          1204000000 * ((b n + 1) ^ 3 * r n) + 3834600000 * (b n + 1) ^ 3 := by ring
      have q5 : r n * dsW n ≤ r n * (9 * (b n + 1)) := Nat.mul_le_mul_left _ hw
      have e5 : r n * (9 * (b n + 1)) = 9 * ((b n + 1) * r n) := by ring
      omega
    omega
  -- the total
  unfold dsMainCost dsSrcCost
  omega

/-- **The cost of the distribution machine at the pipeline widths**: eventually
`dsMainCost n ≤ 10^10 n + 10^10 (b n + 1)^5` (`C = 10^10`, `k = 5`). -/
theorem ds_mainCost_le : ∀ᶠ n in atTop, dsMainCost n ≤ 10 ^ 10 * n + 10 ^ 10 * (b n + 1) ^ 5 := by
  filter_upwards [eventually_big, ds_poly_r_le_T (10 ^ 11) 3] with n hbig hr
  have hn := hbig.1
  have h := ds_main_bound hbig
  have hWT := pm_W_T_le hn
  have hb := one_le_b hn
  have hB : (b n + 1) ^ 3 ≤ 8 * b n ^ 3 := by
    calc (b n + 1) ^ 3 ≤ (2 * b n) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * b n ^ 3 := by ring
  have hr' : 10 ^ 10 * ((b n + 1) ^ 3 * r n) ≤ T n := by
    calc 10 ^ 10 * ((b n + 1) ^ 3 * r n) ≤ 10 ^ 10 * (8 * b n ^ 3 * r n) :=
          Nat.mul_le_mul_left _ (by nlinarith)
      _ = 8 * 10 ^ 10 * b n ^ 3 * r n := by ring
      _ ≤ 10 ^ 11 * b n ^ 3 * r n := by
          have : 8 * 10 ^ 10 ≤ 10 ^ 11 := by norm_num
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
      _ ≤ T n := hr
  have hT : T n ≤ pmW n * T n := Nat.le_mul_of_pos_left _ (by have := pmW_ge n; omega)
  omega

end Main

end IntegerMultBounds.MathlibTM2.Fast.TableVM
