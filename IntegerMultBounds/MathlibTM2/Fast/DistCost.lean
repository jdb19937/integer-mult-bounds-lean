module

public import IntegerMultBounds.MathlibTM2.Fast.DistWidth

/-!
# The cost of the distribution machine

Bounds on the pieces of the step counts of the distribution machines (`Fast/Dist.lean`,
`Fast/DistSrc.lean`): the values pushed by the axis loop (`ds_ax_vals`), the sums of the axis
lengths (`ds_sum_t`, `ds_sum_s`), the table atom cost (`ds_tblC_le`), the axis loop
(`ds_loopCost_le`, `ds_ar_loop`).

The linear part is the unary output: the fields `t_i, s_i, P_i, G_i` of the records
(`Σ_i (t_i + s_i) ≤ 3 d r + 23 d`, `P_i, G_i ≤ T / r`, `d r ≤ T`, `d ≤ r`), the chirp streams,
`r`, `B = r w` and `W_L`, each tick at most `O(pmW n)` steps, with `pmW n · T ≤ 192 n`
(`pm_W_T_le`). Everything else is polynomial in `b`: `d ≤ b` iterations of the axis code
(`28` table atoms of `tblC (pmW n) (pmW n) = O(b²)` steps) and the single values.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli


section Cost

variable {n : ℕ}

theorem ds_vars_sum (v : Fin pmNV → ℕ) :
    (dsVarsL.map v).sum = 3 * v 33 + 3 * v 35 + 2 * v 32 + 2 * v 37 + v 36 + v 19 + v 20 +
      2 * v 34 + 2 * v 7 + 2 * v 12 + 2 * v 2 + 2 * v 38 := by
  simp only [dsVarsL, dsFA, dsFB, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem ds_map_affine {α : Type} (l : List α) (v : α → ℕ) (a c : ℕ) :
    (l.map fun x => a * v x + c).sum = a * (l.map v).sum + l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem ds_vars_cost (W : ℕ) (v : Fin pmNV → ℕ) :
    (dsVarsL.map fun x => W * (4 * v x + 11) + 2 * v x + 8).sum =
      (4 * W + 2) * (dsVarsL.map v).sum + 23 * (11 * W + 8) := by
  have e : (fun x => W * (4 * v x + 11) + 2 * v x + 8) =
      fun x => (4 * W + 2) * v x + (11 * W + 8) := by funext x; ring
  rw [e, ds_map_affine]
  simp only [dsVarsL, dsFA, dsFB, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.length_cons, List.length_nil]

/-- The values pushed in one iteration. -/
theorem ds_ax_vals (hn : 2 ≤ n) {i : ℕ} (hi : i < d n) (Wt : ℕ) :
    (dsVarsL.map (dsAV n Wt i)).sum ≤
      9 * r n + 69 + 4 * (T n / r n) + 2 * Wt + 60 * (b n + 1) ^ 2 := by
  rw [ds_vars_sum]
  simp only [dsAV, dsLV, pmNV, Fin.isValue]
  norm_num [pmVal]
  have ht := dsT_le hn i
  have hs := dsS_le hn hi
  have hP := dsP_le_Tr hn hi
  have hG := dsG_le_Tr hn i
  have hq : dsQ n i ≤ p n + 1 := by unfold dsQ; split_ifs <;> omega
  have hL : dsL n i ≤ ℓ n := by unfold dsL; split_ifs <;> omega
  have hℓ := pm_ℓ_le hn
  have hα := pm_alpha_le hn
  have hwA : Pipeline.windowA (p n) (alpha n) ≤ 24 * b n ^ 2 + 1 := by
    unfold Pipeline.windowA; have := pm_sqrt_le hn; omega
  have hwB : FastB0.fastWindow (p n) (alpha n) ≤ p n + 1 := by
    unfold FastB0.fastWindow
    have h1 := Nat.div_le_self (Nat.sqrt (p n)) (2 * alpha n)
    have h2 := Nat.sqrt_le_self (p n)
    omega
  have e : (b n + 1) ^ 2 = b n ^ 2 + 2 * b n + 1 := by ring
  unfold p at hq hwA hwB ⊢
  omega

/-- `Σ_{i < d} t_i ≤ T`. -/
theorem ds_sum_t (hn : 2 ≤ n) : (List.ofFn (t n)).sum ≤ T n := by
  rw [ds_ofFn_t]
  have h := List.sum_le_length_nsmul ((List.range (d n)).map (dsT n)) (r n) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact dsT_le hn i)
  simp only [List.length_map, List.length_range, smul_eq_mul] at h
  exact h.trans (ds_d_mul_r_le hn)

/-- `Σ_{i < d} s_i ≤ 2 T + 23 d`. -/
theorem ds_sum_s (hn : 2 ≤ n) : (List.ofFn (s n)).sum ≤ 2 * T n + 23 * d n := by
  rw [ds_ofFn_s]
  have h := List.sum_le_length_nsmul ((List.range (d n)).map (dsS n)) (2 * r n + 23) (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact dsS_le hn (List.mem_range.1 hi))
  simp only [List.length_map, List.length_range, smul_eq_mul] at h
  have := ds_d_mul_r_le hn
  nlinarith

theorem ds_tblC_le (n : ℕ) : tblC (pmW n) (pmW n) ≤ 2^16 * (b n + 1) ^ 2 := by
  have hs := pm_size_le (n := n)
  unfold tblC pmW
  norm_num only [Nat.reducePow]
  nlinarith

/-- The sharper distribution allowance applies to actual inputs of length at least two. -/
theorem ds_tblC_le_of_two {n : ℕ} (hn : 2≤n) :
    tblC (pmW n) (pmW n) ≤ 18600 * (b n + 1) ^ 2 := by
  have hs := pm_size_le (n := n)
  have hb := one_le_b hn
  unfold tblC pmW
  nlinarith

/-- The axis loop: the records cost `O(pmW · T)`, the rest is polynomial in `b`. -/
theorem ds_loopCost_le (hn : 2 ≤ n) (Wt : ℕ) :
    dsLoopCost n Wt ≤ d n * (28 * tblC (pmW n) (pmW n) + (4 * pmW n + 2) *
      (9 * r n + 69 + 4 * (T n / r n) + 2 * Wt + 60 * (b n + 1) ^ 2) +
        23 * (11 * pmW n + 8) + 4) + 2 * d n + 4 := by
  unfold dsLoopCost
  have h : ∑ i ∈ Finset.range (d n), (28 * tblC (pmW n) (pmW n) +
      ((dsVarsL.map fun x => pmW n * (4 * dsAV n Wt i x + 11) + 2 * dsAV n Wt i x + 8).sum + 1)
        + 3) ≤ ∑ _i ∈ Finset.range (d n), (28 * tblC (pmW n) (pmW n) + (4 * pmW n + 2) *
      (9 * r n + 69 + 4 * (T n / r n) + 2 * Wt + 60 * (b n + 1) ^ 2) +
        23 * (11 * pmW n + 8) + 4) := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [ds_vars_cost]
    have := Nat.mul_le_mul_left (4 * pmW n + 2) (ds_ax_vals hn (Finset.mem_range.1 hi) Wt)
    omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  omega

/-! #### Arithmetic over plain variables -/

theorem ds_ar_pow (B : ℕ) (hB : 1 ≤ B) : B ≤ B ^ 2 ∧ B ^ 2 ≤ B ^ 3 ∧ B ^ 3 ≤ B ^ 4 :=
  ⟨Nat.le_self_pow (by norm_num) B, Nat.pow_le_pow_right hB (by norm_num),
    Nat.pow_le_pow_right hB (by norm_num)⟩

/-- `x y ≤ c₁ c₂ B^(i+j)` from `x ≤ c₁ B^i`, `y ≤ c₂ B^j`. -/
theorem ds_ar_mul {x y c₁ c₂ B i j : ℕ} (hx : x ≤ c₁ * B ^ i) (hy : y ≤ c₂ * B ^ j) :
    x * y ≤ (c₁ * c₂) * B ^ (i + j) := by
  calc x * y ≤ (c₁ * B ^ i) * (c₂ * B ^ j) := Nat.mul_le_mul hx hy
    _ = (c₁ * c₂) * B ^ (i + j) := by rw [pow_add]; ring

/-- The axis loop over plain variables. -/
theorem ds_ar_loop {d W C r T Tr Wt B : ℕ} (hB : 1 ≤ B) (hd : d ≤ B) (hdr : d * r ≤ T)
    (hdTr : d * Tr ≤ T) (hW1 : W ≤ 4 * B + 16) (hC : C ≤ 18600 * B ^ 2) (hWt : Wt ≤ 200 * B) :
    d * (28 * C + (4 * W + 2) * (9 * r + 69 + 4 * Tr + 2 * Wt + 60 * B ^ 2) +
      23 * (11 * W + 8) + 4) ≤ 13 * ((4 * W + 2) * T) + 50000 * B ^ 4 + 530000 * B ^ 3 := by
  obtain ⟨h2, h3, h4⟩ := ds_ar_pow B hB
  have e : d * (28 * C + (4 * W + 2) * (9 * r + 69 + 4 * Tr + 2 * Wt + 60 * B ^ 2) +
      23 * (11 * W + 8) + 4) = (4 * W + 2) * (9 * (d * r) + 4 * (d * Tr)) +
      d * ((4 * W + 2) * (69 + 2 * Wt + 60 * B ^ 2)) + d * (28 * C + 23 * (11 * W + 8) + 4) := by
    ring
  have p1 : (4 * W + 2) * (9 * (d * r) + 4 * (d * Tr)) ≤ (4 * W + 2) * (13 * T) :=
    Nat.mul_le_mul_left _ (by omega)
  have p2 : d * ((4 * W + 2) * (69 + 2 * Wt + 60 * B ^ 2)) ≤ 43460 * B ^ 4 := by
    have h1 : 4 * W + 2 ≤ 82 * B := by omega
    have h2 : 69 + 2 * Wt + 60 * B ^ 2 ≤ 530 * B ^ 2 := by omega
    calc d * ((4 * W + 2) * (69 + 2 * Wt + 60 * B ^ 2)) ≤ B * (82 * B * (530 * B ^ 2)) :=
          Nat.mul_le_mul hd (Nat.mul_le_mul h1 h2)
      _ = 43460 * B ^ 4 := by ring
  have p3 : d * (28 * C + 23 * (11 * W + 8) + 4) ≤ 530000 * B ^ 3 := by
    have h1 : 28 * C + 23 * (11 * W + 8) + 4 ≤ 530000 * B ^ 2 := by omega
    calc d * (28 * C + 23 * (11 * W + 8) + 4) ≤ B * (530000 * B ^ 2) := Nat.mul_le_mul hd h1
      _ = 530000 * B ^ 3 := by ring
  have e2 : (4 * W + 2) * (13 * T) = 13 * ((4 * W + 2) * T) := by ring
  omega

end Cost

end IntegerMultBounds.MathlibTM2.Fast.TableVM
