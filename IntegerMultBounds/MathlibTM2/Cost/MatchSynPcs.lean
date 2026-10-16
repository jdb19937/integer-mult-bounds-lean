module

public import IntegerMultBounds.MathlibTM2.Cost.LayerCost
public import IntegerMultBounds.MathlibTM2.Cost.Branching
public import IntegerMultBounds.MathlibTM2.Cost.Total
public import IntegerMultBounds.MathlibTM2.Fast.SynSel

/-!
# Cost matching: the pieces of a chunk round of the synthetic transforms

The pieces of a chunk round (`synPcs`, `Fast/SynRec.lean`) are the nonzero base-`m` digits of
the piece bits `D`: digit `j` gives one piece with `d_j < m` leaf bits at level `j` on
`R₂ = rowsAt (2^X) J'` rows, `J' = ⌊log_m D⌋`. Its layer call costs at most
`lcNorm · V'` with `V' = R₂ 2^n r w'` the padded volume (`Cost/LayerCost.lean`), and the
normalized cost obeys the node recurrence down to level `0` (no cutoff: the leaves have fewer
than `m` bits), so `Layer/Recurrence.recurrence_closed` gives
`lcNorm ≤ C (m^j d_j)^λ K^τ + C a^j d_j` with `a = F / NW`. With `m^j d_j ≤ D ≤ d`,
`K ≤ d^c`, `a < m^λ` and at most `1 + log_m d` pieces, the pieces cost
`C (1 + log_m d) d^{λ + c} V' ≤ C' d^{λ'} V'` (`mrP_pieces_le`).

* `mrP_tr`: a sequence truncated at level `j`, which follows the recurrence at every level.
* `mrP_norm_le`: the closed bound on `lcNorm … j` from the node steps below `j` only.
* `mrP_length_synPcs_le`, `mrP_synJ_le`: at most `synJ D D ≤ 1 + log_m d` pieces.
* `mrP_logb_branching`: `log_m (F / NW) < λ` for the fixed directions.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Networks
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.Sizes

set_option maxHeartbeats 4000000

/-! ### Truncated sequences -/

/-- The sequence `G` up to level `j`, continued by the recurrence `a · _ + c i` above it. -/
noncomputable def mrP_tr (G : ℕ → ℝ) (a : ℝ) (c : ℕ → ℝ) (j : ℕ) : ℕ → ℝ
  | 0 => G 0
  | i + 1 => if i + 1 ≤ j then G (i + 1) else a * mrP_tr G a c j i + c i

theorem mrP_tr_eq (G : ℕ → ℝ) (a : ℝ) (c : ℕ → ℝ) (j : ℕ) :
    ∀ i ≤ j, mrP_tr G a c j i = G i
  | 0, _ => rfl
  | i + 1, h => by simp [mrP_tr, h]

theorem mrP_tr_step (G : ℕ → ℝ) (a : ℝ) (c : ℕ → ℝ) (j : ℕ)
    (hs : ∀ i, i < j → G (i + 1) ≤ a * G i + c i) (i : ℕ) :
    mrP_tr G a c j (i + 1) ≤ a * mrP_tr G a c j i + c i := by
  by_cases h : i + 1 ≤ j
  · rw [mrP_tr_eq G a c j _ h, mrP_tr_eq G a c j i (by omega)]
    exact hs i (by omega)
  · simp [mrP_tr, h]

/-! ### Counting the pieces -/

theorem mrP_filterMap_le {α β : Type} (f : α → Option β) (p : α → Bool)
    (hp : ∀ a, (f a).isSome → p a) : ∀ l : List α, (l.filterMap f).length ≤ (l.filter p).length
  | [] => le_rfl
  | a :: l => by
      have ih := mrP_filterMap_le f p hp l
      rw [List.filter_cons]
      cases hfa : f a with
      | none =>
          rw [List.filterMap_cons_none hfa]
          split <;> simp <;> omega
      | some b =>
          have := hp a (by simp [hfa])
          rw [List.filterMap_cons_some hfa, ite_eq_left this]
          simp
          omega

/-- At most `synJ D t` pieces: one per `j < t` with `D / m^j > 0`. -/
theorem mrP_length_synPcs_le (K X D oS J t : ℕ) : (synPcs K X D oS J t).length ≤ synJ D t := by
  unfold synPcs synJ synJk
  have := mrP_filterMap_le
    (fun j => if synDg D j = 0 then none else some (synPc K X D oS J j))
    (fun j => decide (0 < D / m ^ j)) (fun j hj => by
      by_cases h0 : synDg D j = 0
      · simp [h0] at hj
      · simpa using synDg_pos_div h0) (List.range t).reverse
  rw [List.filter_reverse, List.length_reverse] at this
  exact this

/-- `synJ D D ≤ 1 + log_m d` for `D ≤ d`. -/
theorem mrP_synJ_le {D : ℕ} {dd : ℝ} (hD : (D : ℝ) ≤ dd) (hdd : 1 ≤ dd) :
    (synJ D D : ℝ) ≤ 1 + Real.logb m dd := by
  have hm : (1 : ℝ) < m := by exact_mod_cast one_lt_m
  have hl0 : 0 ≤ Real.logb m dd := Real.logb_nonneg hm hdd
  rcases Nat.eq_zero_or_pos D with rfl | hpos
  · simp only [synJ, synJk, List.range_zero, List.filter_nil, List.length_nil, Nat.cast_zero]
    linarith
  · rw [synJ_self_eq hpos.ne', Nat.cast_add, Nat.cast_one]
    have h1 : (Nat.log m D : ℝ) ≤ Real.logb m D := by
      have hf := Real.floor_logb_natCast (b := m) (r := (D : ℝ)) (Nat.cast_nonneg D)
      rw [Int.log_natCast] at hf
      have h2 := Int.floor_le (Real.logb (m : ℝ) (D : ℝ))
      rw [hf] at h2
      exact_mod_cast h2
    have h2 : Real.logb m D ≤ Real.logb m dd :=
      Real.logb_le_logb_of_le hm (by exact_mod_cast hpos) hD
    linarith

/-! ### Logarithms and exponents -/

theorem mrP_eps_pos : 0 < totLam' - totLam - cParam := by
  rw [cParam_eq]; norm_num [totLam, totLam']

/-- `1 + log_m d ≤ C d^ε` at the exponent gap `ε = λ' - λ - c`. -/
theorem mrP_eps_logb_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ dd : ℝ, 1 ≤ dd →
      1 + Real.logb m dd ≤ C * dd ^ (totLam' - totLam - cParam) := by
  have hm : (1 : ℝ) < m := by exact_mod_cast one_lt_m
  refine ⟨1 + 1 / ((totLam' - totLam - cParam) * Real.log m), ?_, fun dd hdd =>
    IntegerMultBounds.MathlibTM2.Layer.Recurrence.one_add_logb_le hm hdd mrP_eps_pos⟩
  exact add_nonneg zero_le_one
    (div_nonneg zero_le_one (mul_nonneg mrP_eps_pos.le (Real.log_nonneg hm.le)))

/-- `1 + log_m d ≤ C d^{λ'}`. -/
theorem mrP_one_add_logb_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ dd : ℝ, 1 ≤ dd → 1 + Real.logb m dd ≤ C * dd ^ totLam' := by
  have hm : (1 : ℝ) < m := by exact_mod_cast one_lt_m
  have hl : 0 < totLam' := by norm_num [totLam']
  refine ⟨1 + 1 / (totLam' * Real.log m), ?_, fun dd hdd =>
    IntegerMultBounds.MathlibTM2.Layer.Recurrence.one_add_logb_le hm hdd hl⟩
  exact add_nonneg zero_le_one
    (div_nonneg zero_le_one (mul_nonneg hl.le (Real.log_nonneg hm.le)))

/-- `log_m (F / NW) < λ` for the fixed directions (`br_branching`). -/
theorem mrP_logb_branching :
    Real.logb m ((factorCount (program Cost.brDirs) : ℝ) / NW) < totLam := by
  have hm : (1 : ℝ) < m := by exact_mod_cast one_lt_m
  have hb := br_branching
  have hσ := tot_sigma_lt_lam
  have h0 : (0 : ℝ) ≤ (factorCount (program Cost.brDirs) : ℝ) / NW :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.logb_zero]; linarith [tot_sigma_nonneg]
  · exact ((Real.logb_lt_iff_lt_rpow hm h).2 hb).trans hσ

/-! ### The closed bound at one level -/

/-- **The closed bound on `lcNorm … j`** from the node steps below level `j` (the child
exponents fit the word below `j`, `ε ≤ 1` there since `lcKey ≤ n + Lb + 1`). -/
theorem mrP_norm_le (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (hal : Real.logb m ((factorCount (program ds) : ℝ) / NW) < totLam)
    {u K ρ R₀ n r w' j Lb : ℕ} (hu : 1 ≤ u) (hK : 1 ≤ K) (hr : 1 ≤ r) (hw : 1 ≤ w')
    (hR₀ : 1 ≤ R₀) (hρ : ρ < K) (hfit : K * bits u j ≤ n) (hTw : ∀ i < j, expZ u ds i ≤ w')
    (hR : rowsAt R₀ j ≤ 2 ^ Lb) (h1 : 2 * (n + Lb + 2) ≤ r * w')
    (h2 : 24 * n * (n + Lb + 2) ≤ 2 ^ K) :
    lcNorm T ds u K ρ R₀ n r w' j ≤
      IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m totLam 400
          (2 * lcC1 T ds) * ((m : ℝ) ^ j * u) ^ totLam * (K : ℝ) ^ Parameters.tau +
        IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m totLam 400
          (2 * lcC1 T ds) * ((factorCount (program ds) : ℝ) / NW) ^ j * u := by
  have ha : (0 : ℝ) ≤ (factorCount (program ds) : ℝ) / NW :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hm : (1 : ℝ) < m := by exact_mod_cast one_lt_m
  have hC := lcC1_nonneg T ds
  have hkey : ∀ i, i ≤ j → lcKey R₀ n i ≤ n + Lb + 1 := by
    intro i hi
    have hrow : rowsAt R₀ i ≤ rowsAt R₀ j := by
      rw [rowsAt_eq, rowsAt_eq]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right one_le_NW hi)
    have hpos : rowsAt R₀ i ≠ 0 := by have := rowsAt_pos hR₀ i; omega
    have hlog : (rowsAt R₀ i).log2 ≤ Lb := by
      have : (rowsAt R₀ i).log2 < Lb + 1 := (Nat.log2_lt hpos).2 (by
        calc rowsAt R₀ i ≤ 2 ^ Lb := hrow.trans hR
          _ < 2 ^ (Lb + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega))
      omega
    have := lc_rb_le (rowsAt R₀ i)
    unfold lcKey
    omega
  have hstep : ∀ i, i < j → lcNorm T ds u K ρ R₀ n r w' (i + 1) ≤
      ((factorCount (program ds) : ℝ) / NW) * lcNorm T ds u K ρ R₀ n r w' i +
        2 * lcC1 T ds * (((K : ℝ) * (m : ℝ) ^ i * u) ^ Parameters.tau + 1) := by
    intro i hi
    have hadm : K * bits u (i + 1) ≤ n :=
      (Nat.mul_le_mul_left _ (lc_bits_mono u (by omega))).trans hfit
    have hki := hkey i (by omega)
    have hε := lc_eps_le_one (R₀ := R₀) (r := r) (w := w') hK hadm (by omega)
      ((Nat.mul_le_mul_left (24 * n) (by omega)).trans h2)
    have h := lc_norm_succ_le_eps T ds hu hr hw hR₀ hρ (n := n) (j := i)
      (fun _ i' hi' => hTw i' (by omega))
    refine h.trans ?_
    have hε0 : 0 ≤ lcEps u K R₀ n r w' i :=
      add_nonneg (lcDelta_nonneg _ _ _ _ _) (lcEbad_nonneg _ _ _ _ _ _ _)
    have hL : 0 ≤ ((K : ℝ) * (m : ℝ) ^ i * u) ^ Parameters.tau + 1 :=
      add_nonneg (Real.rpow_nonneg (by positivity) _) zero_le_one
    generalize ((K : ℝ) * (m : ℝ) ^ i * u) ^ Parameters.tau + 1 = L at hL ⊢
    generalize lcEps u K R₀ n r w' i = e at hε hε0 ⊢
    nlinarith [mul_nonneg (mul_nonneg hC hL) (sub_nonneg.2 hε)]
  have h0 : lcNorm T ds u K ρ R₀ n r w' 0 ≤ 400 * u := by
    have h := lc_norm_zero_le T ds hu hr hw hR₀ hρ (n := n)
    have hpos : (0 : ℝ) < ((r * w' : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hr hw
    have hq : (n : ℝ) / ((r * w' : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hpos, one_mul]; exact_mod_cast (show n ≤ r * w' by omega)
    have hq0 : 0 ≤ (n : ℝ) / ((r * w' : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg _) hpos.le
    have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
    generalize (n : ℝ) / ((r * w' : ℕ) : ℝ) = q at h hq hq0
    nlinarith
  have hrec := IntegerMultBounds.MathlibTM2.Layer.Recurrence.recurrence_closed
    (F := mrP_tr (fun i => lcNorm T ds u K ρ R₀ n r w' i) ((factorCount (program ds) : ℝ) / NW)
      (fun i => 2 * lcC1 T ds * (((K : ℝ) * (m : ℝ) ^ i * u) ^ Parameters.tau + 1)) j)
    (C₀ := 400) (C₁ := 2 * lcC1 T ds)
    ha hm tot_tau_nonneg tot_tau_lt_lam.le hal (by exact_mod_cast hK) (by norm_num)
    (by linarith) (by exact_mod_cast hu)
    (by rw [mrP_tr_eq _ _ _ _ 0 (Nat.zero_le _)]; exact h0)
    (mrP_tr_step _ _ _ _ hstep) j
  rwa [mrP_tr_eq _ _ _ _ j le_rfl] at hrec

/-! ### One piece -/

/-- One piece of a chunk round costs at most `C d^λ (d^c + m) V'`. -/
theorem mrP_piece_le (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (hal : Real.logb m ((factorCount (program ds) : ℝ) / NW) < totLam)
    {K ρ X D oS n r w' Lb : ℕ} {dd : ℝ}
    (hK : 1 ≤ K) (hρ : ρ < K) (hr : 1 ≤ r) (hw : 1 ≤ w') (hD : (D : ℝ) ≤ dd) (hdd : 1 ≤ dd)
    (hKd : (K : ℝ) ≤ dd ^ cParam) (hfit : oS + K * D ≤ n)
    (hE : synE (gateCount (program ds)) (factorCount (program ds)) D D + D ≤ w')
    (hR : rowsAt (2 ^ X) (synJ D D - 1) ≤ 2 ^ Lb) (h1 : 2 * (n + Lb + 2) ≤ r * w')
    (h2 : 24 * n * (n + Lb + 2) ≤ 2 ^ K) {pc : TopPc}
    (hpc : pc ∈ synPcs K X D oS (synJ D D - 1) D) :
    (layerCost T ds pc.u K ρ pc.R₀ n r w' pc.j pc.a₀ : ℝ) ≤
      IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m totLam 400
          (2 * lcC1 T ds) * dd ^ totLam * (dd ^ cParam + m) *
        ((rowsAt (2 ^ X) (synJ D D - 1) * 2 ^ n * (r * w') : ℕ) : ℝ) := by
  have hok := synPcs_ok ds hfit hE pc hpc
  obtain ⟨j, hj, hd0, rfl⟩ := mem_synPcs hpc
  have hoku : 1 ≤ synDg D j := hok.hu
  have hokR₀ : 1 ≤ rowsAt (2 ^ X) (synJ D D - 1 - j) := hok.hR₀
  have hokR : rowsAt (2 ^ X) (synJ D D - 1) = rowsAt (rowsAt (2 ^ X) (synJ D D - 1 - j)) j :=
    hok.hR
  have hokTw : ∀ i < j, expZ (synDg D j) ds i ≤ w' := hok.hTw
  have hokfit : oS + K * (D % m ^ j) + K * bits (synDg D j) j ≤ n := hok.hfit
  clear hok
  simp only [synPc]
  have ha : (0 : ℝ) ≤ (factorCount (program ds) : ℝ) / NW :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hm : (1 : ℝ) < m := by exact_mod_cast one_lt_m
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hC := lcC1_nonneg T ds
  have hfit' : K * bits (synDg D j) j ≤ n := by omega
  have hR' : rowsAt (rowsAt (2 ^ X) (synJ D D - 1 - j)) j ≤ 2 ^ Lb := by
    rw [← hokR]; exact hR
  have hnorm := mrP_norm_le T ds hal hoku hK hr hw hokR₀ hρ hfit' hokTw hR' h1 h2
  have hV := lcVol_pos (n := n) hr hw hokR₀ j
  have hmax : (lcMax T ds (synDg D j) K ρ (rowsAt (2 ^ X) (synJ D D - 1 - j)) n r w' j : ℝ) =
      lcNorm T ds (synDg D j) K ρ (rowsAt (2 ^ X) (synJ D D - 1 - j)) n r w' j *
        (lcVol (rowsAt (2 ^ X) (synJ D D - 1 - j)) n r w' j : ℝ) := by
    unfold lcNorm; rw [div_mul_cancel₀ _ hV.ne']
  have hvol : (lcVol (rowsAt (2 ^ X) (synJ D D - 1 - j)) n r w' j : ℝ) =
      ((rowsAt (2 ^ X) (synJ D D - 1) * 2 ^ n * (r * w') : ℕ) : ℝ) := by
    unfold lcVol; rw [← hokR]
  -- the per-piece constants
  have hmu : (m : ℝ) ^ j * (synDg D j : ℝ) ≤ dd := by
    have h1' : D % m ^ j + synDg D j * m ^ j ≤ D := by
      rw [← mod_pow_succ_dg]; exact Nat.mod_le _ _
    have h3 : synDg D j * m ^ j ≤ D := le_trans (Nat.le_add_left _ _) h1'
    have h2' : ((synDg D j * m ^ j : ℕ) : ℝ) ≤ D := by exact_mod_cast h3
    rw [Nat.cast_mul, Nat.cast_pow] at h2'
    linarith
  have hu1 : (1 : ℝ) ≤ synDg D j := by exact_mod_cast hoku
  have hum : (synDg D j : ℝ) ≤ m := by
    have : synDg D j < m := Nat.mod_lt _ m_pos
    exact_mod_cast this.le
  have hmj : (m : ℝ) ^ j ≤ dd := by
    have hp : (0 : ℝ) ≤ (m : ℝ) ^ j := pow_nonneg hm0 j
    nlinarith
  have hlam0 : 0 ≤ totLam := by norm_num [totLam]
  have hP : ((m : ℝ) ^ j * (synDg D j : ℝ)) ^ totLam ≤ dd ^ totLam :=
    Real.rpow_le_rpow (by positivity) hmu hlam0
  have hKτ : (K : ℝ) ^ Parameters.tau ≤ dd ^ cParam := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    calc (K : ℝ) ^ Parameters.tau ≤ (K : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK1 tot_tau_le_one
      _ = K := Real.rpow_one _
      _ ≤ dd ^ cParam := hKd
  have halt : (factorCount (program ds) : ℝ) / NW < (m : ℝ) ^ totLam :=
    IntegerMultBounds.MathlibTM2.Layer.Recurrence.lt_rpow_of_logb_lt ha hm hal
  have hA : ((factorCount (program ds) : ℝ) / NW) ^ j ≤ dd ^ totLam := by
    calc ((factorCount (program ds) : ℝ) / NW) ^ j ≤ ((m : ℝ) ^ totLam) ^ j :=
          pow_le_pow_left₀ ha halt.le j
      _ = ((m : ℝ) ^ j) ^ totLam := (IntegerMultBounds.MathlibTM2.Layer.Recurrence.pow_rpow_eq hm0 j totLam).symm
      _ ≤ dd ^ totLam := Real.rpow_le_rpow (pow_nonneg hm0 j) hmj hlam0
  have hRc : 0 ≤ IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m totLam
      400 (2 * lcC1 T ds) := by
    unfold IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst
    refine add_nonneg (by norm_num) (div_nonneg ?_ (sub_pos.2 halt).le)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.rpow_nonneg hm0 _)
  have hdd0 : (0 : ℝ) ≤ dd := by linarith
  have hDl : 0 ≤ dd ^ totLam := Real.rpow_nonneg hdd0 _
  have hDc : 0 ≤ dd ^ cParam := Real.rpow_nonneg hdd0 _
  have hKτ0 : 0 ≤ (K : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA0 : 0 ≤ ((factorCount (program ds) : ℝ) / NW) ^ j := pow_nonneg ha j
  have hP0 : 0 ≤ ((m : ℝ) ^ j * (synDg D j : ℝ)) ^ totLam := Real.rpow_nonneg (by positivity) _
  -- the normalized bound
  have hnb : lcNorm T ds (synDg D j) K ρ (rowsAt (2 ^ X) (synJ D D - 1 - j)) n r w' j ≤
      IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m totLam 400
        (2 * lcC1 T ds) * dd ^ totLam * (dd ^ cParam + m) := by
    refine hnorm.trans ?_
    generalize IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m totLam
      400 (2 * lcC1 T ds) = Rc at hRc ⊢
    generalize ((m : ℝ) ^ j * (synDg D j : ℝ)) ^ totLam = P at hP hP0 ⊢
    generalize (K : ℝ) ^ Parameters.tau = Kt at hKτ hKτ0 ⊢
    generalize ((factorCount (program ds) : ℝ) / NW) ^ j = A at hA hA0 ⊢
    generalize dd ^ totLam = Dl at hP hA hDl ⊢
    generalize dd ^ cParam = Dc at hKτ hDc ⊢
    generalize (synDg D j : ℝ) = U at hu1 hum ⊢
    have e1 : Rc * P * Kt ≤ Rc * Dl * Dc :=
      mul_le_mul (mul_le_mul_of_nonneg_left hP hRc) hKτ hKτ0 (mul_nonneg hRc hDl)
    have e2 : Rc * A * U ≤ Rc * Dl * m :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA hRc) hum (by linarith) (mul_nonneg hRc hDl)
    nlinarith
  calc (layerCost T ds (synDg D j) K ρ (rowsAt (2 ^ X) (synJ D D - 1 - j)) n r w' j
        (oS + K * (D % m ^ j)) : ℝ)
      ≤ (lcMax T ds (synDg D j) K ρ (rowsAt (2 ^ X) (synJ D D - 1 - j)) n r w' j : ℝ) := by
        exact_mod_cast lc_le_max T ds hokfit
    _ = _ := hmax
    _ ≤ _ := mul_le_mul_of_nonneg_right hnb hV.le
    _ = _ := by rw [hvol]

/-! ### All the pieces -/

/-- **The layer calls of the pieces of a chunk round** cost `C d^{λ'}` times the padded volume
`R₂ 2^n r w'`, `R₂ = rowsAt (2^X) J'`, `J' = ⌊log_m D⌋`. -/
theorem mrP_pieces_le (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (hal : Real.logb m ((factorCount (program ds) : ℝ) / NW) < totLam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K ρ X D oS n r w' Lb : ℕ) (dd : ℝ),
      1 ≤ K → ρ < K → 1 ≤ r → 1 ≤ w' → (D : ℝ) ≤ dd → 1 ≤ dd → (K : ℝ) ≤ dd ^ cParam →
      oS + K * D ≤ n →
      synE (gateCount (program ds)) (factorCount (program ds)) D D + D ≤ w' →
      rowsAt (2 ^ X) (synJ D D - 1) ≤ 2 ^ Lb → 2 * (n + Lb + 2) ≤ r * w' →
      24 * n * (n + Lb + 2) ≤ 2 ^ K →
      (((synPcs K X D oS (synJ D D - 1) D).map fun pc =>
          layerCost T ds pc.u K ρ pc.R₀ n r w' pc.j pc.a₀).sum : ℝ) ≤
        C * dd ^ totLam' * ((rowsAt (2 ^ X) (synJ D D - 1) * 2 ^ n * (r * w') : ℕ) : ℝ) := by
  obtain ⟨Cε, hCε0, hCε⟩ := mrP_eps_logb_le
  have ha : (0 : ℝ) ≤ (factorCount (program ds) : ℝ) / NW :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hm : (1 : ℝ) < m := by exact_mod_cast one_lt_m
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hC := lcC1_nonneg T ds
  have halt : (factorCount (program ds) : ℝ) / NW < (m : ℝ) ^ totLam :=
    IntegerMultBounds.MathlibTM2.Layer.Recurrence.lt_rpow_of_logb_lt ha hm hal
  have hRc : 0 ≤ IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m totLam
      400 (2 * lcC1 T ds) := by
    unfold IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst
    refine add_nonneg (by norm_num) (div_nonneg ?_ (sub_pos.2 halt).le)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.rpow_nonneg hm0 _)
  generalize hRcd : IntegerMultBounds.MathlibTM2.Layer.Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m totLam
    400 (2 * lcC1 T ds) = Rc at hRc
  refine ⟨Cε * Rc * (1 + m), mul_nonneg (mul_nonneg hCε0 hRc) (by linarith), ?_⟩
  intro K ρ X D oS n r w' Lb dd hK hρ hr hw hD hdd hKd hfit hE hR h1 h2
  rw [Nat.cast_list_sum, List.map_map]
  set V : ℝ := ((rowsAt (2 ^ X) (synJ D D - 1) * 2 ^ n * (r * w') : ℕ) : ℝ) with hVd
  have hV0 : 0 ≤ V := Nat.cast_nonneg _
  have hper : ∀ x ∈ (synPcs K X D oS (synJ D D - 1) D).map
      (Nat.cast ∘ fun pc => layerCost T ds pc.u K ρ pc.R₀ n r w' pc.j pc.a₀),
      x ≤ Rc * dd ^ totLam * (dd ^ cParam + m) * V := by
    intro x hx
    obtain ⟨pc, hpc, rfl⟩ := List.mem_map.1 hx
    have := mrP_piece_le T ds hal hK hρ hr hw hD hdd hKd hfit hE hR h1 h2 hpc
    rw [hRcd] at this
    exact this
  have hsum := List.sum_le_length_nsmul _ _ hper
  rw [List.length_map, nsmul_eq_mul] at hsum
  have hlen₁ : ((synPcs K X D oS (synJ D D - 1) D).length : ℝ) ≤ (synJ D D : ℝ) := by
    exact_mod_cast mrP_length_synPcs_le K X D oS (synJ D D - 1) D
  have hlen : ((synPcs K X D oS (synJ D D - 1) D).length : ℝ) ≤ 1 + Real.logb m dd :=
    hlen₁.trans (mrP_synJ_le hD hdd)
  have hlog := hlen.trans (hCε dd hdd)
  have hdd0 : 0 < dd := by linarith
  have hexp : dd ^ (totLam' - totLam - cParam) * dd ^ totLam * dd ^ cParam = dd ^ totLam' := by
    rw [← Real.rpow_add hdd0, ← Real.rpow_add hdd0]; congr 1; ring
  have hDl : 0 ≤ dd ^ totLam := Real.rpow_nonneg hdd0.le _
  have hDc1 : 1 ≤ dd ^ cParam := Real.one_le_rpow hdd gr_cParam_pos.le
  have hE0 : 0 ≤ dd ^ (totLam' - totLam - cParam) := Real.rpow_nonneg hdd0.le _
  have hlen0 : (0 : ℝ) ≤ ((synPcs K X D oS (synJ D D - 1) D).length : ℝ) := Nat.cast_nonneg _
  rw [← hexp]
  generalize dd ^ (totLam' - totLam - cParam) = E at hlog hE0 ⊢
  generalize dd ^ totLam = Dl at hDl hsum ⊢
  generalize dd ^ cParam = Dc at hDc1 hsum ⊢
  generalize ((synPcs K X D oS (synJ D D - 1) D).length : ℝ) = len at hsum hlog hlen0 ⊢
  have hsplit : Dc + m ≤ (1 + m) * Dc := by nlinarith
  have hB0 : 0 ≤ Rc * Dl * (Dc + m) * V :=
    mul_nonneg (mul_nonneg (mul_nonneg hRc hDl) (by linarith)) hV0
  calc _ ≤ len * (Rc * Dl * (Dc + m) * V) := hsum
    _ ≤ (Cε * E) * (Rc * Dl * ((1 + m) * Dc) * V) := by
        refine mul_le_mul hlog ?_ hB0 (mul_nonneg hCε0 hE0)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsplit (mul_nonneg hRc hDl)) hV0
    _ = Cε * Rc * (1 + m) * (E * Dl * Dc) * V := by ring

end IntegerMultBounds.MathlibTM2.Cost
