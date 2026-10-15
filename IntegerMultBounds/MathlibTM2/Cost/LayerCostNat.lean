module

public import IntegerMultBounds.MathlibTM2.Node.LayerProc

/-!
# Step counts of the layer machine: the linear parts

Natural-number bounds on the step bound `layerCost T ds u K ρ R₀ n r w j a₀` of
`Node/LayerProc.lean`. At a node of level `j + 1` write `R = rowsAt R₀ j` for the rows of one
wire, `V = R 2^n (r w)` for the volume of a wire (the volume of a child array), `W = R 2^n n`, and
`X = NW (V + W)`; the level-`j + 1` array has volume `NW V`, so `X = V_{j+1} (1 + n / (r w))`.
Let `F = factorCount (program ds)`, `G = gateCount (program ds)`, `c₂₅ = |Wires.Address 25|`.

* `lc_leaf_nat`: `layerCost … 0 a₀ ≤ 200 u (R₀ 2^n (r w) + R₀ 2^n n)`.
* `lc_signStage_le`: a sign stage costs at most `(4 m c₂₅ + 200 c₂₅ + 200) X`.
* `lc_factor_nat`: the factor program of `(fw, g)` costs at most `cc + 2 B + 400 NW (V + W)`,
  for a child call within `cc` steps and basis changes within `B` steps each.
* `lc_node_nat`: `layerCost … (j + 1) a₀ ≤ F (M + 2 B) + lcLin ds · X` when every child call
  (offset `a₀ + s K bits u j`, `s < m`) is within `M` steps and every basis change within `B`
  steps; `lcLin ds = 400 F + 50 G + 8 m c₂₅ + 500 c₂₅ + 500`.

Hypotheses: `1 ≤ u, r, w, R₀`, `ρ < K`, the active bits fit (`a₀ + K · bits u (j + 1) ≤ n`) and
the child exponents fit the word (`expZ u ds i ≤ w` for `i ≤ j`). The fit gives
`a₀, K, u, j, bits u (j + 1) ≤ n` (`LcFacts`), and `n < 2^n` puts every term linear in `n`, `w`
or `j w` under `V` or `W`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Networks

/-! ### Elementary facts -/

/-- `bits u j = m^j u`. -/
lemma lc_bits_eq (u : ℕ) : ∀ j, bits u j = m ^ j * u
  | 0 => by simp [bits]
  | j + 1 => by rw [bits, lc_bits_eq u j, pow_succ]; ring

lemma lc_bits_mono (u : ℕ) {i j : ℕ} (h : i ≤ j) : bits u i ≤ bits u j := by
  rw [lc_bits_eq, lc_bits_eq]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num [m]) h)

/-- The level is at most the number of active bits. -/
lemma lc_lev_le_bits {u : ℕ} (hu : 1 ≤ u) (j : ℕ) : j ≤ bits u j := by
  rw [lc_bits_eq]
  have h1 : j < 2 ^ j := Nat.lt_two_pow_self
  have h2 : 2 ^ j ≤ m ^ j := Nat.pow_le_pow_left (by norm_num [m]) j
  have h3 : m ^ j ≤ m ^ j * u := Nat.le_mul_of_pos_right _ hu
  omega

/-- The exponent program with every exponent below `j` at most `x`. -/
lemma lc_expCost_le {G F u j x : ℕ} (h : ∀ i < j, expSeq G F u i ≤ x) :
    expCost G F u j ≤ 4 * u + 2 * j + 8 + j * (8 * x + 12) := by
  unfold expCost
  have : ∑ i ∈ Finset.range j, (8 * expSeq G F u i + 12) ≤ ∑ _i ∈ Finset.range j, (8 * x + 12) :=
    Finset.sum_le_sum fun i hi => by have := h i (Finset.mem_range.1 hi); omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  omega

/-- The pivot of a factor direction is a slot. -/
lemma lc_pivotOf_lt (vv : BinaryWalsh.Address m) : pivotOf vv < m := by
  unfold pivotOf
  split_ifs with h
  · exact (Fin.find _ h).2
  · norm_num [m]

/-! ### The node -/

/-- Size facts at a node of level `j + 1` with `R` rows per wire: every parameter is at most
`n`, and `R`, `w`, `j w` are at most the wire volume `R 2^n (r w)`. -/
structure LcFacts (u K a₀ R n r w j : ℕ) : Prop where
  hR : 1 ≤ R
  hP : 1 ≤ R * 2 ^ n
  hV1 : 1 ≤ R * 2 ^ n * (r * w)
  hPV : R * 2 ^ n ≤ R * 2 ^ n * (r * w)
  hRV : R ≤ R * 2 ^ n * (r * w)
  hPr : R * 2 ^ n * r ≤ R * 2 ^ n * (r * w)
  hwV : w ≤ R * 2 ^ n * (r * w)
  hnW : n ≤ R * 2 ^ n * n
  hjw : j * w ≤ R * 2 ^ n * (r * w)
  hjn : j * n ≤ R * 2 ^ n * n
  hK1 : 1 ≤ K
  hk1 : 1 ≤ bits u j
  hkn : bits u (j + 1) ≤ n
  hKk : K * bits u (j + 1) ≤ n
  hLc : K * bits u j ≤ n
  hun : u ≤ n
  hjle : j ≤ n
  ha₀ : a₀ ≤ n
  hKn : K ≤ n

/-- The size facts from the hypotheses of the node. -/
theorem lcFacts_of {u K ρ a₀ R n r w j : ℕ} (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR : 1 ≤ R)
    (hρ : ρ < K) (hfit : a₀ + K * bits u (j + 1) ≤ n) : LcFacts u K a₀ R n r w j := by
  have h2 : n < 2 ^ n := Nat.lt_two_pow_self
  have hP : 1 ≤ R * 2 ^ n := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hrw : 1 ≤ r * w := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hV : R * 2 ^ n ≤ R * 2 ^ n * (r * w) := Nat.le_mul_of_pos_right _ hrw
  have hK1 : 1 ≤ K := by omega
  have hk1 : bits u (j + 1) ≤ n := by
    have : bits u (j + 1) ≤ K * bits u (j + 1) := Nat.le_mul_of_pos_left _ hK1
    omega
  have hjn : j ≤ n := le_trans (lc_lev_le_bits hu j) (le_trans (lc_bits_mono u (Nat.le_succ j)) hk1)
  have h2R : 2 ^ n ≤ R * 2 ^ n * r := by
    have : 2 ^ n ≤ R * 2 ^ n := Nat.le_mul_of_pos_left _ hR
    exact le_trans this (Nat.le_mul_of_pos_right _ hr)
  refine
    { hR := hR, hP := hP, hV1 := le_trans hP hV, hPV := hV
      hRV := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hV
      hPr := by rw [← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ hw
      hwV := by
        have : w ≤ (R * 2 ^ n * r) * w := Nat.le_mul_of_pos_left w (by positivity)
        calc w ≤ _ := this
          _ = _ := by ring
      hnW := Nat.le_mul_of_pos_left n hP
      hjw := by
        have h1 : j * w ≤ 2 ^ n * w := Nat.mul_le_mul_right _ (by omega)
        have h3 : 2 ^ n * w ≤ R * 2 ^ n * (r * w) := by
          calc 2 ^ n * w ≤ R * 2 ^ n * r * w := Nat.mul_le_mul_right _ h2R
            _ = R * 2 ^ n * (r * w) := by ring
        omega
      hjn := by
        have : j ≤ R * 2 ^ n := le_trans (by omega) (Nat.le_mul_of_pos_left _ hR)
        exact Nat.mul_le_mul_right _ this
      hK1 := hK1, hk1 := bits_pos hu j, hkn := hk1, hKk := by omega
      hLc := by
        have : K * bits u j ≤ K * bits u (j + 1) :=
          Nat.mul_le_mul_left K (lc_bits_mono u (Nat.le_succ j))
        omega
      hun := le_trans (lc_bits_mono u (Nat.zero_le (j + 1))) hk1
      hjle := hjn
      ha₀ := by omega
      hKn := by
        have : K ≤ K * bits u (j + 1) := Nat.le_mul_of_pos_right _ (bits_pos hu (j + 1))
        omega }

/-- `X = NW (V + W)` dominates `1`, `V` and `W`. -/
lemma lc_X_ge {R n r w : ℕ} (hV1 : 1 ≤ R * 2 ^ n * (r * w)) :
    1 ≤ NW * (R * 2 ^ n * (r * w) + R * 2 ^ n * n) ∧
    R * 2 ^ n * (r * w) ≤ NW * (R * 2 ^ n * (r * w) + R * 2 ^ n * n) ∧
    R * 2 ^ n * n ≤ NW * (R * 2 ^ n * (r * w) + R * 2 ^ n * n) := by
  have hNW : 1 ≤ NW := one_le_NW
  have h := Nat.le_mul_of_pos_left (R * 2 ^ n * (r * w) + R * 2 ^ n * n) hNW
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **The sign stage**: `signStageCost ≤ (4 m c₂₅ + 200 c₂₅ + 200) X`. -/
theorem lc_signStage_le {u K ρ a₀ R n r w j : ℕ} (hF : LcFacts u K a₀ R n r w j) (hρ : ρ < K) :
    signStageCost u j a₀ ρ K R n r w ≤
      (4 * m * Fintype.card (Wires.Address 25) + 200 * Fintype.card (Wires.Address 25) + 200) *
        (NW * (R * 2 ^ n * (r * w) + R * 2 ^ n * n)) := by
  obtain ⟨hX1, hXV, hXW⟩ := lc_X_ge hF.hV1
  have hNW : 1 ≤ NW := one_le_NW
  have hdiv : NW * R / NW = R := Nat.mul_div_cancel_left R (by omega)
  have hE : expCost 0 m u j ≤ 4 * u + 2 * j + 8 + j * (8 * n + 12) := lc_expCost_le fun i hi => by
    rw [← bits_eq_expSeq]; exact le_trans (lc_bits_mono u (by omega)) hF.hkn
  have hmk : m * bits u j * K ≤ n := by
    have : bits u (j + 1) = m * bits u j := rfl
    nlinarith [hF.hKk]
  have hmk' : m * bits u j ≤ n := le_trans (Nat.le_mul_of_pos_right _ hF.hK1) hmk
  have hmX : m ≤ m * (NW * (R * 2 ^ n * (r * w) + R * 2 ^ n * n)) := Nat.le_mul_of_pos_right m hX1
  have hsign : signCost n (a₀ + ρ) K (bits u j) R r w ≤
      (4 * m + 200) * (NW * (R * 2 ^ n * (r * w) + R * 2 ^ n * n)) := by
    unfold signCost
    have : m * (bits u j * (4 * K + 9) + 4) ≤ 13 * n + 4 * m := by nlinarith
    nlinarith [hF.hPV, hF.hnW, hF.ha₀, hF.hKn]
  have hNWR : NW * R ≤ NW * (R * 2 ^ n * (r * w) + R * 2 ^ n * n) :=
    Nat.mul_le_mul_left NW (hF.hRV.trans (Nat.le_add_right _ _))
  have hc := Nat.mul_le_mul_left (Fintype.card (Wires.Address 25)) hsign
  unfold signStageCost maskPrepCost
  rw [hdiv]
  have h2R : 2 ^ n * R ≤ R * 2 ^ n * (r * w) := by
    have : 2 ^ n * R = R * 2 ^ n := Nat.mul_comm _ _
    have := hF.hPV
    omega
  have hjn := hF.hjn
  have hc1 : Fintype.card (Wires.Address 25) ≤ Fintype.card (Wires.Address 25) *
      (NW * (R * 2 ^ n * (r * w) + R * 2 ^ n * n)) := Nat.le_mul_of_pos_right _ hX1
  nlinarith [hF.ha₀, hF.hun, hF.hjle, hF.hk1, hF.hkn, hF.hKn, hF.hnW]

/-- **The factor program**: `factorCost … g cc ≤ cc + 2 B + 400 NW (V + W)`. -/
theorem lc_factor_nat (T : ℕ) (ds : ComplexFramedExecution.Directions)
    {j u K ρ a₀ R₀ n r w : ℕ} (g : ZMod 4 × BinaryWalsh.Address m) (cc B : ℕ)
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hfit : a₀ + K * bits u (j + 1) ≤ n) (hTw : ∀ i ≤ j, expZ u ds i ≤ w)
    (hB : ∀ (vv : BinaryWalsh.Address m) (s : Fin m),
      basisCostN T a₀ K ρ (K * bits u j) (rowsAt R₀ j) n (r * w) (bits u j) vv s ≤ B) :
    factorCost T ds j u K ρ a₀ R₀ n r w g cc ≤
      cc + 2 * B + 400 * NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) := by
  have hF : LcFacts u K a₀ (rowsAt R₀ j) n r w j :=
    lcFacts_of hu hr hw (rowsAt_pos hR₀ j) hρ hfit
  set R := rowsAt R₀ j with hRdef
  have hNW : 1 ≤ NW := one_le_NW
  have hV1 := hF.hV1
  have hWn := hF.hnW
  have hRV := hF.hRV
  have hPr := hF.hPr
  have hwV := hF.hwV
  have hLc := hF.hLc
  have hun := hF.hun
  have hjn := hF.hjle
  have hjw := hF.hjw
  have hTc : expZ u ds j ≤ w := hTw j le_rfl
  have hE : expCost (gateCount (program ds)) (factorCount (program ds)) u j ≤
      4 * u + 2 * j + 8 + j * (8 * w + 12) := lc_expCost_le fun i hi => by
    rw [← expZ_eq_expSeq]; exact hTw i hi.le
  have hTcP : R * 2 ^ n * r * expZ u ds j ≤ R * 2 ^ n * (r * w) := by
    calc R * 2 ^ n * r * expZ u ds j ≤ R * 2 ^ n * r * w := Nat.mul_le_mul_left _ hTc
      _ = R * 2 ^ n * (r * w) := by ring
  have hNWV : ∀ x, x ≤ R * 2 ^ n * (r * w) → NW * x ≤ NW * (R * 2 ^ n * (r * w)) :=
    fun x hx => Nat.mul_le_mul_left _ hx
  have hNWV1 : NW ≤ NW * (R * 2 ^ n * (r * w)) := Nat.le_mul_of_pos_right _ hV1
  have hVNW : R * 2 ^ n * (r * w) ≤ NW * (R * 2 ^ n * (r * w)) := Nat.le_mul_of_pos_left _ hNW
  have hWNW : R * 2 ^ n * n ≤ NW * (R * 2 ^ n * n) := Nat.le_mul_of_pos_left _ hNW
  unfold factorCost
  split_ifs with hpiv
  · set s : Fin m := Fin.find _ hpiv
    have hs : (s : ℕ) * (K * bits u j) ≤ n := by
      have : (s : ℕ) * (K * bits u j) ≤ m * (K * bits u j) := Nat.mul_le_mul_right _ s.2.le
      have h' : m * (K * bits u j) = K * bits u (j + 1) := by
        rw [show bits u (j + 1) = m * bits u j from rfl]; ring
      have := hF.hKk
      omega
    have hb := hB g.2 s
    have h1 := hNWV _ hRV
    have h2' := hNWV _ hTcP
    have h3 := hNWV _ hPr
    unfold childCost callCost conjCost shiftCost
    nlinarith
  · unfold shiftCost
    have h2' := hNWV _ hTcP
    have h3 := hNWV _ hPr
    nlinarith

/-- `facMax` is at most any bound of its factor values. -/
lemma lc_facMax_le (ds : ComplexFramedExecution.Directions)
    (f : NWire → ZMod 4 × BinaryWalsh.Address m → ℕ) (b : ℕ)
    (h : ∀ fw g, Instr.factor fw g ∈ program ds → f fw g ≤ b) : facMax ds f ≤ b := by
  unfold facMax
  generalize program ds = l at h
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.foldr_cons]
      refine max_le ?_ (ih fun fw g hg => h fw g (List.mem_cons_of_mem _ hg))
      cases i with
      | gate _ => exact Nat.zero_le _
      | factor fw g => exact h fw g List.mem_cons_self

/-- The constant of the linear part of a node:
`400 F + 50 G + 8 m c₂₅ + 500 c₂₅ + 500`. -/
noncomputable def lcLin (ds : ComplexFramedExecution.Directions) : ℕ :=
  400 * factorCount (program ds) + 50 * gateCount (program ds) +
    8 * m * Fintype.card (Wires.Address 25) + 500 * Fintype.card (Wires.Address 25) + 500

/-- **The node in natural numbers.** With every child call within `M` steps and every basis
change within `B` steps, `layerCost … (j + 1) a₀ ≤ F (M + 2 B) + lcLin ds · NW (V + W)`. -/
theorem lc_node_nat (T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w j a₀ M B : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hfit : a₀ + K * bits u (j + 1) ≤ n) (hTw : ∀ i ≤ j, expZ u ds i ≤ w)
    (hM : ∀ s < m, layerCost T ds u K ρ R₀ n r w j (a₀ + s * (K * bits u j)) ≤ M)
    (hB : ∀ (vv : BinaryWalsh.Address m) (s : Fin m),
      basisCostN T a₀ K ρ (K * bits u j) (rowsAt R₀ j) n (r * w) (bits u j) vv s ≤ B) :
    layerCost T ds u K ρ R₀ n r w (j + 1) a₀ ≤
      factorCount (program ds) * (M + 2 * B) +
        lcLin ds * (NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n)) := by
  have hF : LcFacts u K a₀ (rowsAt R₀ j) n r w j :=
    lcFacts_of hu hr hw (rowsAt_pos hR₀ j) hρ hfit
  obtain ⟨hX1, hXV, hXW⟩ := lc_X_ge hF.hV1
  have hNW : 1 ≤ NW := one_le_NW
  have hcf : facMax ds (fun _ g => factorCost T ds j u K ρ a₀ R₀ n r w g
      (layerCost T ds u K ρ R₀ n r w j (a₀ + pivotOf g.2 * (K * bits u j)))) ≤
      M + 2 * B + 400 * NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) := by
    refine lc_facMax_le ds _ _ fun fw g _ => ?_
    refine le_trans (lc_factor_nat T ds g _ B hu hr hw hR₀ hρ hfit hTw hB) ?_
    have := hM _ (lc_pivotOf_lt g.2)
    omega
  have hSS := lc_signStage_le hF hρ
  have hgate : gateCost (rowsAt R₀ j) n r w ≤
      43 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n)) := by
    unfold gateCost
    have h1 : NW * (rowsAt R₀ j * 2 ^ n * r) * (11 * w + 24) ≤
        35 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w))) := by
      have := Nat.mul_le_mul_left NW hF.hPr
      nlinarith
    have h2 : NW * (rowsAt R₀ j * 2 ^ n * (r * w)) ≤
        NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
      Nat.mul_le_mul_left NW (Nat.le_add_right _ _)
    have h3 : NW ≤ NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
      Nat.le_mul_of_pos_right _ (by have := hF.hV1; omega)
    rw [show Fintype.card NWire = NW from rfl]
    omega
  have hexch : exchCost u (rowsAt R₀ j) n r w ≤
      30 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n)) := by
    unfold exchCost
    nlinarith [hF.hPr, hF.hun, hF.hnW]
  have hE : expCost (gateCount (program ds)) (factorCount (program ds)) u j ≤
      4 * u + 2 * j + 8 + j * (8 * w + 12) := lc_expCost_le fun i hi => by
    rw [← expZ_eq_expSeq]; exact hTw i hi.le
  have hTc : expZ u ds j ≤ w := hTw j le_rfl
  have hNWR : NW * rowsAt R₀ j ≤
      NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    Nat.mul_le_mul_left NW (hF.hRV.trans (Nat.le_add_right _ _))
  have hNWV : NW * (rowsAt R₀ j * 2 ^ n * (r * w)) ≤
      NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    Nat.mul_le_mul_left NW (Nat.le_add_right _ _)
  have hNW1 : NW ≤ NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    Nat.le_mul_of_pos_right _ (by have := hF.hV1; omega)
  have h1 := Nat.mul_le_mul_left (factorCount (program ds)) hcf
  have h2 := Nat.mul_le_mul_left (gateCount (program ds)) hgate
  have h3 := Nat.mul_le_mul_left (Fintype.card (Wires.Address 25)) hexch
  simp only [layerCost]
  unfold nodeCost lcLin
  have hjw := hF.hjw
  have hun := hF.hun
  have hjle := hF.hjle
  have hnW := hF.hnW
  have hwV := hF.hwV
  generalize Fintype.card (Wires.Address 25) = c25 at *
  generalize factorCount (program ds) = F at *
  generalize gateCount (program ds) = G at *
  generalize rowsAt R₀ j * 2 ^ n * (r * w) = V at *
  generalize rowsAt R₀ j * 2 ^ n * n = Wn at *
  have := Nat.zero_le (G * (NW * (V + Wn)))
  have := Nat.zero_le (c25 * (NW * (V + Wn)))
  have := Nat.zero_le (m * c25 * (NW * (V + Wn)))
  have := Nat.zero_le (F * (NW * (V + Wn)))
  have := Nat.zero_le (NW * (V + Wn))
  linarith

/-! ### The leaf -/

/-- **The leaf in natural numbers**: `layerCost … 0 a₀ ≤ 200 u (R₀ 2^n (r w) + R₀ 2^n n)`. -/
theorem lc_leaf_nat (T : ℕ) (ds : ComplexFramedExecution.Directions) {u K ρ R₀ n r w a₀ : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hfit : a₀ + K * u ≤ n) :
    layerCost T ds u K ρ R₀ n r w 0 a₀ ≤
      200 * u * (R₀ * 2 ^ n * (r * w) + R₀ * 2 ^ n * n) := by
  have hK : K ≤ K * u := Nat.le_mul_of_pos_right K hu
  have hu' : u ≤ K * u := Nat.le_mul_of_pos_left u (by omega)
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hP : 1 ≤ R₀ * 2 ^ n := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hrw : 1 ≤ r * w := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hV : R₀ * 2 ^ n ≤ R₀ * 2 ^ n * (r * w) := Nat.le_mul_of_pos_right _ hrw
  have hWn : n ≤ R₀ * 2 ^ n * n := Nat.le_mul_of_pos_left n hP
  have hV1 : 1 ≤ R₀ * 2 ^ n * (r * w) := le_trans hP hV
  simp only [layerCost, leafCost]
  nlinarith

end IntegerMultBounds.MathlibTM2.Cost
