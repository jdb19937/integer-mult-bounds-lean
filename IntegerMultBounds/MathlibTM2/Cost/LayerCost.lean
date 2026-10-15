module

public import IntegerMultBounds.MathlibTM2.Cost.LayerCostNat
public import IntegerMultBounds.MathlibTM2.Layer.Recurrence

/-!
# Step counts of the layer machine in per-volume form

Explicit bounds on the step bound `layerCost T ds u K ρ R₀ n r w j a₀` of the layer procedure
(`Node/LayerProc.lean`), in the per-volume recurrence form of `Layer/Recurrence.lean`.

**Notation.** `V_j = rowsAt R₀ j · 2^n · (r w)` is the volume of a level-`j` array (`lcVol`);
the children of a node of level `j + 1` have volume `V_j = V_{j+1} / NW`. `F = factorCount
(program ds)` is the number of factor instructions, `τ = Parameters.tau`, `k = bits u j = m^j u`
the number of active bits of a child. At a node of level `j + 1` the slot XORs use the key length
`k' = n + rb`, `rb = |sxBits (rowsAt R₀ j)| ≤ log₂ (rowsAt R₀ j) + 1` (`lcKey`, `lc_rb_le`); the
small ratios are `δ = k' / (r w)` (`lcDelta`) and
`E_bad = min 1 (8 (k - 1) / 2^K) · k' · (1 + (k' + 1) / (r w))` (`lcEbad`), and `ε = δ + E_bad`
(`lcEps`). The maximum over offsets runs over the admissible offsets `a₀ + K · bits u j ≤ n`
(`lcMax`); the child offsets `a₀ + s K bits u j`, `s < m`, of an admissible node are admissible,
and every bound below holds uniformly in the admissible offset.

**Constants.** `S = swapConst (T + 12 swapT 6 + 5)` (`lcS`), `c_T = 20 T + 60 swapT 6 + 20000`
(`lcCT`), `lcLin ds = 400 F + 50 G + 8 m c₂₅ + 500 c₂₅ + 500` (`Cost/LayerCostNat.lean`), and
`C₁ = lcC1 T ds = 2 m F (30 S + c_T + 40013) + 4 F + lcLin ds`: the fixed network (`F`, `G`,
`c₂₅`, `m`), the host register count `T` and the vendored constants `swapConst`, `swapT 6`.

**Main results.**
* `lc_leaf_le`: `layerCost … 0 a₀ ≤ 200 u V₀ (1 + n / (r w))`.
* `lc_node_le`:
  `layerCost … (j + 1) a₀ ≤ F · lcMax … j + C₁ V_{j+1} ((1 + δ) (K k)^τ + 1 + δ + E_bad)`.
  The interchanges of `basisCost_le` act on the keyed volume `R 2^n (r w + k') = V_j (1 + δ)`,
  which puts the factor `1 + δ` on the `τ` term; with `δ ≤ 1`, `lc_node_le_of_delta` gives
  `F · lcMax … j + 2 C₁ V_{j+1} ((K k)^τ + 1 + δ + E_bad)`.
* `lc_norm_zero_le`, `lc_norm_succ_le`, `lc_norm_succ_le_eps`: the normalized cost
  `G j = lcMax … j / V_j` (`lcNorm`) has `G 0 ≤ 200 u (1 + n / (r w))` and
  `G (j + 1) ≤ (F / NW) G j + C₁ (1 + ε) ((K m^j u)^τ + 1)`.
* `lc_eps_le_one`: `ε ≤ 1` at an admissible node when `2 (k' + 1) ≤ r w` and `24 n k' ≤ 2^K`.
* `lc_pieceCost`: for a cutoff `m^j₀ ≤ d^β ≤ m^(j₀+1)`, `n ≤ r w`, the child exponents in the
  word and `ε ≤ 1` at the admissible nodes, the normalized piece costs satisfy
  `Recurrence.PieceCost m (F / NW) τ β 400 (2 C₁) d K`; `lc_closed` is
  `Recurrence.recurrence_closed` for one leaf size.

**Basis changes.** A factor with a pivot makes two basis changes of at most `m` slot XORs each
(`lc_basisCostN_le`). A slot XOR costs at most `lcBt` (`lc_basisCost_le`): `basisCost_le`, with
the exceptional addresses of margin `1` bounded by `card_bad_le`,
`|Bad| ≤ min 1 (8 (k - 1) / 2^K) · R 2^n` (`lc_sxBad_le`). Against the volume (`lcBt_le_vol`),
`lcBt ≤ V_j (30 S (1 + δ) (K k)^τ + 20000 (2 + δ) + 13 E_bad + c_T)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Networks

/-! ### The slot XORs of a basis change -/

open IntegerMultBounds.MathlibTM2.Layer.PackedXor in
/-- The exceptional addresses of a slot XOR: `|Bad| ≤ min 1 (8 (k - 1) / 2^K) · M`. -/
lemma lc_sxBad_le {d : SxD} (hv : d.Valid) :
    (sxBad d : ℝ) ≤ min 1 (8 * ((d.k - 1 : ℕ) : ℝ) / 2 ^ d.K) * (d.M : ℝ) := by
  have h := card_bad_le d.K d.ρ d.L d.N₀ d.N₁ d.N₂ d.N₃ d.k 1 hv.hρ
    (by rw [hv.hLK, Nat.mul_comm]) hv.hk
  have hc : Nat.card (Addr d.N₀ d.N₁ d.N₂ d.N₃ d.L) = d.M := by
    rw [Nat.card_congr (rankEquiv d.N₀ d.N₁ d.N₂ d.N₃ d.L), Nat.card_eq_fintype_card,
      Fintype.card_fin, SxD.rect_eq hv]
  rw [hc] at h
  unfold sxBad
  simpa using h

/-- The bound of one slot XOR of a basis change: `basisCost_le` with `lc_sxBad_le`. -/
noncomputable def lcBt (T K L k R n rw : ℕ) : ℝ :=
  30 * swapConst * ((T + 12 * IntegerMultBounds.MathlibTM2.Host.swapT 6 + 5 : ℕ) : ℝ) *
      ((R * 2 ^ n * (rw + (n + (sxBits R).length)) : ℕ) : ℝ) *
        ((max 1 L : ℕ) : ℝ) ^ Parameters.tau +
    ((20000 * (R * 2 ^ n * (rw + (n + (sxBits R).length) + 1)) : ℕ) : ℝ) +
    13 * min 1 (8 * ((k - 1 : ℕ) : ℝ) / 2 ^ K) * ((R * 2 ^ n : ℕ) : ℝ) *
      ((n + (sxBits R).length : ℕ) : ℝ) * ((rw + (n + (sxBits R).length) + 1 : ℕ) : ℝ) +
    ((20 * T + 60 * IntegerMultBounds.MathlibTM2.Host.swapT 6 + 20000 : ℕ) : ℝ)

lemma lcBt_nonneg (T K L k R n rw : ℕ) : 0 ≤ lcBt T K L k R n rw := by
  have := swapConst_pos
  have hmin : 0 ≤ min (1 : ℝ) (8 * ((k - 1 : ℕ) : ℝ) / 2 ^ K) := le_min zero_le_one (by positivity)
  unfold lcBt
  positivity

/-- One slot XOR of a basis change costs at most `lcBt`. -/
lemma lc_basisCost_le {a₀ K ρ k L R n rw : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k)
    (hR : 1 ≤ R) (hrw : 1 ≤ rw) (hfit : a₀ + m * L ≤ n) {j j' : Fin m} (hj' : j' ≠ j) (T : ℕ) :
    basisCost T (basisData a₀ K ρ L R n rw k j j') ≤ lcBt T K L k R n rw := by
  obtain ⟨hz1, hz2⟩ := basisZ_ne j j'
  have hfit' : a₀ + (sxPos j j' (basisZ j j') 0 + 1) * L ≤ n :=
    le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right L (sxPos_lt_m 0)) a₀) hfit
  have hv : (basisData a₀ K ρ L R n rw k j j').Valid :=
    ⟨hρ, hLK, hk, hR, hrw, fun h => hj' (Fin.ext h).symm, fun h => hz1 (Fin.ext h).symm,
      fun h => hz2 (Fin.ext h).symm, hfit'⟩
  have hb := basisCost_le hρ hLK hk hR hrw hfit hj' T
  have hbad := lc_sxBad_le hv
  have hM : (basisData a₀ K ρ L R n rw k j j').M = R * 2 ^ n := rfl
  have hk' : (basisData a₀ K ρ L R n rw k j j').k = k := rfl
  have hK' : (basisData a₀ K ρ L R n rw k j j').K = K := rfl
  rw [hM, hk', hK'] at hbad
  refine hb.trans ?_
  unfold lcBt
  generalize IntegerMultBounds.MathlibTM2.Host.swapT 6 = sT at hb ⊢
  generalize sxBad (basisData a₀ K ρ L R n rw k j j') = bad at hb hbad ⊢
  push_cast at hb hbad ⊢
  have hkk : (0 : ℝ) ≤ ((n : ℝ) + ((sxBits R).length : ℝ)) *
      ((rw : ℝ) + ((n : ℝ) + ((sxBits R).length : ℝ)) + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hbad hkk]

/-- A basis change costs at most `⌈m · lcBt + 1⌉`. -/
lemma lc_basisCostN_le {a₀ K ρ k L R n rw : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k)
    (hR : 1 ≤ R) (hrw : 1 ≤ rw) (hfit : a₀ + m * L ≤ n) (T : ℕ) (vv : BinaryWalsh.Address m)
    (s : Fin m) :
    basisCostN T a₀ K ρ L R n rw k vv s ≤ ⌈(m : ℝ) * lcBt T K L k R n rw + 1⌉₊ := by
  unfold basisCostN
  apply Nat.ceil_mono
  have hsum := List.sum_le_length_nsmul ((basisTargets vv s).map fun j' =>
      basisCost T (basisData a₀ K ρ L R n rw k s j')) (lcBt T K L k R n rw) (by
    intro x hx
    obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hx
    exact lc_basisCost_le hρ hLK hk hR hrw hfit (mem_basisTargets.1 hj').2 T)
  rw [List.length_map, nsmul_eq_mul] at hsum
  have hlen : ((basisTargets vv s).length : ℝ) ≤ m := by
    have : (basisTargets vv s).length ≤ m := by
      unfold basisTargets
      exact (List.length_filter_le _ _).trans (List.length_finRange).le
    exact_mod_cast this
  have := mul_le_mul_of_nonneg_right hlen (lcBt_nonneg T K L k R n rw)
  linarith

/-- `⌈x + 1⌉ ≤ x + 2`. -/
lemma lc_ceil_le {x : ℝ} (hx : 0 ≤ x) : ((⌈x + 1⌉₊ : ℕ) : ℝ) ≤ x + 2 := by
  have := Nat.ceil_lt_add_one (show 0 ≤ x + 1 by linarith)
  linarith

/-- The key length `k' = n + rb` of the slot XORs at a node of level `j + 1`. -/
noncomputable def lcKey (R₀ n j : ℕ) : ℕ := n + (sxBits (rowsAt R₀ j)).length

/-- `δ = k' / (r w)`. -/
noncomputable def lcDelta (R₀ n r w j : ℕ) : ℝ := (lcKey R₀ n j : ℝ) / ((r * w : ℕ) : ℝ)

/-- The density of exceptional addresses, `min 1 (8 (k - 1) / 2^K)` (margin `1`). -/
noncomputable def lcBad (u K j : ℕ) : ℝ := min 1 (8 * ((bits u j - 1 : ℕ) : ℝ) / 2 ^ K)

/-- The repair ratio `E_bad = min 1 (8 (k - 1)/2^K) · k' · (1 + (k' + 1)/(r w))`. -/
noncomputable def lcEbad (u K R₀ n r w j : ℕ) : ℝ :=
  lcBad u K j * lcKey R₀ n j * (1 + ((lcKey R₀ n j : ℝ) + 1) / ((r * w : ℕ) : ℝ))

lemma lcBad_nonneg (u K j : ℕ) : 0 ≤ lcBad u K j :=
  le_min zero_le_one (by positivity)

lemma lcDelta_nonneg (R₀ n r w j : ℕ) : 0 ≤ lcDelta R₀ n r w j := by
  unfold lcDelta; positivity

lemma lcEbad_nonneg (u K R₀ n r w j : ℕ) : 0 ≤ lcEbad u K R₀ n r w j := by
  have := lcBad_nonneg u K j
  unfold lcEbad; positivity

/-- The interchange factor `S = C (T + 12 t + 5)`. -/
noncomputable def lcS (T : ℕ) : ℝ := swapConst * ((T + 12 * IntegerMultBounds.MathlibTM2.Host.swapT 6 + 5 : ℕ) : ℝ)

/-- The additive constant of a slot XOR, `20 T + 60 t + 20000`. -/
noncomputable def lcCT (T : ℕ) : ℕ := 20 * T + 60 * IntegerMultBounds.MathlibTM2.Host.swapT 6 + 20000

lemma lcS_nonneg (T : ℕ) : 0 ≤ lcS T := by
  have := swapConst_pos; unfold lcS; positivity

/-- `lcBt` against the volume `V_j = R 2^n (r w)` of a child. -/
lemma lcBt_le_vol (T : ℕ) {u K R₀ n r w j : ℕ} (hu : 1 ≤ u) (hK : 1 ≤ K) (hr : 1 ≤ r)
    (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) :
    lcBt T K (K * bits u j) (bits u j) (rowsAt R₀ j) n (r * w) ≤
      ((rowsAt R₀ j * 2 ^ n * (r * w) : ℕ) : ℝ) *
        (30 * lcS T * (1 + lcDelta R₀ n r w j) * ((K * bits u j : ℕ) : ℝ) ^ Parameters.tau +
          20000 * (2 + lcDelta R₀ n r w j) + 13 * lcEbad u K R₀ n r w j + (lcCT T : ℝ)) := by
  have hR : 1 ≤ rowsAt R₀ j := rowsAt_pos hR₀ j
  have hk : 1 ≤ bits u j := bits_pos hu j
  have hL : max 1 (K * bits u j) = K * bits u j :=
    max_eq_right (Nat.one_le_iff_ne_zero.2 (by positivity))
  unfold lcBt lcDelta lcEbad lcBad lcS lcCT
  rw [hL]
  have hkey : (n : ℝ) + ((sxBits (rowsAt R₀ j)).length : ℝ) = (lcKey R₀ n j : ℝ) := by
    unfold lcKey; push_cast; ring
  generalize IntegerMultBounds.MathlibTM2.Host.swapT 6 = sT
  push_cast
  rw [hkey]
  set P : ℝ := (rowsAt R₀ j : ℝ) * 2 ^ n with hP
  set q : ℝ := (r : ℝ) * w with hq
  set kk : ℝ := (lcKey R₀ n j : ℝ)
  set β : ℝ := min 1 (8 * ((bits u j - 1 : ℕ) : ℝ) / 2 ^ K)
  set Lτ : ℝ := ((K : ℝ) * (bits u j : ℝ)) ^ Parameters.tau
  have hP1 : 1 ≤ P := by
    have h1 : (1 : ℝ) ≤ rowsAt R₀ j := by exact_mod_cast hR
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hq1 : 1 ≤ q := by
    have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have h2 : (1 : ℝ) ≤ w := by exact_mod_cast hw
    nlinarith
  have hkk : 0 ≤ kk := by positivity
  have hβ : 0 ≤ β := le_min zero_le_one (by positivity)
  have hLτ : 0 ≤ Lτ := by positivity
  have hS : 0 ≤ swapConst * ((T : ℝ) + 12 * sT + 5) := by have := swapConst_pos; positivity
  have hq0 : q ≠ 0 := by linarith
  have e1 : P * (q + kk) = P * q * (1 + kk / q) := by field_simp
  have e2 : P * (q + kk + 1) ≤ P * q * (2 + kk / q) := by
    have : P * q * (2 + kk / q) = P * (q + kk + 1) + P * (q - 1) := by field_simp; ring
    nlinarith
  have e3 : P * kk * (q + kk + 1) = P * q * (kk * (1 + (kk + 1) / q)) := by field_simp; ring
  have e4 : (20 * (T : ℝ) + 60 * sT + 20000) ≤ P * q * (20 * (T : ℝ) + 60 * sT + 20000) := by
    have : 1 ≤ P * q := by nlinarith
    have h0 : 0 ≤ 20 * (T : ℝ) + 60 * sT + 20000 := by positivity
    nlinarith
  have e5 : 30 * swapConst * ((T : ℝ) + 12 * sT + 5) * (P * (q + kk)) * Lτ =
      P * q * (30 * (swapConst * ((T : ℝ) + 12 * sT + 5)) * (1 + kk / q) * Lτ) := by
    rw [e1]; ring
  have e6 : 13 * β * P * kk * (q + kk + 1) = P * q * (13 * (β * kk * (1 + (kk + 1) / q))) := by
    rw [show 13 * β * P * kk * (q + kk + 1) = 13 * β * (P * kk * (q + kk + 1)) by ring, e3]; ring
  rw [e5, e6]
  nlinarith [e2, e4]

/-! ### The leaf -/

/-- The volume of a level-`j` array: `rowsAt R₀ j · 2^n` records of `r w` symbols. -/
noncomputable def lcVol (R₀ n r w j : ℕ) : ℕ := rowsAt R₀ j * 2 ^ n * (r * w)

/-- **The leaf**: `layerCost … 0 a₀ ≤ 200 u V₀ (1 + n / (r w))`. -/
theorem lc_leaf_le (T : ℕ) (ds : ComplexFramedExecution.Directions) {u K ρ R₀ n r w a₀ : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hfit : a₀ + K * bits u 0 ≤ n) :
    (layerCost T ds u K ρ R₀ n r w 0 a₀ : ℝ) ≤
      200 * u * (lcVol R₀ n r w 0 : ℝ) * (1 + (n : ℝ) / ((r * w : ℕ) : ℝ)) := by
  have h := lc_leaf_nat T ds hu hr hw hR₀ hρ hfit
  have hq : (0 : ℝ) < ((r * w : ℕ) : ℝ) := by
    have : 0 < r * w := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have e : 200 * (u : ℝ) * (lcVol R₀ n r w 0 : ℝ) * (1 + (n : ℝ) / ((r * w : ℕ) : ℝ)) =
      ((200 * u * (R₀ * 2 ^ n * (r * w) + R₀ * 2 ^ n * n) : ℕ) : ℝ) := by
    unfold lcVol
    simp only [rowsAt]
    push_cast
    field_simp
  rw [e]
  exact_mod_cast h

/-! ### The largest cost over admissible offsets -/

/-- The largest `layerCost … j a₀` over the admissible offsets `a₀ + K · bits u j ≤ n`. -/
noncomputable def lcMax (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (u K ρ R₀ n r w j : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun a => a + K * bits u j ≤ n).sup
    (layerCost T ds u K ρ R₀ n r w j)

/-- An admissible offset costs at most `lcMax`. -/
lemma lc_le_max (T : ℕ) (ds : ComplexFramedExecution.Directions) {u K ρ R₀ n r w j a : ℕ}
    (h : a + K * bits u j ≤ n) :
    layerCost T ds u K ρ R₀ n r w j a ≤ lcMax T ds u K ρ R₀ n r w j :=
  Finset.le_sup (f := layerCost T ds u K ρ R₀ n r w j)
    (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h⟩)

/-- `lcMax` is at most every real bound of the admissible offsets. -/
lemma lc_max_le_real (T : ℕ) (ds : ComplexFramedExecution.Directions) {u K ρ R₀ n r w j : ℕ}
    {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ a, a + K * bits u j ≤ n → (layerCost T ds u K ρ R₀ n r w j a : ℝ) ≤ X) :
    (lcMax T ds u K ρ R₀ n r w j : ℝ) ≤ X := by
  unfold lcMax
  set s := (Finset.range (n + 1)).filter fun a => a + K * bits u j ≤ n
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs, Finset.sup_empty]; simpa using hX
  · obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup s hs (layerCost T ds u K ρ R₀ n r w j)
    rw [he]
    exact h a (Finset.mem_filter.1 ha).2

/-- Without admissible offsets, `lcMax = 0`. -/
lemma lc_max_eq_zero (T : ℕ) (ds : ComplexFramedExecution.Directions) {u K ρ R₀ n r w j : ℕ}
    (h : n < K * bits u j) : lcMax T ds u K ρ R₀ n r w j = 0 := by
  unfold lcMax
  convert Finset.sup_empty
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
  intro _ ha
  omega

/-! ### The node -/

/-- The node constant `C₁ = 2 m F (30 S + c_T + 40013) + 4 F + lcLin`. -/
noncomputable def lcC1 (T : ℕ) (ds : ComplexFramedExecution.Directions) : ℝ :=
  2 * m * factorCount (program ds) * (30 * lcS T + lcCT T + 40013) +
    4 * factorCount (program ds) + lcLin ds

lemma lcC1_nonneg (T : ℕ) (ds : ComplexFramedExecution.Directions) : 0 ≤ lcC1 T ds := by
  have := lcS_nonneg T
  unfold lcC1; positivity

/-- The real algebra of the node bound: `lc_node_nat` with the basis changes within
`m · lcBt + 2` steps, `lcBt_le_vol` and `W ≤ V δ`. -/
lemma lc_node_alg {Lc M B Bt F NW V Wn δ E Lτ mm S cT Lin : ℝ}
    (hF : 0 ≤ F) (hmm : 0 ≤ mm) (hS : 0 ≤ S) (hcT : 0 ≤ cT) (hLin : 0 ≤ Lin)
    (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hLτ : 0 ≤ Lτ) (hNW : 1 ≤ NW) (hV : 1 ≤ V)
    (hN : Lc ≤ F * (M + 2 * B) + Lin * (NW * (V + Wn))) (hB : B ≤ mm * Bt + 2)
    (hBt : Bt ≤ V * (30 * S * (1 + δ) * Lτ + 20000 * (2 + δ) + 13 * E + cT))
    (hWn : Wn ≤ V * δ) :
    Lc ≤ F * M + (2 * mm * F * (30 * S + cT + 40013) + 4 * F + Lin) * (NW * V) *
      ((1 + δ) * Lτ + 1 + δ + E) := by
  set Q : ℝ := (1 + δ) * Lτ + 1 + δ + E with hQ
  have hQ1 : 1 + δ ≤ Q := by nlinarith
  have hQτ : (1 + δ) * Lτ ≤ Q := by linarith
  have hEQ : E ≤ Q := by nlinarith
  have hinner : 30 * S * (1 + δ) * Lτ + 20000 * (2 + δ) + 13 * E + cT ≤
      (30 * S + cT + 40013) * Q := by
    have h1 : 30 * S * (1 + δ) * Lτ ≤ 30 * S * Q := by
      rw [mul_assoc (30 * S)]; exact mul_le_mul_of_nonneg_left hQτ (by positivity)
    have h2 : cT ≤ cT * Q := by nlinarith
    nlinarith
  have hVV : V ≤ NW * V := by nlinarith
  have hVQ : 1 ≤ NW * V * Q := by
    have : 1 ≤ NW * V := by nlinarith
    nlinarith
  have hC0 : 0 ≤ (30 * S + cT + 40013) * Q := by positivity
  have hBt' : mm * Bt ≤ mm * (NW * V) * ((30 * S + cT + 40013) * Q) := by
    calc mm * Bt ≤ mm * (V * ((30 * S + cT + 40013) * Q)) :=
          mul_le_mul_of_nonneg_left (hBt.trans (mul_le_mul_of_nonneg_left hinner (by linarith))) hmm
      _ ≤ mm * (NW * V * ((30 * S + cT + 40013) * Q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hVV hC0) hmm
      _ = _ := by ring
  have hbasis : 2 * F * B ≤
      2 * mm * F * (30 * S + cT + 40013) * (NW * V * Q) + 4 * F * (NW * V * Q) := by
    have h4 : 2 * F * 2 ≤ 4 * F * (NW * V * Q) := by nlinarith
    have h5 : 2 * F * B ≤ 2 * F * (mm * Bt) + 2 * F * 2 := by nlinarith
    have h6 : 2 * F * (mm * Bt) ≤ 2 * F * (mm * (NW * V) * ((30 * S + cT + 40013) * Q)) :=
      mul_le_mul_of_nonneg_left hBt' (by positivity)
    nlinarith
  have hlin : Lin * (NW * (V + Wn)) ≤ Lin * (NW * V * Q) := by
    apply mul_le_mul_of_nonneg_left _ hLin
    have : V + Wn ≤ V * Q := by nlinarith
    calc NW * (V + Wn) ≤ NW * (V * Q) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = _ := by ring
  calc Lc ≤ F * M + 2 * F * B + Lin * (NW * (V + Wn)) := by linarith
    _ ≤ F * M + (2 * mm * F * (30 * S + cT + 40013) * (NW * V * Q) + 4 * F * (NW * V * Q)) +
          Lin * (NW * V * Q) := by linarith
    _ = _ := by ring

/-- **The node.** At an admissible offset (`a₀ + K · bits u (j + 1) ≤ n`), with the child
exponents in the word, `layerCost … (j + 1) a₀ ≤ F · lcMax … j +
C₁ V_{j+1} ((1 + δ) (K bits u j)^τ + 1 + δ + E_bad)`. -/
theorem lc_node_le (T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w j a₀ : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hfit : a₀ + K * bits u (j + 1) ≤ n) (hTw : ∀ i ≤ j, expZ u ds i ≤ w) :
    (layerCost T ds u K ρ R₀ n r w (j + 1) a₀ : ℝ) ≤
      factorCount (program ds) * (lcMax T ds u K ρ R₀ n r w j : ℝ) +
        lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
          ((1 + lcDelta R₀ n r w j) * ((K * bits u j : ℕ) : ℝ) ^ Parameters.tau + 1 +
            lcDelta R₀ n r w j + lcEbad u K R₀ n r w j) := by
  have hK : 1 ≤ K := by omega
  have hR : 1 ≤ rowsAt R₀ j := rowsAt_pos hR₀ j
  have hrw : 1 ≤ r * w := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hceil := lc_ceil_le (mul_nonneg (Nat.cast_nonneg m)
    (lcBt_nonneg T K (K * bits u j) (bits u j) (rowsAt R₀ j) n (r * w)))
  have hBv := lcBt_le_vol T (j := j) hu hK hr hw hR₀ (n := n)
  have hNW : (1 : ℝ) ≤ ((NW : ℕ) : ℝ) := by exact_mod_cast one_le_NW
  have hV1 : (1 : ℝ) ≤ ((rowsAt R₀ j * 2 ^ n * (r * w) : ℕ) : ℝ) := by
    have : 1 ≤ rowsAt R₀ j * 2 ^ n * (r * w) :=
      Nat.mul_le_mul (Nat.mul_le_mul hR h2n) hrw
    exact_mod_cast this
  have hVol : (lcVol R₀ n r w (j + 1) : ℝ) =
      ((NW : ℕ) : ℝ) * ((rowsAt R₀ j * 2 ^ n * (r * w) : ℕ) : ℝ) := by
    rw [lcVol, show rowsAt R₀ (j + 1) = NW * rowsAt R₀ j from rfl]
    push_cast; ring
  have hWnδ : ((rowsAt R₀ j * 2 ^ n * n : ℕ) : ℝ) ≤
      ((rowsAt R₀ j * 2 ^ n * (r * w) : ℕ) : ℝ) * lcDelta R₀ n r w j := by
    have hq : (0 : ℝ) < ((r * w : ℕ) : ℝ) := by exact_mod_cast hrw
    have hkey : n ≤ lcKey R₀ n j := Nat.le_add_right _ _
    have e : ((rowsAt R₀ j * 2 ^ n * (r * w) : ℕ) : ℝ) * lcDelta R₀ n r w j =
        ((rowsAt R₀ j * 2 ^ n : ℕ) : ℝ) * (lcKey R₀ n j : ℝ) := by
      unfold lcDelta
      rw [Nat.cast_mul (rowsAt R₀ j * 2 ^ n)]
      field_simp
    rw [e, Nat.cast_mul (rowsAt R₀ j * 2 ^ n)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkey) (Nat.cast_nonneg _)
  have hB : ∀ (vv : BinaryWalsh.Address m) (s : Fin m),
      basisCostN T a₀ K ρ (K * bits u j) (rowsAt R₀ j) n (r * w) (bits u j) vv s ≤
        ⌈(m : ℝ) * lcBt T K (K * bits u j) (bits u j) (rowsAt R₀ j) n (r * w) + 1⌉₊ :=
    fun vv s => lc_basisCostN_le hρ rfl (bits_pos hu j) hR hrw
      (by rw [show bits u (j + 1) = m * bits u j from rfl] at hfit; linarith) T vv s
  have hM : ∀ s < m, layerCost T ds u K ρ R₀ n r w j (a₀ + s * (K * bits u j)) ≤
      lcMax T ds u K ρ R₀ n r w j := fun s hs => by
    apply lc_le_max
    have : (s + 1) * (K * bits u j) ≤ m * (K * bits u j) := Nat.mul_le_mul_right _ hs
    rw [show bits u (j + 1) = m * bits u j from rfl] at hfit
    nlinarith
  have hN := lc_node_nat T ds hu hr hw hR₀ hρ hfit hTw hM hB
  have hNr : (layerCost T ds u K ρ R₀ n r w (j + 1) a₀ : ℝ) ≤
      (factorCount (program ds) : ℝ) * ((lcMax T ds u K ρ R₀ n r w j : ℝ) +
        2 * (⌈(m : ℝ) * lcBt T K (K * bits u j) (bits u j) (rowsAt R₀ j) n (r * w) + 1⌉₊ : ℕ)) +
        (lcLin ds : ℝ) * ((NW : ℕ) * (((rowsAt R₀ j * 2 ^ n * (r * w)) : ℕ) +
        ((rowsAt R₀ j * 2 ^ n * n : ℕ) : ℝ))) := by
    exact_mod_cast hN
  rw [hVol]
  unfold lcC1
  exact lc_node_alg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (lcS_nonneg T)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (lcDelta_nonneg _ _ _ _ _)
    (lcEbad_nonneg _ _ _ _ _ _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hNW hV1
    hNr hceil hBv hWnδ

/-! ### The normalized recurrence -/

lemma lcVol_pos {R₀ n r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (j : ℕ) :
    (0 : ℝ) < (lcVol R₀ n r w j : ℝ) := by
  have : 0 < lcVol R₀ n r w j :=
    Nat.mul_pos (Nat.mul_pos (rowsAt_pos hR₀ j) (Nat.two_pow_pos n)) (Nat.mul_pos hr hw)
  exact_mod_cast this

/-- The normalized cost `G j = lcMax … j / V_j`. -/
noncomputable def lcNorm (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (u K ρ R₀ n r w j : ℕ) : ℝ :=
  (lcMax T ds u K ρ R₀ n r w j : ℝ) / (lcVol R₀ n r w j : ℝ)

lemma lcNorm_nonneg (T : ℕ) (ds : ComplexFramedExecution.Directions) (u K ρ R₀ n r w j : ℕ) :
    0 ≤ lcNorm T ds u K ρ R₀ n r w j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The small ratios of a node of level `j + 1`: `ε = δ + E_bad`. -/
noncomputable def lcEps (u K R₀ n r w j : ℕ) : ℝ := lcDelta R₀ n r w j + lcEbad u K R₀ n r w j

/-- The width of the active region of a child, `K bits u j = K m^j u`. -/
lemma lc_cast_Kbits (K u j : ℕ) : ((K * bits u j : ℕ) : ℝ) = (K : ℝ) * (m : ℝ) ^ j * u := by
  rw [lc_bits_eq]; push_cast; ring

lemma lc_Q_nonneg (u K R₀ n r w j : ℕ) :
    0 ≤ (1 + lcDelta R₀ n r w j) * ((K : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau +
      1 + lcDelta R₀ n r w j + lcEbad u K R₀ n r w j := by
  have := lcDelta_nonneg R₀ n r w j
  have := lcEbad_nonneg u K R₀ n r w j
  have : 0 ≤ ((K : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau :=
    Real.rpow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg K) (pow_nonneg (Nat.cast_nonneg m) j))
      (Nat.cast_nonneg u)) _
  positivity

lemma lc_div_aux {M' M C Q F nw V : ℝ} (hnw : 0 < nw) (hV : 0 < V)
    (h : M' ≤ F * M + C * (nw * V) * Q) : M' / (nw * V) ≤ (F / nw) * (M / V) + C * Q := by
  rw [div_le_iff₀ (mul_pos hnw hV)]
  calc M' ≤ F * M + C * (nw * V) * Q := h
    _ = _ := by field_simp

/-- **The normalized node recurrence**:
`G (j + 1) ≤ (F / NW) G j + C₁ ((1 + δ) (K m^j u)^τ + 1 + δ + E_bad)`. A level without admissible
offsets has `G (j + 1) = 0`, so the child exponents need to fit the word only at admissible
levels. -/
theorem lc_norm_succ_le (T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w j : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hTw : K * bits u (j + 1) ≤ n → ∀ i ≤ j, expZ u ds i ≤ w) :
    lcNorm T ds u K ρ R₀ n r w (j + 1) ≤
      ((factorCount (program ds) : ℝ) / NW) * lcNorm T ds u K ρ R₀ n r w j +
        lcC1 T ds * ((1 + lcDelta R₀ n r w j) * ((K : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau +
          1 + lcDelta R₀ n r w j + lcEbad u K R₀ n r w j) := by
  have hV := lcVol_pos (n := n) hr hw hR₀ j
  have hV' := lcVol_pos (n := n) hr hw hR₀ (j + 1)
  have hNW : (0 : ℝ) < ((NW : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne NW))
  have hQ := lc_Q_nonneg u K R₀ n r w j
  have hrhs : 0 ≤ ((factorCount (program ds) : ℝ) / NW) * lcNorm T ds u K ρ R₀ n r w j +
      lcC1 T ds * ((1 + lcDelta R₀ n r w j) * ((K : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau +
        1 + lcDelta R₀ n r w j + lcEbad u K R₀ n r w j) :=
    add_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (lcNorm_nonneg _ _ _ _ _ _ _ _ _ _)) (mul_nonneg (lcC1_nonneg T ds) hQ)
  have hVV : (lcVol R₀ n r w (j + 1) : ℝ) = ((NW : ℕ) : ℝ) * (lcVol R₀ n r w j : ℝ) := by
    rw [lcVol, lcVol, show rowsAt R₀ (j + 1) = NW * rowsAt R₀ j from rfl, Nat.mul_assoc NW,
      Nat.mul_assoc NW, Nat.cast_mul]
  by_cases hadm : K * bits u (j + 1) ≤ n
  · have key : (lcMax T ds u K ρ R₀ n r w (j + 1) : ℝ) ≤
        factorCount (program ds) * (lcMax T ds u K ρ R₀ n r w j : ℝ) +
          lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
            ((1 + lcDelta R₀ n r w j) * ((K * bits u j : ℕ) : ℝ) ^ Parameters.tau + 1 +
              lcDelta R₀ n r w j + lcEbad u K R₀ n r w j) := by
      refine lc_max_le_real T ds ?_ fun a ha => lc_node_le T ds hu hr hw hR₀ hρ ha (hTw hadm)
      rw [lc_cast_Kbits]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg (lcC1_nonneg T ds) hV'.le) hQ)
    rw [lc_cast_Kbits, hVV] at key
    unfold lcNorm
    rw [hVV]
    exact lc_div_aux hNW hV key
  · rw [lcNorm, lc_max_eq_zero T ds (by omega), Nat.cast_zero, zero_div]
    exact hrhs

/-- The normalized node recurrence with `ε = δ + E_bad`:
`G (j + 1) ≤ (F / NW) G j + C₁ (1 + ε) ((K m^j u)^τ + 1)`. -/
theorem lc_norm_succ_le_eps (T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w j : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hTw : K * bits u (j + 1) ≤ n → ∀ i ≤ j, expZ u ds i ≤ w) :
    lcNorm T ds u K ρ R₀ n r w (j + 1) ≤
      ((factorCount (program ds) : ℝ) / NW) * lcNorm T ds u K ρ R₀ n r w j +
        lcC1 T ds * (1 + lcEps u K R₀ n r w j) *
          (((K : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau + 1) := by
  refine (lc_norm_succ_le T ds hu hr hw hR₀ hρ hTw).trans ?_
  rw [mul_assoc (lcC1 T ds)]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (lcC1_nonneg T ds))
  have hE := lcEbad_nonneg u K R₀ n r w j
  have hL : 0 ≤ ((K : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau :=
    Real.rpow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg K) (pow_nonneg (Nat.cast_nonneg m) j))
      (Nat.cast_nonneg u)) _
  generalize ((K : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau = L at hL ⊢
  unfold lcEps
  nlinarith

/-- **The normalized leaf**: `G 0 ≤ 200 u (1 + n / (r w))`. -/
theorem lc_norm_zero_le (T : ℕ) (ds : ComplexFramedExecution.Directions) {u K ρ R₀ n r w : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K) :
    lcNorm T ds u K ρ R₀ n r w 0 ≤ 200 * u * (1 + (n : ℝ) / ((r * w : ℕ) : ℝ)) := by
  have hV := lcVol_pos (n := n) hr hw hR₀ 0
  have hq : (0 : ℝ) ≤ (n : ℝ) / ((r * w : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  unfold lcNorm
  rw [div_le_iff₀ hV]
  refine lc_max_le_real T ds (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    (by linarith)) hV.le) fun a ha => ?_
  calc (layerCost T ds u K ρ R₀ n r w 0 a : ℝ) ≤ _ := lc_leaf_le T ds hu hr hw hR₀ hρ ha
    _ = _ := by ring

/-! ### When the small ratios are at most `1` -/

/-- The row field has logarithmic width: `rb ≤ log₂ R + 1`. -/
lemma lc_rb_le (R : ℕ) : (sxBits R).length ≤ R.log2 + 1 := by
  have h := GrowingCounterData.canonical_width (sxBits R) (canonical_sxBits R)
  rwa [value_sxBits] at h

/-- **`ε ≤ 1`** at an admissible node of level `j + 1` when `2 (k' + 1) ≤ r w` and
`24 n k' ≤ 2^K`, `k' = n + rb`. -/
theorem lc_eps_le_one {u K R₀ n r w j : ℕ} (hK : 1 ≤ K)
    (hadm : K * bits u (j + 1) ≤ n)
    (h1 : 2 * (lcKey R₀ n j + 1) ≤ r * w) (h2 : 24 * n * lcKey R₀ n j ≤ 2 ^ K) :
    lcEps u K R₀ n r w j ≤ 1 := by
  have hkn : bits u j - 1 ≤ n := by
    have h3 : bits u j ≤ bits u (j + 1) := lc_bits_mono u (Nat.le_succ j)
    have h4 : bits u (j + 1) ≤ K * bits u (j + 1) := Nat.le_mul_of_pos_left _ hK
    omega
  unfold lcEps lcDelta lcEbad lcBad
  have hq1 : (2 : ℝ) * ((lcKey R₀ n j : ℝ) + 1) ≤ ((r * w : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : (24 : ℝ) * n * (lcKey R₀ n j : ℝ) ≤ 2 ^ K := by exact_mod_cast h2
  have hkn' : ((bits u j - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hkn
  have hkk0 : (0 : ℝ) ≤ (lcKey R₀ n j : ℝ) := Nat.cast_nonneg _
  have hP : (0 : ℝ) < 2 ^ K := by positivity
  have hβ : min 1 (8 * ((bits u j - 1 : ℕ) : ℝ) / 2 ^ K) ≤ 8 * (n : ℝ) / 2 ^ K :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_right (by linarith) hP.le)
  have hβ0 : 0 ≤ min 1 (8 * ((bits u j - 1 : ℕ) : ℝ) / 2 ^ K) :=
    le_min zero_le_one (div_nonneg (by positivity) hP.le)
  generalize min 1 (8 * ((bits u j - 1 : ℕ) : ℝ) / 2 ^ K) = β at hβ hβ0 ⊢
  generalize ((r * w : ℕ) : ℝ) = q at hq1 ⊢
  generalize (lcKey R₀ n j : ℝ) = kk at hq1 h2' hkk0 ⊢
  have hq : 0 < q := by linarith
  have hδ : kk / q ≤ 1 / 2 := by rw [div_le_iff₀ hq]; linarith
  have ht : (kk + 1) / q ≤ 1 / 2 := by rw [div_le_iff₀ hq]; linarith
  have ht0 : 0 ≤ (kk + 1) / q := div_nonneg (by linarith) hq.le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hB : 8 * (n : ℝ) / 2 ^ K * kk ≤ 1 / 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hP]; nlinarith
  have hE : β * kk * (1 + (kk + 1) / q) ≤ 1 / 2 := by
    have h1 : β * kk ≤ 8 * (n : ℝ) / 2 ^ K * kk := mul_le_mul_of_nonneg_right hβ hkk0
    have h2 : β * kk * (1 + (kk + 1) / q) ≤ β * kk * (3 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hβ0 hkk0)
    nlinarith
  linarith

/-- The node bound with `(1 + δ)` absorbed (`δ ≤ 1`):
`layerCost … (j + 1) a₀ ≤ F · lcMax … j + 2 C₁ V_{j+1} ((K bits u j)^τ + 1 + δ + E_bad)`. -/
theorem lc_node_le_of_delta (T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w j a₀ : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hfit : a₀ + K * bits u (j + 1) ≤ n) (hTw : ∀ i ≤ j, expZ u ds i ≤ w)
    (hδ : lcDelta R₀ n r w j ≤ 1) :
    (layerCost T ds u K ρ R₀ n r w (j + 1) a₀ : ℝ) ≤
      factorCount (program ds) * (lcMax T ds u K ρ R₀ n r w j : ℝ) +
        2 * lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
          (((K * bits u j : ℕ) : ℝ) ^ Parameters.tau + 1 + lcDelta R₀ n r w j +
            lcEbad u K R₀ n r w j) := by
  refine (lc_node_le T ds hu hr hw hR₀ hρ hfit hTw).trans ?_
  have hδ0 := lcDelta_nonneg R₀ n r w j
  have hE := lcEbad_nonneg u K R₀ n r w j
  have hL : 0 ≤ ((K * bits u j : ℕ) : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCV : 0 ≤ lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) :=
    mul_nonneg (lcC1_nonneg T ds) (Nat.cast_nonneg _)
  generalize ((K * bits u j : ℕ) : ℝ) ^ Parameters.tau = L at hL ⊢
  have h1 : (1 + lcDelta R₀ n r w j) * L + 1 + lcDelta R₀ n r w j + lcEbad u K R₀ n r w j ≤
      2 * (L + 1 + lcDelta R₀ n r w j + lcEbad u K R₀ n r w j) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 hCV
  have h3 : lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
      (2 * (L + 1 + lcDelta R₀ n r w j + lcEbad u K R₀ n r w j)) =
      2 * lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
        (L + 1 + lcDelta R₀ n r w j + lcEbad u K R₀ n r w j) := by ring
  linarith

/-! ### The piece-cost recurrence -/

/-- **`PieceCost` for the layer machine.** Fix the cutoff `m^j₀ ≤ d^β ≤ m^(j₀+1)`. A piece of
`m^j` chunks runs the layer machine with `u = m^(min j j₀)` bits per leaf at level `j - j₀`;
its normalized cost `G j = lcNorm … (m^(min j j₀)) … (j - j₀)` satisfies
`Recurrence.PieceCost m (F / NW) τ β 400 (2 C₁) d K G`, provided `n ≤ r w`, the child
exponents fit the word at every admissible node, and `ε ≤ 1` at every admissible node. -/
theorem lc_pieceCost (T : ℕ) (ds : ComplexFramedExecution.Directions) {K ρ R₀ n r w j₀ : ℕ}
    {d β : ℝ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K) (hn : n ≤ r * w)
    (hj₀ : (m : ℝ) ^ j₀ ≤ d ^ β) (hj₀' : d ^ β ≤ (m : ℝ) ^ (j₀ + 1))
    (hTw : ∀ i, K * bits (m ^ j₀) (i + 1) ≤ n → ∀ i' ≤ i, expZ (m ^ j₀) ds i' ≤ w)
    (hε : ∀ i, K * bits (m ^ j₀) (i + 1) ≤ n → lcEps (m ^ j₀) K R₀ n r w i ≤ 1) :
    Recurrence.PieceCost (m : ℝ) ((factorCount (program ds) : ℝ) / NW) Parameters.tau β 400
      (2 * lcC1 T ds) d K (fun j => lcNorm T ds (m ^ min j j₀) K ρ R₀ n r w (j - j₀)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by norm_num [m])
  have hm0 : 0 < m := by norm_num [m]
  have hq : (n : ℝ) / ((r * w : ℕ) : ℝ) ≤ 1 := by
    have : (0 : ℝ) < ((r * w : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by omega) (by omega)
    rw [div_le_iff₀ this, one_mul]; exact_mod_cast hn
  refine Recurrence.pieceCost_of_cutoff hm1 hj₀ hj₀' ?_ ?_
  · intro j hj
    simp only [min_eq_left hj, Nat.sub_eq_zero_of_le hj]
    have hu : 1 ≤ m ^ j := Nat.one_le_pow _ _ hm0
    refine (lc_norm_zero_le T ds hu hr hw hR₀ hρ).trans ?_
    rw [Nat.cast_pow]
    have : (0 : ℝ) ≤ (m : ℝ) ^ j := pow_nonneg (Nat.cast_nonneg m) j
    generalize (m : ℝ) ^ j = M at this ⊢
    generalize (n : ℝ) / ((r * w : ℕ) : ℝ) = q at hq ⊢
    nlinarith
  · intro j hj
    have e1 : min (j + 1) j₀ = j₀ := min_eq_right (by omega)
    have e2 : min j j₀ = j₀ := min_eq_right hj
    have e3 : j + 1 - j₀ = (j - j₀) + 1 := by omega
    simp only [e1, e2, e3]
    have hu : 1 ≤ m ^ j₀ := Nat.one_le_pow _ _ hm0
    have hG0 := lcNorm_nonneg T ds (m ^ j₀) K ρ R₀ n r w (j - j₀)
    have hC := lcC1_nonneg T ds
    have hτ : 0 ≤ Parameters.tau := by norm_num [Parameters.tau]
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hmono : ((K : ℝ) * (m : ℝ) ^ j) ^ Parameters.tau ≤
        ((K : ℝ) * (m : ℝ) ^ (j + 1)) ^ Parameters.tau :=
      Real.rpow_le_rpow (mul_nonneg hK0 (pow_nonneg (Nat.cast_nonneg m) j))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 (Nat.le_succ j)) hK0) hτ
    have hLj : 0 ≤ ((K : ℝ) * (m : ℝ) ^ j) ^ Parameters.tau :=
      Real.rpow_nonneg (mul_nonneg hK0 (pow_nonneg (Nat.cast_nonneg m) j)) _
    have hrhs : 0 ≤ (factorCount (program ds) : ℝ) / NW *
        lcNorm T ds (m ^ j₀) K ρ R₀ n r w (j - j₀) +
        2 * lcC1 T ds * (((K : ℝ) * (m : ℝ) ^ (j + 1)) ^ Parameters.tau + 1) :=
      add_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hG0)
        (mul_nonneg (mul_nonneg (by norm_num) hC) (by linarith))
    by_cases hadm : K * bits (m ^ j₀) ((j - j₀) + 1) ≤ n
    · have h := lc_norm_succ_le_eps T ds hu hr hw hR₀ hρ (n := n) (j := j - j₀)
        (fun _ => hTw _ hadm)
      have he := hε _ hadm
      have hKL : (K : ℝ) * (m : ℝ) ^ (j - j₀) * ((m ^ j₀ : ℕ) : ℝ) = (K : ℝ) * (m : ℝ) ^ j := by
        push_cast
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
      rw [hKL] at h
      refine h.trans (add_le_add le_rfl ?_)
      have he0 : 0 ≤ lcEps (m ^ j₀) K R₀ n r w (j - j₀) :=
        add_nonneg (lcDelta_nonneg _ _ _ _ _) (lcEbad_nonneg _ _ _ _ _ _ _)
      have h1 : lcC1 T ds * (1 + lcEps (m ^ j₀) K R₀ n r w (j - j₀)) ≤ 2 * lcC1 T ds := by
        nlinarith
      calc lcC1 T ds * (1 + lcEps (m ^ j₀) K R₀ n r w (j - j₀)) *
            (((K : ℝ) * (m : ℝ) ^ j) ^ Parameters.tau + 1)
          ≤ 2 * lcC1 T ds * (((K : ℝ) * (m : ℝ) ^ j) ^ Parameters.tau + 1) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ 2 * lcC1 T ds * (((K : ℝ) * (m : ℝ) ^ (j + 1)) ^ Parameters.tau + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    · rw [lcNorm, lc_max_eq_zero T ds (by omega), Nat.cast_zero, zero_div]
      exact hrhs

/-- **The closed bound** (`Recurrence.recurrence_closed` with `C₀ = 400`, `C₁' = 2 C₁`): for
`τ ≤ λ`, `log_m (F / NW) < λ`, `n ≤ r w`, child exponents in the word and `ε ≤ 1` at every
admissible node, `G j ≤ C (m^j u)^λ K^τ + C (F / NW)^j u`. -/
theorem lc_closed (T : ℕ) (ds : ComplexFramedExecution.Directions) {u K ρ R₀ n r w : ℕ}
    {lam : ℝ} (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hn : n ≤ r * w) (hτl : Parameters.tau ≤ lam)
    (hal : Real.logb (m : ℝ) ((factorCount (program ds) : ℝ) / NW) < lam)
    (hTw : ∀ i, K * bits u (i + 1) ≤ n → ∀ i' ≤ i, expZ u ds i' ≤ w)
    (hε : ∀ i, K * bits u (i + 1) ≤ n → lcEps u K R₀ n r w i ≤ 1) (j : ℕ) :
    lcNorm T ds u K ρ R₀ n r w j ≤
      Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m lam 400 (2 * lcC1 T ds) *
          ((m : ℝ) ^ j * u) ^ lam * (K : ℝ) ^ Parameters.tau +
        Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m lam 400 (2 * lcC1 T ds) *
          ((factorCount (program ds) : ℝ) / NW) ^ j * u := by
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by norm_num [m])
  have hτ : 0 ≤ Parameters.tau := by norm_num [Parameters.tau]
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hq : (n : ℝ) / ((r * w : ℕ) : ℝ) ≤ 1 := by
    have : (0 : ℝ) < ((r * w : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by omega) (by omega)
    rw [div_le_iff₀ this, one_mul]; exact_mod_cast hn
  refine Recurrence.recurrence_closed (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hm1 hτ
    hτl hal hK (by norm_num) (mul_nonneg (by norm_num) (lcC1_nonneg T ds)) hu' ?_ ?_ j
  · refine (lc_norm_zero_le T ds hu hr hw hR₀ hρ).trans ?_
    generalize (n : ℝ) / ((r * w : ℕ) : ℝ) = q at hq ⊢
    nlinarith
  · intro i
    have hG0 := lcNorm_nonneg T ds u K ρ R₀ n r w i
    have hC := lcC1_nonneg T ds
    have hL : 0 ≤ ((K : ℝ) * (m : ℝ) ^ i * u) ^ Parameters.tau :=
      Real.rpow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg K)
        (pow_nonneg (Nat.cast_nonneg m) i)) (Nat.cast_nonneg u)) _
    by_cases hadm : K * bits u (i + 1) ≤ n
    · have h := lc_norm_succ_le_eps T ds hu hr hw hR₀ hρ (n := n) (j := i) (fun _ => hTw _ hadm)
      have he := hε _ hadm
      have he0 : 0 ≤ lcEps u K R₀ n r w i :=
        add_nonneg (lcDelta_nonneg _ _ _ _ _) (lcEbad_nonneg _ _ _ _ _ _ _)
      refine h.trans (add_le_add le_rfl ?_)
      have h1 : lcC1 T ds * (1 + lcEps u K R₀ n r w i) ≤ 2 * lcC1 T ds := by nlinarith
      exact mul_le_mul_of_nonneg_right h1 (by linarith)
    · rw [lcNorm, lc_max_eq_zero T ds (by omega), Nat.cast_zero, zero_div]
      exact add_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hG0)
        (mul_nonneg (mul_nonneg (by norm_num) hC) (by linarith))

end IntegerMultBounds.MathlibTM2.Cost
