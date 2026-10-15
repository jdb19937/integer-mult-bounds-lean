module

public import IntegerMultBounds.MathlibTM2.Cost.LayerCostNat
public import IntegerMultBounds.MathlibTM2.Layer.Recurrence
public import IntegerMultBounds.MathlibTM2.Node.CompactCost
public import IntegerMultBounds.MathlibTM2.Node.CompactBadBound

/-!
# Step counts of the layer machine in per-volume form

Explicit bounds on the step bound `layerCost A T ds u K ρ R₀ n r w Gd j a₀` of the layer
procedure (`Node/LayerProc.lean`), in the per-volume recurrence form of `Layer/Recurrence.lean`.

**Notation.** `V_j = rowsAt R₀ j · 2^n · (r w)` is the volume of a level-`j` array (`lcVol`);
the children of a node of level `j + 1` have volume `V_j = V_{j+1} / NW`. `F = factorCount
(program ds)` is the number of factor instructions, `τ = Parameters.tau`, `k = bits u j = m^j u`
the number of active bits of a child, `Gd` the digit width of the compact slot XORs, whose
control fields have width `H = (k - 1) Gd`. At a node of level `j + 1` the slot XORs use the
key length `k' = n + rb`, `rb = |sxBits (rowsAt R₀ j)| ≤ log₂ (rowsAt R₀ j) + 1` (`lcKey`,
`lc_rb_le`); the small ratios are `δ = k' / (r w)` (`lcDelta`) and
`E_bad = min 1 ((k - 1) (2 / 2^Gd + 8 · 2^Gd / 2^K)) · k' · (1 + (k' + 1) / (r w))` (`lcEbad`),
and `ε = δ + E_bad` (`lcEps`).

**Admissible offsets** (`lcAdm`). At level `j` the offset `a` is admissible when the active bits
fit, `a + K · bits u j ≤ n`, and, at a node (`1 ≤ j`), a control field of the children fits
below the slots and three fit above: `(bits u (j - 1) - 1) Gd ≤ a` and
`a + K · bits u j + 3 (bits u (j - 1) - 1) Gd ≤ n`. The maximum over offsets (`lcMax`) runs
over the admissible offsets; the child offsets `a₀ + s K bits u j`, `s < m`, of an admissible
node are admissible, and every bound below holds uniformly in the admissible offset.

**Constants.** `S = swapConst (T + 12 swapT 6 + 5)` (`lcS`), `c_T = 24 T + 72 swapT 6 + 400000`
(`lcCT`), `lcLin ds = 400 F + 50 G + 8 m c₂₅ + 500 c₂₅ + 500` (`Cost/LayerCostNat.lean`), and
`C₁ = lcC1 T ds = 2 m F (36 S + c_T + 4000013) + 404 F + lcLin ds`: the fixed network (`F`, `G`,
`c₂₅`, `m`), the host register count `T` and the vendored constants `swapConst`, `swapT 6`.

**Main results.**
* `lc_leaf_le`: `layerCost … 0 a₀ ≤ 200 u V₀ (1 + n / (r w))`.
* `lc_node_le`:
  `layerCost … (j + 1) a₀ ≤ F · lcMax … j + C₁ V_{j+1} ((1 + δ) (Gd k)^τ + 1 + δ + E_bad)`.
  The interchanges of `cxCost_le` act on the keyed volume `R 2^n (r w + k') = V_j (1 + δ)` with
  chunks of width `H ≤ Gd k`, which puts the factor `1 + δ` on the `τ` term; with `δ ≤ 1`,
  `lc_node_le_of_delta` gives `F · lcMax … j + 2 C₁ V_{j+1} ((Gd k)^τ + 1 + δ + E_bad)`.
* `lc_norm_zero_le`, `lc_norm_succ_le`, `lc_norm_succ_le_eps`: the normalized cost
  `G j = lcMax … j / V_j` (`lcNorm`) has `G 0 ≤ 200 u (1 + n / (r w))` and
  `G (j + 1) ≤ (F / NW) G j + C₁ (1 + ε) ((Gd m^j u)^τ + 1)`.
* `lc_eps_le_one`: `ε ≤ 1` at a node of level `j + 1` with `K · bits u (j + 1) ≤ n` when
  `2 (k' + 1) ≤ r w`, `12 n k' ≤ 2^Gd` and `48 n k' 2^Gd ≤ 2^K`.
* `lc_pieceCost`: for a cutoff `m^j₀ ≤ d^β ≤ m^(j₀+1)` with `1 ≤ j₀`, `n ≤ r w`, the child
  exponents in the word and `ε ≤ 1` at the admissible nodes, the normalized piece costs satisfy
  `Recurrence.PieceCost m (F / NW) τ β 400 (2 C₁) d Gd`; `lc_closed` is
  `Recurrence.recurrence_closed` for one leaf size `u ≥ 2`.

**Basis changes.** A factor with a pivot makes two basis changes of at most `m` compact slot
XORs each (`2 ≤ k` selects the compact branch of `basisW`), plus the branch test, the layout
computation and the clearing of the layout registers, which are linear in `a₀, K, L, k, Gd`
(`lcBN`, `lc_basisCostN_le`, `lcBN_le`: `lcBN ≤ 158 n + 99`). A slot XOR costs at most `lcBt`
(`lc_basisCost_le`): `cxCost_le` with the exceptional addresses bounded by `CxD.cxBad_le` and
`cxBad_le_M`, `|Bad| ≤ min 1 ((k - 1) (2 / 2^Gd + 8 · 2^Gd / 2^K)) · R 2^n`. Against the volume
(`lcBt_le_vol`), `lcBt ≤ V_j (36 S (1 + δ) (Gd k)^τ + 10^6 (2 + 4 δ) + 13 E_bad + c_T)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Networks

/-! ### The slot XORs of a basis change -/

/-- The bound of one slot XOR of a basis change: `cxCost_le` with the exceptional addresses
bounded by `min 1 ((k - 1) (2 / 2^Gd + 8 · 2^Gd / 2^K)) · R 2^n`. -/
noncomputable def lcBt (T K Gd L k R n rw : ℕ) : ℝ :=
  36 * swapConst * ((T + 12 * IntegerMultBounds.MathlibTM2.Host.swapT 6 + 5 : ℕ) : ℝ) *
      ((R * 2 ^ n * (rw + (n + (sxBits R).length)) : ℕ) : ℝ) *
        ((max 1 ((k - 1) * Gd) : ℕ) : ℝ) ^ Parameters.tau +
    ((1000000 * (R * 2 ^ n * (rw + L + n + (n + (sxBits R).length) + (k - 1) * Gd + 1)) : ℕ) :
      ℝ) +
    13 * min 1 (((k - 1 : ℕ) : ℝ) * (2 / 2 ^ Gd + 8 * 2 ^ Gd / 2 ^ K)) * ((R * 2 ^ n : ℕ) : ℝ) *
      ((n + (sxBits R).length : ℕ) : ℝ) * ((rw + (n + (sxBits R).length) + 1 : ℕ) : ℝ) +
    ((24 * T + 72 * IntegerMultBounds.MathlibTM2.Host.swapT 6 + 400000 : ℕ) : ℝ)

lemma lcBt_nonneg (T K Gd L k R n rw : ℕ) : 0 ≤ lcBt T K Gd L k R n rw := by
  have := swapConst_pos
  have hmin : 0 ≤ min (1 : ℝ) (((k - 1 : ℕ) : ℝ) * (2 / 2 ^ Gd + 8 * 2 ^ Gd / 2 ^ K)) :=
    le_min zero_le_one (by positivity)
  unfold lcBt
  positivity

/-- A valid compact slot XOR costs at most `lcBt` of its parameters. -/
lemma lc_cxCost_le {d : CxD} (hv : d.Valid) (A T : ℕ) :
    cxCost A d T ≤ lcBt T d.K d.G d.L d.k d.R d.n d.rw := by
  have hb := cxCost_le hv A T
  have hbad := d.cxBad_le hv
  have hbadM : (cxBad d : ℝ) ≤ d.M := by exact_mod_cast cxBad_le_M d
  obtain ⟨eM, eBk, -, -, -, -, -, eL, -, -, -⟩ := d.swapD_fields
  have hM : d.M = d.R * 2 ^ d.n := rfl
  have hkl : d.kl = d.n + (sxBits d.R).length := rfl
  have hBk : d.Bk = d.rw + d.kl := rfl
  have hnG : d.nG = (d.k - 1) * d.G := rfl
  have hnn : d.nn = d.k - 1 := rfl
  unfold sxSwapReal at hb
  rw [eM, eBk, eL, hBk, hkl, hnG, hM] at hb
  rw [hnn, hM] at hbad
  rw [hM] at hbadM
  have hβ : (cxBad d : ℝ) ≤
      min 1 (((d.k - 1 : ℕ) : ℝ) * (2 / 2 ^ d.G + 8 * 2 ^ d.G / 2 ^ d.K)) *
        ((d.R * 2 ^ d.n : ℕ) : ℝ) := by
    rcases min_choice (1 : ℝ) (((d.k - 1 : ℕ) : ℝ) * (2 / 2 ^ d.G + 8 * 2 ^ d.G / 2 ^ d.K)) with
      h | h <;> rw [h]
    · simpa using hbadM
    · exact hbad
  refine hb.trans ?_
  unfold lcBt
  generalize IntegerMultBounds.MathlibTM2.Host.swapT 6 = sT
  generalize cxBad d = bad at hβ
  generalize d.k - 1 = k1 at hβ ⊢
  generalize (sxBits d.R).length = rb
  push_cast at hβ ⊢
  have hkk : (0 : ℝ) ≤ ((d.n : ℝ) + rb) * ((d.rw : ℝ) + ((d.n : ℝ) + rb) + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hβ hkk]

/-- One slot XOR of a basis change costs at most `lcBt`. -/
lemma lc_basisCost_le {a₀ K ρ k L R n rw Gd : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 2 ≤ k)
    (hR : 1 ≤ R) (hrw : 1 ≤ rw) (hGd : 1 ≤ Gd) (hGK : Gd + 3 ≤ K) (hfront : (k - 1) * Gd ≤ a₀)
    (hback : a₀ + m * L + 3 * ((k - 1) * Gd) ≤ n) {j j' : Fin m} (hj' : j' ≠ j) (A T : ℕ) :
    basisCostC A T a₀ K ρ L R n rw k Gd j j' ≤ lcBt T K Gd L k R n rw :=
  lc_cxCost_le (cxLayout_valid hρ hLK hk hR hrw (fun h => hj' (Fin.ext h).symm) j.isLt j'.isLt
    hGd hGK hfront hback) A T

/-- The linear part of a compact basis change: the division and the test, the layout
computation and the clearing of the layout registers. -/
def lcBN (a₀ K L k Gd : ℕ) : ℕ :=
  (12 * (L + K) + 12) + (4 * k + 4) + 1 + 1 + (2 * k + 2) + 1 +
    ((20 * (a₀ + k * Gd + k + L + m * L + (k - 1) * Gd) + 60) + (2 * k + 2) + (2 * a₀ + 2) +
      (2 * (m * L + 2) + 2) + (2 * (m * L + 3) + 2))

/-- The linear part of a basis change is at most `158 n + 99` when the slots and the control
fields fit the address. -/
lemma lcBN_le {a₀ K L k Gd n : ℕ} (hLK : L = K * k) (hk : 2 ≤ k) (hGK : Gd + 3 ≤ K)
    (hback : a₀ + m * L + 3 * ((k - 1) * Gd) ≤ n) : lcBN a₀ K L k Gd ≤ 158 * n + 99 := by
  have hLm : L ≤ m * L := Nat.le_mul_of_pos_left _ (by norm_num [m])
  have hKL : K ≤ L := by rw [hLK]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hkL : k ≤ L := by rw [hLK]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hkG : k * Gd ≤ L := by rw [hLK, Nat.mul_comm K k]; exact Nat.mul_le_mul_left _ (by omega)
  unfold lcBN
  omega

/-- A basis change costs at most `⌈m · lcBt + 1⌉ + lcBN`. -/
lemma lc_basisCostN_le {a₀ K ρ k L R n rw Gd : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 2 ≤ k)
    (hR : 1 ≤ R) (hrw : 1 ≤ rw) (hGd : 1 ≤ Gd) (hGK : Gd + 3 ≤ K) (hfront : (k - 1) * Gd ≤ a₀)
    (hback : a₀ + m * L + 3 * ((k - 1) * Gd) ≤ n) (A T : ℕ) (vv : BinaryWalsh.Address m)
    (s : Fin m) :
    basisCostN A T a₀ K ρ L R n rw k Gd vv s ≤
      ⌈(m : ℝ) * lcBt T K Gd L k R n rw + 1⌉₊ + lcBN a₀ K L k Gd := by
  unfold basisCostN
  simp only [hk, ↓reduceIte]
  unfold basisCostNC lcBN
  have hceil : ⌈((basisTargets vv s).map fun j' =>
      basisCostC A T a₀ K ρ L R n rw k Gd s j').sum + 1⌉₊ ≤
      ⌈(m : ℝ) * lcBt T K Gd L k R n rw + 1⌉₊ := by
    apply Nat.ceil_mono
    have hsum := List.sum_le_length_nsmul ((basisTargets vv s).map fun j' =>
        basisCostC A T a₀ K ρ L R n rw k Gd s j') (lcBt T K Gd L k R n rw) (by
      intro x hx
      obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hx
      exact lc_basisCost_le hρ hLK hk hR hrw hGd hGK hfront hback (mem_basisTargets.1 hj').2 A T)
    rw [List.length_map, nsmul_eq_mul] at hsum
    have hlen : ((basisTargets vv s).length : ℝ) ≤ m := by
      have : (basisTargets vv s).length ≤ m := by
        unfold basisTargets
        exact (List.length_filter_le _ _).trans (List.length_finRange).le
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_right hlen (lcBt_nonneg T K Gd L k R n rw)
    linarith
  omega

/-- `⌈x + 1⌉ ≤ x + 2`. -/
lemma lc_ceil_le {x : ℝ} (hx : 0 ≤ x) : ((⌈x + 1⌉₊ : ℕ) : ℝ) ≤ x + 2 := by
  have := Nat.ceil_lt_add_one (show 0 ≤ x + 1 by linarith)
  linarith

/-- The key length `k' = n + rb` of the slot XORs at a node of level `j + 1`. -/
noncomputable def lcKey (R₀ n j : ℕ) : ℕ := n + (sxBits (rowsAt R₀ j)).length

/-- `δ = k' / (r w)`. -/
noncomputable def lcDelta (R₀ n r w j : ℕ) : ℝ := (lcKey R₀ n j : ℝ) / ((r * w : ℕ) : ℝ)

/-- The density of exceptional addresses, `min 1 ((k - 1) (2 / 2^Gd + 8 · 2^Gd / 2^K))`. -/
noncomputable def lcBad (u K Gd j : ℕ) : ℝ :=
  min 1 (((bits u j - 1 : ℕ) : ℝ) * (2 / 2 ^ Gd + 8 * 2 ^ Gd / 2 ^ K))

/-- The repair ratio `E_bad = lcBad · k' · (1 + (k' + 1)/(r w))`. -/
noncomputable def lcEbad (u K Gd R₀ n r w j : ℕ) : ℝ :=
  lcBad u K Gd j * lcKey R₀ n j * (1 + ((lcKey R₀ n j : ℝ) + 1) / ((r * w : ℕ) : ℝ))

lemma lcBad_nonneg (u K Gd j : ℕ) : 0 ≤ lcBad u K Gd j :=
  le_min zero_le_one (by positivity)

lemma lcDelta_nonneg (R₀ n r w j : ℕ) : 0 ≤ lcDelta R₀ n r w j := by
  unfold lcDelta; positivity

lemma lcEbad_nonneg (u K Gd R₀ n r w j : ℕ) : 0 ≤ lcEbad u K Gd R₀ n r w j := by
  have := lcBad_nonneg u K Gd j
  unfold lcEbad; positivity

/-- The interchange factor `S = C (T + 12 t + 5)`. -/
noncomputable def lcS (T : ℕ) : ℝ := swapConst * ((T + 12 * IntegerMultBounds.MathlibTM2.Host.swapT 6 + 5 : ℕ) : ℝ)

/-- The additive constant of a slot XOR, `24 T + 72 t + 400000`. -/
noncomputable def lcCT (T : ℕ) : ℕ := 24 * T + 72 * IntegerMultBounds.MathlibTM2.Host.swapT 6 + 400000

lemma lcS_nonneg (T : ℕ) : 0 ≤ lcS T := by
  have := swapConst_pos; unfold lcS; positivity

/-- `lcBt` against the volume `V_j = R 2^n (r w)` of a child: the slots (`K k ≤ n`) and a
control field (`(k - 1) Gd ≤ n`) fit the address. -/
lemma lcBt_le_vol (T : ℕ) {u K Gd R₀ n r w j : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w)
    (hR₀ : 1 ≤ R₀) (hGd : 1 ≤ Gd) (hk2 : 2 ≤ bits u j) (hLn : K * bits u j ≤ n)
    (hHn : (bits u j - 1) * Gd ≤ n) :
    lcBt T K Gd (K * bits u j) (bits u j) (rowsAt R₀ j) n (r * w) ≤
      ((rowsAt R₀ j * 2 ^ n * (r * w) : ℕ) : ℝ) *
        (36 * lcS T * (1 + lcDelta R₀ n r w j) * ((Gd * bits u j : ℕ) : ℝ) ^ Parameters.tau +
          1000000 * (2 + 4 * lcDelta R₀ n r w j) + 13 * lcEbad u K Gd R₀ n r w j +
          (lcCT T : ℝ)) := by
  have hC := swapConst_pos
  have hR : 1 ≤ rowsAt R₀ j := rowsAt_pos hR₀ j
  have hH1 : 1 ≤ (bits u j - 1) * Gd :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hmax : max 1 ((bits u j - 1) * Gd) = (bits u j - 1) * Gd := max_eq_right hH1
  have hHG : (bits u j - 1) * Gd ≤ Gd * bits u j := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hτ : (((bits u j - 1) * Gd : ℕ) : ℝ) ^ Parameters.tau ≤
      ((Gd * bits u j : ℕ) : ℝ) ^ Parameters.tau :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hHG) (by norm_num [Parameters.tau])
  have hLτ0 : 0 ≤ (((bits u j - 1) * Gd : ℕ) : ℝ) ^ Parameters.tau :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold lcBt lcDelta lcEbad lcBad lcS lcCT
  rw [hmax]
  have hkey : (n : ℝ) + ((sxBits (rowsAt R₀ j)).length : ℝ) = (lcKey R₀ n j : ℝ) := by
    unfold lcKey; push_cast; ring
  have hnkey : (n : ℝ) ≤ (lcKey R₀ n j : ℝ) := by
    unfold lcKey; exact_mod_cast Nat.le_add_right _ _
  generalize IntegerMultBounds.MathlibTM2.Host.swapT 6 = sT
  generalize (((bits u j - 1) * Gd : ℕ) : ℝ) ^ Parameters.tau = Lτ' at hτ hLτ0
  generalize ((Gd * bits u j : ℕ) : ℝ) ^ Parameters.tau = Lτ at hτ
  push_cast
  rw [hkey]
  have hLn' : (K : ℝ) * (bits u j : ℝ) ≤ n := by exact_mod_cast hLn
  have hHn' : ((bits u j - 1 : ℕ) : ℝ) * (Gd : ℝ) ≤ n := by exact_mod_cast hHn
  have hk10 : (0 : ℝ) ≤ ((bits u j - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize (K : ℝ) * (bits u j : ℝ) = Lr at hLn'
  generalize ((bits u j - 1 : ℕ) : ℝ) * (Gd : ℝ) = Hr at hHn'
  generalize ((bits u j - 1 : ℕ) : ℝ) = k1 at hk10
  set P : ℝ := (rowsAt R₀ j : ℝ) * 2 ^ n with hP
  set q : ℝ := (r : ℝ) * w with hq
  set kk : ℝ := (lcKey R₀ n j : ℝ)
  set β : ℝ := min 1 (k1 * (2 / 2 ^ Gd + 8 * 2 ^ Gd / 2 ^ K))
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
  have hLτ : 0 ≤ Lτ := hLτ0.trans hτ
  have hS : 0 ≤ swapConst * ((T : ℝ) + 12 * sT + 5) := by have := swapConst_pos; positivity
  have hq0 : q ≠ 0 := by linarith
  have e1 : P * (q + kk) = P * q * (1 + kk / q) := by field_simp
  have e2 : P * (q + Lr + n + kk + Hr + 1) ≤ P * q * (2 + 4 * (kk / q)) := by
    have : P * q * (2 + 4 * (kk / q)) = P * (2 * q + 4 * kk) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e3 : P * kk * (q + kk + 1) = P * q * (kk * (1 + (kk + 1) / q)) := by field_simp; ring
  have e4 : (24 * (T : ℝ) + 72 * sT + 400000) ≤ P * q * (24 * (T : ℝ) + 72 * sT + 400000) := by
    have : 1 ≤ P * q := by nlinarith
    have h0 : 0 ≤ 24 * (T : ℝ) + 72 * sT + 400000 := by positivity
    nlinarith
  have e5 : 36 * swapConst * ((T : ℝ) + 12 * sT + 5) * (P * (q + kk)) * Lτ' ≤
      P * q * (36 * (swapConst * ((T : ℝ) + 12 * sT + 5)) * (1 + kk / q) * Lτ) := by
    rw [e1]
    have h1 : 0 ≤ 36 * swapConst * ((T : ℝ) + 12 * sT + 5) * (P * q * (1 + kk / q)) := by
      have : 0 ≤ kk / q := by positivity
      positivity
    calc 36 * swapConst * ((T : ℝ) + 12 * sT + 5) * (P * q * (1 + kk / q)) * Lτ'
        ≤ 36 * swapConst * ((T : ℝ) + 12 * sT + 5) * (P * q * (1 + kk / q)) * Lτ :=
          mul_le_mul_of_nonneg_left hτ h1
      _ = _ := by ring
  have e6 : 13 * β * P * kk * (q + kk + 1) = P * q * (13 * (β * kk * (1 + (kk + 1) / q))) := by
    rw [show 13 * β * P * kk * (q + kk + 1) = 13 * β * (P * kk * (q + kk + 1)) by ring, e3]; ring
  have e7 : (1000000 : ℝ) * (P * (q + Lr + n + kk + Hr + 1)) ≤
      P * q * (1000000 * (2 + 4 * (kk / q))) := by
    have := mul_le_mul_of_nonneg_left e2 (by norm_num : (0 : ℝ) ≤ 1000000)
    linarith
  rw [e6]
  linarith [e5, e7, e4]

/-! ### The leaf -/

/-- The volume of a level-`j` array: `rowsAt R₀ j · 2^n` records of `r w` symbols. -/
noncomputable def lcVol (R₀ n r w j : ℕ) : ℕ := rowsAt R₀ j * 2 ^ n * (r * w)

/-- **The leaf**: `layerCost … 0 a₀ ≤ 200 u V₀ (1 + n / (r w))`. -/
theorem lc_leaf_le (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w Gd a₀ : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hfit : a₀ + K * bits u 0 ≤ n) :
    (layerCost A T ds u K ρ R₀ n r w Gd 0 a₀ : ℝ) ≤
      200 * u * (lcVol R₀ n r w 0 : ℝ) * (1 + (n : ℝ) / ((r * w : ℕ) : ℝ)) := by
  have h := lc_leaf_nat A T ds (Gd := Gd) hu hr hw hR₀ hρ hfit
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

/-- The offset `a` is admissible at level `j`: the active bits fit the address, and at a node
(`1 ≤ j`) a control field of the children fits below the slots and three fit above. -/
def lcAdm (u K n Gd j a : ℕ) : Prop :=
  a + K * bits u j ≤ n ∧
    (1 ≤ j → (bits u (j - 1) - 1) * Gd ≤ a ∧
      a + K * bits u j + 3 * ((bits u (j - 1) - 1) * Gd) ≤ n)

instance (u K n Gd j a : ℕ) : Decidable (lcAdm u K n Gd j a) := by
  unfold lcAdm; infer_instance

/-- The children `a₀ + s K bits u j`, `s < m`, of a node admissible at level `j + 1` are
admissible at level `j`. -/
lemma lcAdm_child {u K n Gd j a₀ : ℕ} (h : lcAdm u K n Gd (j + 1) a₀) {s : ℕ} (hs : s < m) :
    lcAdm u K n Gd j (a₀ + s * (K * bits u j)) := by
  obtain ⟨hfit, hres⟩ := h
  obtain ⟨hfront, hback⟩ := hres (by omega)
  simp only [Nat.add_sub_cancel] at hfront hback
  have hL₁ : K * bits u (j + 1) = m * (K * bits u j) := by
    rw [show bits u (j + 1) = m * bits u j from rfl]; ring
  have h1 : (s + 1) * (K * bits u j) ≤ m * (K * bits u j) := Nat.mul_le_mul_right _ hs
  have h3 : (s + 1) * (K * bits u j) = s * (K * bits u j) + K * bits u j := by ring
  refine ⟨by omega, fun hj => ?_⟩
  have hbl : bits u (j - 1) ≤ bits u j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simpa using bits_le_succ u j'
  have h2 : (bits u (j - 1) - 1) * Gd ≤ (bits u j - 1) * Gd := Nat.mul_le_mul_right _ (by omega)
  constructor <;> omega

/-- The largest `layerCost … j a` over the admissible offsets `a`. -/
noncomputable def lcMax (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    (u K ρ R₀ n r w Gd j : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun a => lcAdm u K n Gd j a).sup
    (layerCost A T ds u K ρ R₀ n r w Gd j)

/-- An admissible offset costs at most `lcMax`. -/
lemma lc_le_max (A T : ℕ) (ds : ComplexFramedExecution.Directions) {u K ρ R₀ n r w Gd j a : ℕ}
    (h : lcAdm u K n Gd j a) :
    layerCost A T ds u K ρ R₀ n r w Gd j a ≤ lcMax A T ds u K ρ R₀ n r w Gd j :=
  Finset.le_sup (f := layerCost A T ds u K ρ R₀ n r w Gd j)
    (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := h.1; omega), h⟩)

/-- `lcMax` is at most every real bound of the admissible offsets. -/
lemma lc_max_le_real (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w Gd j : ℕ} {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ a, lcAdm u K n Gd j a → (layerCost A T ds u K ρ R₀ n r w Gd j a : ℝ) ≤ X) :
    (lcMax A T ds u K ρ R₀ n r w Gd j : ℝ) ≤ X := by
  unfold lcMax
  set s := (Finset.range (n + 1)).filter fun a => lcAdm u K n Gd j a
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs, Finset.sup_empty]; simpa using hX
  · obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup s hs (layerCost A T ds u K ρ R₀ n r w Gd j)
    rw [he]
    exact h a (Finset.mem_filter.1 ha).2

/-- Without admissible offsets, `lcMax = 0`. -/
lemma lc_max_eq_zero (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w Gd j : ℕ} (h : ∀ a, ¬ lcAdm u K n Gd j a) :
    lcMax A T ds u K ρ R₀ n r w Gd j = 0 := by
  unfold lcMax
  convert Finset.sup_empty
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
  exact fun _ => h a

/-! ### The node -/

/-- The node constant `C₁ = 2 m F (36 S + c_T + 4000013) + 404 F + lcLin`. -/
noncomputable def lcC1 (T : ℕ) (ds : ComplexFramedExecution.Directions) : ℝ :=
  2 * m * factorCount (program ds) * (36 * lcS T + lcCT T + 4000013) +
    404 * factorCount (program ds) + lcLin ds

lemma lcC1_nonneg (T : ℕ) (ds : ComplexFramedExecution.Directions) : 0 ≤ lcC1 T ds := by
  have := lcS_nonneg T
  unfold lcC1; positivity

/-- The real algebra of the node bound: `lc_node_nat` with the basis changes within
`m · lcBt + 2 + 200 (V + W)` steps, `lcBt_le_vol` and `W ≤ V δ`. -/
lemma lc_node_alg {Lc M B Bt F NW V Wn δ E Lτ mm S cT Lin : ℝ}
    (hF : 0 ≤ F) (hmm : 0 ≤ mm) (hS : 0 ≤ S) (hcT : 0 ≤ cT) (hLin : 0 ≤ Lin)
    (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hLτ : 0 ≤ Lτ) (hNW : 1 ≤ NW) (hV : 1 ≤ V)
    (hN : Lc ≤ F * (M + 2 * B) + Lin * (NW * (V + Wn)))
    (hB : B ≤ mm * Bt + 2 + 200 * (V + Wn))
    (hBt : Bt ≤ V * (36 * S * (1 + δ) * Lτ + 1000000 * (2 + 4 * δ) + 13 * E + cT))
    (hWn : Wn ≤ V * δ) :
    Lc ≤ F * M + (2 * mm * F * (36 * S + cT + 4000013) + 404 * F + Lin) * (NW * V) *
      ((1 + δ) * Lτ + 1 + δ + E) := by
  set Q : ℝ := (1 + δ) * Lτ + 1 + δ + E with hQ
  have hδLτ : 0 ≤ (1 + δ) * Lτ := mul_nonneg (by linarith) hLτ
  have hQ1 : 1 + δ ≤ Q := by linarith
  have hQ1' : 1 ≤ Q := by linarith
  have hQτ : (1 + δ) * Lτ ≤ Q := by linarith
  have hEQ : E ≤ Q := by linarith
  have hinner : 36 * S * (1 + δ) * Lτ + 1000000 * (2 + 4 * δ) + 13 * E + cT ≤
      (36 * S + cT + 4000013) * Q := by
    have h1 : 36 * S * (1 + δ) * Lτ ≤ 36 * S * Q := by
      rw [mul_assoc (36 * S)]; exact mul_le_mul_of_nonneg_left hQτ (by positivity)
    have h2 : cT * 1 ≤ cT * Q := mul_le_mul_of_nonneg_left hQ1' hcT
    have h3 : 1000000 * (2 + 4 * δ) ≤ 4000000 * Q := by linarith
    linarith
  have hVV : V ≤ NW * V := le_mul_of_one_le_left (by linarith) hNW
  have hNV1 : 1 ≤ NW * V := one_le_mul_of_one_le_of_one_le hNW hV
  have hVQ : 1 ≤ NW * V * Q := one_le_mul_of_one_le_of_one_le hNV1 hQ1'
  have hC0 : 0 ≤ (36 * S + cT + 4000013) * Q := by positivity
  have hBt' : mm * Bt ≤ mm * (NW * V) * ((36 * S + cT + 4000013) * Q) := by
    calc mm * Bt ≤ mm * (V * ((36 * S + cT + 4000013) * Q)) :=
          mul_le_mul_of_nonneg_left (hBt.trans (mul_le_mul_of_nonneg_left hinner (by linarith))) hmm
      _ ≤ mm * (NW * V * ((36 * S + cT + 4000013) * Q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hVV hC0) hmm
      _ = _ := by ring
  have hVW : V + Wn ≤ NW * V * Q := by
    have h1 : V * (1 + δ) ≤ V * Q := mul_le_mul_of_nonneg_left hQ1 (by linarith)
    have h2 : V * Q ≤ NW * V * Q := mul_le_mul_of_nonneg_right hVV (by linarith)
    linarith
  have hbasis : 2 * F * B ≤
      2 * mm * F * (36 * S + cT + 4000013) * (NW * V * Q) + 404 * F * (NW * V * Q) := by
    have h3 : 200 * (V + Wn) ≤ 200 * (NW * V * Q) :=
      mul_le_mul_of_nonneg_left hVW (by positivity)
    have h4 : F * (200 * (V + Wn)) ≤ F * (200 * (NW * V * Q)) :=
      mul_le_mul_of_nonneg_left h3 hF
    have h5 : F * B ≤ F * (mm * Bt + 2 + 200 * (V + Wn)) :=
      mul_le_mul_of_nonneg_left hB hF
    have h6 : F * (mm * Bt) ≤ F * (mm * (NW * V) * ((36 * S + cT + 4000013) * Q)) :=
      mul_le_mul_of_nonneg_left hBt' hF
    have h7 : F * 2 ≤ F * (2 * (NW * V * Q)) := mul_le_mul_of_nonneg_left (by linarith) hF
    linarith
  have hlin : Lin * (NW * (V + Wn)) ≤ Lin * (NW * V * Q) := by
    apply mul_le_mul_of_nonneg_left _ hLin
    have h1 : V * (1 + δ) ≤ V * Q := mul_le_mul_of_nonneg_left hQ1 (by linarith)
    have : V + Wn ≤ V * Q := by linarith
    calc NW * (V + Wn) ≤ NW * (V * Q) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = _ := by ring
  calc Lc ≤ F * M + 2 * F * B + Lin * (NW * (V + Wn)) := by linarith
    _ ≤ F * M + (2 * mm * F * (36 * S + cT + 4000013) * (NW * V * Q) +
          404 * F * (NW * V * Q)) + Lin * (NW * V * Q) := by linarith
    _ = _ := by ring

/-- **The node.** At an admissible offset (the active bits fit, a control field of the children
fits below the slots and three above), with the child exponents in the word,
`layerCost … (j + 1) a₀ ≤ F · lcMax … j + C₁ V_{j+1} ((1 + δ) (Gd bits u j)^τ + 1 + δ + E_bad)`. -/
theorem lc_node_le (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w Gd j a₀ : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hGd : 1 ≤ Gd) (hGK : Gd + 3 ≤ K) (hk2 : 2 ≤ bits u j)
    (hfit : a₀ + K * bits u (j + 1) ≤ n)
    (hfront : (bits u j - 1) * Gd ≤ a₀)
    (hback : a₀ + K * bits u (j + 1) + 3 * ((bits u j - 1) * Gd) ≤ n)
    (hTw : ∀ i ≤ j, expZ u ds i ≤ w) :
    (layerCost A T ds u K ρ R₀ n r w Gd (j + 1) a₀ : ℝ) ≤
      factorCount (program ds) * (lcMax A T ds u K ρ R₀ n r w Gd j : ℝ) +
        lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
          ((1 + lcDelta R₀ n r w j) * ((Gd * bits u j : ℕ) : ℝ) ^ Parameters.tau + 1 +
            lcDelta R₀ n r w j + lcEbad u K Gd R₀ n r w j) := by
  have hK : 1 ≤ K := by omega
  have hR : 1 ≤ rowsAt R₀ j := rowsAt_pos hR₀ j
  have hrw : 1 ≤ r * w := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hL₁ : K * bits u (j + 1) = m * (K * bits u j) := by
    rw [show bits u (j + 1) = m * bits u j from rfl]; ring
  have hback' : a₀ + m * (K * bits u j) + 3 * ((bits u j - 1) * Gd) ≤ n := by
    rw [← hL₁]; exact hback
  have hadm : lcAdm u K n Gd (j + 1) a₀ :=
    ⟨hfit, fun _ => by simpa only [Nat.add_sub_cancel] using And.intro hfront hback⟩
  have hLn : K * bits u j ≤ n := by
    have : K * bits u j ≤ m * (K * bits u j) := Nat.le_mul_of_pos_left _ (by norm_num [m])
    omega
  have hHn : (bits u j - 1) * Gd ≤ n := by omega
  have hceil := lc_ceil_le (mul_nonneg (Nat.cast_nonneg m)
    (lcBt_nonneg T K Gd (K * bits u j) (bits u j) (rowsAt R₀ j) n (r * w)))
  have hBv := lcBt_le_vol T (j := j) hr hw hR₀ hGd hk2 hLn hHn
  have hBN : lcBN a₀ K (K * bits u j) (bits u j) Gd ≤
      200 * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) := by
    have h1 := lcBN_le rfl hk2 hGK hback'
    have hnW : n ≤ rowsAt R₀ j * 2 ^ n * n :=
      Nat.le_mul_of_pos_left n (Nat.mul_pos hR (Nat.two_pow_pos n))
    have hV1' : 1 ≤ rowsAt R₀ j * 2 ^ n * (r * w) :=
      Nat.mul_le_mul (Nat.mul_le_mul hR h2n) hrw
    omega
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
      basisCostN A T a₀ K ρ (K * bits u j) (rowsAt R₀ j) n (r * w) (bits u j) Gd vv s ≤
        ⌈(m : ℝ) * lcBt T K Gd (K * bits u j) (bits u j) (rowsAt R₀ j) n (r * w) + 1⌉₊ +
          200 * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    fun vv s => (lc_basisCostN_le hρ rfl hk2 hR hrw hGd hGK hfront hback' A T vv s).trans
      (Nat.add_le_add_left hBN _)
  have hM : ∀ s < m, layerCost A T ds u K ρ R₀ n r w Gd j (a₀ + s * (K * bits u j)) ≤
      lcMax A T ds u K ρ R₀ n r w Gd j := fun s hs => lc_le_max A T ds (lcAdm_child hadm hs)
  have hN := lc_node_nat A T ds hu hr hw hR₀ hρ hfit hTw hM hB
  have hNr : (layerCost A T ds u K ρ R₀ n r w Gd (j + 1) a₀ : ℝ) ≤
      (factorCount (program ds) : ℝ) * ((lcMax A T ds u K ρ R₀ n r w Gd j : ℝ) +
        2 * ((⌈(m : ℝ) * lcBt T K Gd (K * bits u j) (bits u j) (rowsAt R₀ j) n (r * w) + 1⌉₊ :
          ℕ) + 200 * (((rowsAt R₀ j * 2 ^ n * (r * w)) : ℕ) +
            ((rowsAt R₀ j * 2 ^ n * n : ℕ) : ℝ)))) +
        (lcLin ds : ℝ) * ((NW : ℕ) * (((rowsAt R₀ j * 2 ^ n * (r * w)) : ℕ) +
        ((rowsAt R₀ j * 2 ^ n * n : ℕ) : ℝ))) := by
    exact_mod_cast hN
  rw [hVol]
  unfold lcC1
  exact lc_node_alg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (lcS_nonneg T)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (lcDelta_nonneg _ _ _ _ _)
    (lcEbad_nonneg _ _ _ _ _ _ _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hNW hV1
    hNr (by linarith) hBv hWnδ

/-! ### The normalized recurrence -/

lemma lcVol_pos {R₀ n r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (j : ℕ) :
    (0 : ℝ) < (lcVol R₀ n r w j : ℝ) := by
  have : 0 < lcVol R₀ n r w j :=
    Nat.mul_pos (Nat.mul_pos (rowsAt_pos hR₀ j) (Nat.two_pow_pos n)) (Nat.mul_pos hr hw)
  exact_mod_cast this

/-- The normalized cost `G j = lcMax … j / V_j`. -/
noncomputable def lcNorm (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    (u K ρ R₀ n r w Gd j : ℕ) : ℝ :=
  (lcMax A T ds u K ρ R₀ n r w Gd j : ℝ) / (lcVol R₀ n r w j : ℝ)

lemma lcNorm_nonneg (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    (u K ρ R₀ n r w Gd j : ℕ) : 0 ≤ lcNorm A T ds u K ρ R₀ n r w Gd j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The small ratios of a node of level `j + 1`: `ε = δ + E_bad`. -/
noncomputable def lcEps (u K Gd R₀ n r w j : ℕ) : ℝ :=
  lcDelta R₀ n r w j + lcEbad u K Gd R₀ n r w j

lemma lcEps_nonneg (u K Gd R₀ n r w j : ℕ) : 0 ≤ lcEps u K Gd R₀ n r w j :=
  add_nonneg (lcDelta_nonneg _ _ _ _ _) (lcEbad_nonneg _ _ _ _ _ _ _ _)

/-- `c · bits u j = c m^j u` as a real number. -/
lemma lc_cast_Kbits (K u j : ℕ) : ((K * bits u j : ℕ) : ℝ) = (K : ℝ) * (m : ℝ) ^ j * u := by
  rw [lc_bits_eq]; push_cast; ring

lemma lc_Q_nonneg (u K Gd R₀ n r w j : ℕ) :
    0 ≤ (1 + lcDelta R₀ n r w j) * ((Gd : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau +
      1 + lcDelta R₀ n r w j + lcEbad u K Gd R₀ n r w j := by
  have := lcDelta_nonneg R₀ n r w j
  have := lcEbad_nonneg u K Gd R₀ n r w j
  have : 0 ≤ ((Gd : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau :=
    Real.rpow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg Gd) (pow_nonneg (Nat.cast_nonneg m) j))
      (Nat.cast_nonneg u)) _
  positivity

lemma lc_div_aux {M' M C Q F nw V : ℝ} (hnw : 0 < nw) (hV : 0 < V)
    (h : M' ≤ F * M + C * (nw * V) * Q) : M' / (nw * V) ≤ (F / nw) * (M / V) + C * Q := by
  rw [div_le_iff₀ (mul_pos hnw hV)]
  calc M' ≤ F * M + C * (nw * V) * Q := h
    _ = _ := by field_simp

/-- **The normalized node recurrence**:
`G (j + 1) ≤ (F / NW) G j + C₁ ((1 + δ) (Gd m^j u)^τ + 1 + δ + E_bad)`, with the child exponents
in the word at every admissible offset of level `j + 1`. -/
theorem lc_norm_succ_le (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w Gd j : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hGd : 1 ≤ Gd) (hGK : Gd + 3 ≤ K) (hk2 : 2 ≤ bits u j)
    (hTw : ∀ a, lcAdm u K n Gd (j + 1) a → ∀ i ≤ j, expZ u ds i ≤ w) :
    lcNorm A T ds u K ρ R₀ n r w Gd (j + 1) ≤
      ((factorCount (program ds) : ℝ) / NW) * lcNorm A T ds u K ρ R₀ n r w Gd j +
        lcC1 T ds * ((1 + lcDelta R₀ n r w j) * ((Gd : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau +
          1 + lcDelta R₀ n r w j + lcEbad u K Gd R₀ n r w j) := by
  have hV := lcVol_pos (n := n) hr hw hR₀ j
  have hV' := lcVol_pos (n := n) hr hw hR₀ (j + 1)
  have hNW : (0 : ℝ) < ((NW : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne NW))
  have hQ := lc_Q_nonneg u K Gd R₀ n r w j
  have hVV : (lcVol R₀ n r w (j + 1) : ℝ) = ((NW : ℕ) : ℝ) * (lcVol R₀ n r w j : ℝ) := by
    rw [lcVol, lcVol, show rowsAt R₀ (j + 1) = NW * rowsAt R₀ j from rfl, Nat.mul_assoc NW,
      Nat.mul_assoc NW, Nat.cast_mul]
  have key : (lcMax A T ds u K ρ R₀ n r w Gd (j + 1) : ℝ) ≤
      factorCount (program ds) * (lcMax A T ds u K ρ R₀ n r w Gd j : ℝ) +
        lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
          ((1 + lcDelta R₀ n r w j) * ((Gd * bits u j : ℕ) : ℝ) ^ Parameters.tau + 1 +
            lcDelta R₀ n r w j + lcEbad u K Gd R₀ n r w j) := by
    refine lc_max_le_real A T ds ?_ fun a ha => ?_
    · rw [lc_cast_Kbits]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg (lcC1_nonneg T ds) hV'.le) hQ)
    · obtain ⟨hfront, hback⟩ := ha.2 (by omega)
      simp only [Nat.add_sub_cancel] at hfront hback
      exact lc_node_le A T ds hu hr hw hR₀ hρ hGd hGK hk2 ha.1 hfront hback (hTw a ha)
  rw [lc_cast_Kbits, hVV] at key
  unfold lcNorm
  rw [hVV]
  exact lc_div_aux hNW hV key

/-- The normalized node recurrence with `ε = δ + E_bad`:
`G (j + 1) ≤ (F / NW) G j + C₁ (1 + ε) ((Gd m^j u)^τ + 1)`. -/
theorem lc_norm_succ_le_eps (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w Gd j : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hGd : 1 ≤ Gd) (hGK : Gd + 3 ≤ K) (hk2 : 2 ≤ bits u j)
    (hTw : ∀ a, lcAdm u K n Gd (j + 1) a → ∀ i ≤ j, expZ u ds i ≤ w) :
    lcNorm A T ds u K ρ R₀ n r w Gd (j + 1) ≤
      ((factorCount (program ds) : ℝ) / NW) * lcNorm A T ds u K ρ R₀ n r w Gd j +
        lcC1 T ds * (1 + lcEps u K Gd R₀ n r w j) *
          (((Gd : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau + 1) := by
  refine (lc_norm_succ_le A T ds hu hr hw hR₀ hρ hGd hGK hk2 hTw).trans ?_
  rw [mul_assoc (lcC1 T ds)]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (lcC1_nonneg T ds))
  have hE := lcEbad_nonneg u K Gd R₀ n r w j
  have hL : 0 ≤ ((Gd : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau :=
    Real.rpow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg Gd) (pow_nonneg (Nat.cast_nonneg m) j))
      (Nat.cast_nonneg u)) _
  generalize ((Gd : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau = L at hL ⊢
  unfold lcEps
  nlinarith

/-- **The normalized leaf**: `G 0 ≤ 200 u (1 + n / (r w))`. -/
theorem lc_norm_zero_le (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w Gd : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K) :
    lcNorm A T ds u K ρ R₀ n r w Gd 0 ≤ 200 * u * (1 + (n : ℝ) / ((r * w : ℕ) : ℝ)) := by
  have hV := lcVol_pos (n := n) hr hw hR₀ 0
  have hq : (0 : ℝ) ≤ (n : ℝ) / ((r * w : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  unfold lcNorm
  rw [div_le_iff₀ hV]
  refine lc_max_le_real A T ds (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (Nat.cast_nonneg _)) (by linarith)) hV.le) fun a ha => ?_
  calc (layerCost A T ds u K ρ R₀ n r w Gd 0 a : ℝ) ≤ _ :=
        lc_leaf_le A T ds hu hr hw hR₀ hρ ha.1
    _ = _ := by ring

/-! ### When the small ratios are at most `1` -/

/-- The row field has logarithmic width: `rb ≤ log₂ R + 1`. -/
lemma lc_rb_le (R : ℕ) : (sxBits R).length ≤ R.log2 + 1 := by
  have h := GrowingCounterData.canonical_width (sxBits R) (canonical_sxBits R)
  rwa [value_sxBits] at h

/-- **`ε ≤ 1`** at a node of level `j + 1` whose active bits fit (`K · bits u (j + 1) ≤ n`)
when `2 (k' + 1) ≤ r w`, `12 n k' ≤ 2^Gd` and `48 n k' 2^Gd ≤ 2^K`, `k' = n + rb`. -/
theorem lc_eps_le_one {u K Gd R₀ n r w j : ℕ} (hK : 1 ≤ K)
    (hadm : K * bits u (j + 1) ≤ n)
    (h1 : 2 * (lcKey R₀ n j + 1) ≤ r * w) (h2 : 12 * n * lcKey R₀ n j ≤ 2 ^ Gd)
    (h3 : 48 * n * lcKey R₀ n j * 2 ^ Gd ≤ 2 ^ K) :
    lcEps u K Gd R₀ n r w j ≤ 1 := by
  have hkn : bits u j - 1 ≤ n := by
    have h4 : bits u j ≤ bits u (j + 1) := lc_bits_mono u (Nat.le_succ j)
    have h5 : bits u (j + 1) ≤ K * bits u (j + 1) := Nat.le_mul_of_pos_left _ hK
    omega
  unfold lcEps lcDelta lcEbad lcBad
  have hq1 : (2 : ℝ) * ((lcKey R₀ n j : ℝ) + 1) ≤ ((r * w : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : (12 : ℝ) * n * (lcKey R₀ n j : ℝ) ≤ 2 ^ Gd := by exact_mod_cast h2
  have h3' : (48 : ℝ) * n * (lcKey R₀ n j : ℝ) * 2 ^ Gd ≤ 2 ^ K := by exact_mod_cast h3
  have hkn' : ((bits u j - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hkn
  have hkk0 : (0 : ℝ) ≤ (lcKey R₀ n j : ℝ) := Nat.cast_nonneg _
  have hPG : (0 : ℝ) < 2 ^ Gd := by positivity
  have hPK : (0 : ℝ) < 2 ^ K := by positivity
  have hζ : (0 : ℝ) ≤ 2 / 2 ^ Gd + 8 * 2 ^ Gd / 2 ^ K := by positivity
  have hβ : min 1 (((bits u j - 1 : ℕ) : ℝ) * (2 / 2 ^ Gd + 8 * 2 ^ Gd / 2 ^ K)) ≤
      (n : ℝ) * (2 / 2 ^ Gd + 8 * 2 ^ Gd / 2 ^ K) :=
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_right hkn' hζ)
  have hβ0 : 0 ≤ min 1 (((bits u j - 1 : ℕ) : ℝ) * (2 / 2 ^ Gd + 8 * 2 ^ Gd / 2 ^ K)) :=
    le_min zero_le_one (by positivity)
  generalize min 1 (((bits u j - 1 : ℕ) : ℝ) * (2 / 2 ^ Gd + 8 * 2 ^ Gd / 2 ^ K)) = β at hβ hβ0 ⊢
  generalize ((r * w : ℕ) : ℝ) = q at hq1 ⊢
  generalize (lcKey R₀ n j : ℝ) = kk at hq1 h2' h3' hkk0 ⊢
  generalize (2 : ℝ) ^ Gd = PG at h2' h3' hPG hζ hβ ⊢
  generalize (2 : ℝ) ^ K = PK at h3' hPK hζ hβ ⊢
  have hq : 0 < q := by linarith
  have hδ : kk / q ≤ 1 / 2 := by rw [div_le_iff₀ hq]; linarith
  have ht : (kk + 1) / q ≤ 1 / 2 := by rw [div_le_iff₀ hq]; linarith
  have ht0 : 0 ≤ (kk + 1) / q := div_nonneg (by linarith) hq.le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hA : 2 * ((n : ℝ) * kk) / PG ≤ 1 / 6 := by
    rw [div_le_iff₀ hPG]; linarith
  have hB' : 8 * ((n : ℝ) * kk) * PG / PK ≤ 1 / 6 := by
    rw [div_le_iff₀ hPK]; linarith
  have hB : (n : ℝ) * (2 / PG + 8 * PG / PK) * kk ≤ 1 / 3 := by
    have : (n : ℝ) * (2 / PG + 8 * PG / PK) * kk =
        2 * ((n : ℝ) * kk) / PG + 8 * ((n : ℝ) * kk) * PG / PK := by ring
    rw [this]; linarith
  have hE : β * kk * (1 + (kk + 1) / q) ≤ 1 / 2 := by
    have h1 : β * kk ≤ (n : ℝ) * (2 / PG + 8 * PG / PK) * kk :=
      mul_le_mul_of_nonneg_right hβ hkk0
    have h2 : β * kk * (1 + (kk + 1) / q) ≤ β * kk * (3 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hβ0 hkk0)
    nlinarith
  linarith

/-- The node bound with `(1 + δ)` absorbed (`δ ≤ 1`):
`layerCost … (j + 1) a₀ ≤ F · lcMax … j + 2 C₁ V_{j+1} ((Gd bits u j)^τ + 1 + δ + E_bad)`. -/
theorem lc_node_le_of_delta (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w Gd j a₀ : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hGd : 1 ≤ Gd) (hGK : Gd + 3 ≤ K) (hk2 : 2 ≤ bits u j)
    (hfit : a₀ + K * bits u (j + 1) ≤ n)
    (hfront : (bits u j - 1) * Gd ≤ a₀)
    (hback : a₀ + K * bits u (j + 1) + 3 * ((bits u j - 1) * Gd) ≤ n)
    (hTw : ∀ i ≤ j, expZ u ds i ≤ w) (hδ : lcDelta R₀ n r w j ≤ 1) :
    (layerCost A T ds u K ρ R₀ n r w Gd (j + 1) a₀ : ℝ) ≤
      factorCount (program ds) * (lcMax A T ds u K ρ R₀ n r w Gd j : ℝ) +
        2 * lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
          (((Gd * bits u j : ℕ) : ℝ) ^ Parameters.tau + 1 + lcDelta R₀ n r w j +
            lcEbad u K Gd R₀ n r w j) := by
  refine (lc_node_le A T ds hu hr hw hR₀ hρ hGd hGK hk2 hfit hfront hback hTw).trans ?_
  have hδ0 := lcDelta_nonneg R₀ n r w j
  have hE := lcEbad_nonneg u K Gd R₀ n r w j
  have hL : 0 ≤ ((Gd * bits u j : ℕ) : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCV : 0 ≤ lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) :=
    mul_nonneg (lcC1_nonneg T ds) (Nat.cast_nonneg _)
  generalize ((Gd * bits u j : ℕ) : ℝ) ^ Parameters.tau = L at hL ⊢
  have h1 : (1 + lcDelta R₀ n r w j) * L + 1 + lcDelta R₀ n r w j + lcEbad u K Gd R₀ n r w j ≤
      2 * (L + 1 + lcDelta R₀ n r w j + lcEbad u K Gd R₀ n r w j) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 hCV
  have h3 : lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
      (2 * (L + 1 + lcDelta R₀ n r w j + lcEbad u K Gd R₀ n r w j)) =
      2 * lcC1 T ds * (lcVol R₀ n r w (j + 1) : ℝ) *
        (L + 1 + lcDelta R₀ n r w j + lcEbad u K Gd R₀ n r w j) := by ring
  linarith

/-! ### The piece-cost recurrence -/

/-- The step of the normalized recurrence with `ε ≤ 1` at the admissible offsets:
`G (j + 1) ≤ (F / NW) G j + 2 C₁ ((Gd m^j u)^τ + 1)`; without admissible offsets of level
`j + 1`, `G (j + 1) = 0`. -/
theorem lc_norm_succ_le_two (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w Gd j : ℕ}
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hGd : 1 ≤ Gd) (hGK : Gd + 3 ≤ K) (hk2 : 2 ≤ bits u j)
    (hTw : ∀ a, lcAdm u K n Gd (j + 1) a → ∀ i ≤ j, expZ u ds i ≤ w)
    (hε : ∀ a, lcAdm u K n Gd (j + 1) a → lcEps u K Gd R₀ n r w j ≤ 1) :
    lcNorm A T ds u K ρ R₀ n r w Gd (j + 1) ≤
      ((factorCount (program ds) : ℝ) / NW) * lcNorm A T ds u K ρ R₀ n r w Gd j +
        2 * lcC1 T ds * (((Gd : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau + 1) := by
  have hG0 := lcNorm_nonneg A T ds u K ρ R₀ n r w Gd j
  have hC := lcC1_nonneg T ds
  have hL : 0 ≤ ((Gd : ℝ) * (m : ℝ) ^ j * u) ^ Parameters.tau :=
    Real.rpow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg Gd)
      (pow_nonneg (Nat.cast_nonneg m) j)) (Nat.cast_nonneg u)) _
  by_cases hex : ∃ a, lcAdm u K n Gd (j + 1) a
  · obtain ⟨a, ha⟩ := hex
    have h := lc_norm_succ_le_eps A T ds hu hr hw hR₀ hρ hGd hGK hk2 hTw
    have he := hε a ha
    have he0 := lcEps_nonneg u K Gd R₀ n r w j
    refine h.trans (add_le_add le_rfl ?_)
    have h1 : lcC1 T ds * (1 + lcEps u K Gd R₀ n r w j) ≤ 2 * lcC1 T ds := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  · rw [lcNorm, lc_max_eq_zero A T ds (fun a ha => hex ⟨a, ha⟩), Nat.cast_zero, zero_div]
    exact add_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hG0)
      (mul_nonneg (mul_nonneg (by norm_num) hC) (by linarith))

/-- **`PieceCost` for the layer machine.** Fix the cutoff `m^j₀ ≤ d^β ≤ m^(j₀+1)` with
`1 ≤ j₀`. A piece of `m^j` chunks runs the layer machine with `u = m^(min j j₀)` bits per leaf
at level `j - j₀`; its normalized cost `G j = lcNorm … (m^(min j j₀)) … (j - j₀)` satisfies
`Recurrence.PieceCost m (F / NW) τ β 400 (2 C₁) d Gd`, provided `n ≤ r w`, the child
exponents fit the word at every admissible offset, and `ε ≤ 1` at every admissible node. -/
theorem lc_pieceCost (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    {K ρ R₀ n r w Gd j₀ : ℕ} {d β : ℝ}
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K) (hGd : 1 ≤ Gd) (hGK : Gd + 3 ≤ K)
    (hj₀1 : 1 ≤ j₀) (hn : n ≤ r * w)
    (hj₀ : (m : ℝ) ^ j₀ ≤ d ^ β) (hj₀' : d ^ β ≤ (m : ℝ) ^ (j₀ + 1))
    (hTw : ∀ i a, lcAdm (m ^ j₀) K n Gd (i + 1) a → ∀ i' ≤ i, expZ (m ^ j₀) ds i' ≤ w)
    (hε : ∀ i a, lcAdm (m ^ j₀) K n Gd (i + 1) a → lcEps (m ^ j₀) K Gd R₀ n r w i ≤ 1) :
    Recurrence.PieceCost (m : ℝ) ((factorCount (program ds) : ℝ) / NW) Parameters.tau β 400
      (2 * lcC1 T ds) d Gd
      (fun j => lcNorm A T ds (m ^ min j j₀) K ρ R₀ n r w Gd (j - j₀)) := by
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
    refine (lc_norm_zero_le A T ds hu hr hw hR₀ hρ).trans ?_
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
    have hu2 : 2 ≤ m ^ j₀ :=
      le_trans (by norm_num [m]) (Nat.pow_le_pow_right hm0 hj₀1 : m ^ 1 ≤ m ^ j₀)
    have hk2 : 2 ≤ bits (m ^ j₀) (j - j₀) := hu2.trans (le_bits _ _)
    have hC := lcC1_nonneg T ds
    have hτ : 0 ≤ Parameters.tau := by norm_num [Parameters.tau]
    have hG0 : (0 : ℝ) ≤ Gd := Nat.cast_nonneg Gd
    have hmono : ((Gd : ℝ) * (m : ℝ) ^ j) ^ Parameters.tau ≤
        ((Gd : ℝ) * (m : ℝ) ^ (j + 1)) ^ Parameters.tau :=
      Real.rpow_le_rpow (mul_nonneg hG0 (pow_nonneg (Nat.cast_nonneg m) j))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 (Nat.le_succ j)) hG0) hτ
    have h := lc_norm_succ_le_two A T ds hu hr hw hR₀ hρ hGd hGK hk2 (n := n) (j := j - j₀)
      (hTw (j - j₀)) (hε (j - j₀))
    have hGL : (Gd : ℝ) * (m : ℝ) ^ (j - j₀) * ((m ^ j₀ : ℕ) : ℝ) = (Gd : ℝ) * (m : ℝ) ^ j := by
      push_cast
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
    rw [hGL] at h
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- **The closed bound** (`Recurrence.recurrence_closed` with `C₀ = 400`, `C₁' = 2 C₁`): for
`τ ≤ λ`, `log_m (F / NW) < λ`, `n ≤ r w`, `2 ≤ u`, child exponents in the word and `ε ≤ 1` at
every admissible node, `G j ≤ C (m^j u)^λ Gd^τ + C (F / NW)^j u`. -/
theorem lc_closed (A T : ℕ) (ds : ComplexFramedExecution.Directions) {u K ρ R₀ n r w Gd : ℕ}
    {lam : ℝ} (hu : 2 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hGd : 1 ≤ Gd) (hGK : Gd + 3 ≤ K)
    (hn : n ≤ r * w) (hτl : Parameters.tau ≤ lam)
    (hal : Real.logb (m : ℝ) ((factorCount (program ds) : ℝ) / NW) < lam)
    (hTw : ∀ i a, lcAdm u K n Gd (i + 1) a → ∀ i' ≤ i, expZ u ds i' ≤ w)
    (hε : ∀ i a, lcAdm u K n Gd (i + 1) a → lcEps u K Gd R₀ n r w i ≤ 1) (j : ℕ) :
    lcNorm A T ds u K ρ R₀ n r w Gd j ≤
      Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m lam 400 (2 * lcC1 T ds) *
          ((m : ℝ) ^ j * u) ^ lam * (Gd : ℝ) ^ Parameters.tau +
        Recurrence.recConst ((factorCount (program ds) : ℝ) / NW) m lam 400 (2 * lcC1 T ds) *
          ((factorCount (program ds) : ℝ) / NW) ^ j * u := by
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by norm_num [m])
  have hτ : 0 ≤ Parameters.tau := by norm_num [Parameters.tau]
  have hGd' : (1 : ℝ) ≤ Gd := by exact_mod_cast hGd
  have hu1 : 1 ≤ u := by omega
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hq : (n : ℝ) / ((r * w : ℕ) : ℝ) ≤ 1 := by
    have : (0 : ℝ) < ((r * w : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by omega) (by omega)
    rw [div_le_iff₀ this, one_mul]; exact_mod_cast hn
  refine Recurrence.recurrence_closed (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hm1 hτ
    hτl hal hGd' (by norm_num) (mul_nonneg (by norm_num) (lcC1_nonneg T ds)) hu' ?_ ?_ j
  · refine (lc_norm_zero_le A T ds hu1 hr hw hR₀ hρ).trans ?_
    generalize (n : ℝ) / ((r * w : ℕ) : ℝ) = q at hq ⊢
    nlinarith
  · intro i
    exact lc_norm_succ_le_two A T ds hu1 hr hw hR₀ hρ hGd hGK (hu.trans (le_bits u i))
      (hTw i) (hε i)

end IntegerMultBounds.MathlibTM2.Cost
