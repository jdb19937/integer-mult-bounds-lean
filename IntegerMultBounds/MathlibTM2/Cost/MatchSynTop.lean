module

public import IntegerMultBounds.MathlibTM2.Cost.LayerCost
public import IntegerMultBounds.MathlibTM2.Node.TopProc

/-!
# Cost matching: the host machine of the simultaneous layer

`topCost` (`Node/TopProc.lean`) with one row `R = 1` on `N = n + a` address bits, `r`
coefficients of `w'` symbols: the linear stages (widening, phase, unit, shift, padding, the
record reads) cost a constant times the volume `V = 2^N r w'`, the two top kernel blocks (one
leaf call with `q` bits at `aT`, one with `q₂` bits at `aT₂`) a constant times `(q + 1) V` and
`(q₂ + 1) V`, and every piece a constant times `V` beside its call of the layer procedure
(`mrT_topCost_le`). The hypotheses are the fit conditions of the stages: `w, s ≤ w'`,
`2^a ≤ R₂ ≤ 2 · 2^a`, `aT + K q ≤ N`, `aT₂ + K q₂ ≤ N`, `K D ≤ N`, `oS, K ≤ N ≤ r w'` and
`TopPc.Ok` for the pieces.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Networks

/-! ### Volume facts -/

/-- The volume facts of one row on `N` address bits: `1, N, w', 2^N ≤ V = 2^N r w'`. -/
theorem mrT_vol_facts {N r w' : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w') (hN : N ≤ r * w') :
    1 ≤ 2 ^ N * (r * w') ∧ N ≤ 2 ^ N * (r * w') ∧ w' ≤ 2 ^ N * (r * w') ∧
      2 ^ N ≤ 2 ^ N * (r * w') ∧ 1 ≤ r * w' := by
  have h2 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  have hrw : 1 ≤ r * w' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hw' : w' ≤ r * w' := Nat.le_mul_of_pos_left _ hr
  have hV : r * w' ≤ 2 ^ N * (r * w') := Nat.le_mul_of_pos_left _ h2
  have hV' : 2 ^ N ≤ 2 ^ N * (r * w') := Nat.le_mul_of_pos_right _ hrw
  exact ⟨by omega, by omega, by omega, hV', hrw⟩

/-- The configuration record is read in `≤ 224 V` steps. -/
theorem mrT_get_le {w w' s n a r K q aT oS D R₂ q₂ aT₂ : ℕ}
    (hr : 1 ≤ r) (hw1 : 1 ≤ w') (hw : w ≤ w') (hs : s ≤ w') (hK : 1 ≤ K)
    (hR₂ : R₂ ≤ 2 * 2 ^ a) (hq : aT + K * q ≤ n + a) (hq₂ : aT₂ + K * q₂ ≤ n + a)
    (hD : K * D ≤ n + a) (hoS : oS ≤ n + a) (hN : n + a ≤ r * w') :
    topGetCost (topCfg w s a 1 R₂ q aT K oS D q₂ aT₂) ≤ 224 * (2 ^ (n + a) * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  have h2a : 2 ^ a ≤ 2 ^ (n + a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqq : q ≤ K * q := Nat.le_mul_of_pos_left _ hK
  have hqq₂ : q₂ ≤ K * q₂ := Nat.le_mul_of_pos_left _ hK
  have hDD : D ≤ K * D := Nat.le_mul_of_pos_left _ hK
  simp only [topGetCost, topRecLen, topCfg, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

/-! ### The linear stages -/

theorem mrT_widen_le {cfg : List ℕ} {N r w w' : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w') (hw : w ≤ w')
    (hN : N ≤ r * w') :
    topWidenSCost cfg 1 N r w w' ≤ topGetCost cfg + 150 * (2 ^ N * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  simp only [topWidenSCost, topWidenCost, one_mul]
  have hsub : w' - w ≤ w' := Nat.sub_le _ _
  have hA : 2 ^ N * r * (4 * w + 4 + (4 * (w' - w) + 4 + 1) + 1) ≤
      14 * (2 ^ N * (r * w')) := by
    calc 2 ^ N * r * (4 * w + 4 + (4 * (w' - w) + 4 + 1) + 1) ≤ 2 ^ N * r * (14 * w') :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 14 * (2 ^ N * (r * w')) := by ring
  have hB : 2 ^ N * r * w' = 2 ^ N * (r * w') := by ring
  omega

theorem mrT_phase_le {cfg : List ℕ} {N r w' K ρ oS D : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w')
    (hρ : ρ < K) (hK : K ≤ N) (hD : K * D ≤ N) (hoS : oS ≤ N) (hN : N ≤ r * w') :
    topPhaseSCost cfg N 1 r w' K ρ oS D ≤ 3 * topGetCost cfg + 300 * (2 ^ N * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  have hDD : D ≤ K * D := Nat.le_mul_of_pos_left _ (by omega)
  simp only [topPhaseSCost, one_mul, mul_one]
  have hDK : D * (4 * K + 9) ≤ 13 * N := by
    have : D * (4 * K + 9) = 4 * (K * D) + 9 * D := by ring
    have hDD : D ≤ K * D := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hA : 2 ^ N * (25 * r * w' + 20 * N + 36) ≤ 81 * (2 ^ N * (r * w')) := by
    calc 2 ^ N * (25 * r * w' + 20 * N + 36) ≤ 2 ^ N * (81 * (r * w')) := by
          apply Nat.mul_le_mul_left
          have : 25 * r * w' = 25 * (r * w') := by ring
          omega
      _ = 81 * (2 ^ N * (r * w')) := by ring
  omega

theorem mrT_unit_le {cfg : List ℕ} {N r w' D : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w') (hD : D ≤ N)
    (hN : N ≤ r * w') :
    topUnitSCost cfg 1 N r w' D ≤ topGetCost cfg + 150 * (2 ^ N * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  simp only [topUnitSCost, topUnitCost, one_mul]
  have hA : 2 ^ N * r * (5 * w' + 6) ≤ 11 * (2 ^ N * (r * w')) := by
    calc 2 ^ N * r * (5 * w' + 6) ≤ 2 ^ N * r * (11 * w') :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 11 * (2 ^ N * (r * w')) := by ring
  have hB : 2 ^ N * r * w' = 2 ^ N * (r * w') := by ring
  omega

theorem mrT_shift_le {cfg : List ℕ} {N r w' s w : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w') (hw : w ≤ w')
    (hs : s ≤ w') (hN : N ≤ r * w') :
    topShiftSCost cfg 1 N r w' s w ≤ 2 * topGetCost cfg + 250 * (2 ^ N * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  simp only [topShiftSCost, topShiftCost, topShiftWordCost, one_mul]
  have hsub : w' - s - w ≤ w' := (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  have hA : 2 ^ N * r * (4 * w' + 4 + (1 + (4 * w' + 4 + (4 * s + 4 + (4 * w + 4 +
      (4 * (w' - s - w) + 4 + 1))))) + 1) ≤ 43 * (2 ^ N * (r * w')) := by
    calc 2 ^ N * r * (4 * w' + 4 + (1 + (4 * w' + 4 + (4 * s + 4 + (4 * w + 4 +
        (4 * (w' - s - w) + 4 + 1))))) + 1) ≤ 2 ^ N * r * (43 * w') :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 43 * (2 ^ N * (r * w')) := by ring
  have hB : 2 ^ N * r * w = 2 ^ N * (r * w) := by ring
  have hC : 2 ^ N * (r * w) ≤ 2 ^ N * (r * w') :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hw)
  omega

/-! ### The top kernels -/

/-- The leaf on one row: `≤ 200 (u + 1) V`. -/
theorem mrT_leaf_le {u K ρ a₀ N r w : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w) (ha : a₀ ≤ N) (hρ : ρ ≤ N)
    (hK : K ≤ N) (hu : u ≤ N) (hN : N ≤ r * w) :
    leafCost u K ρ a₀ 1 N r w ≤ 400 * ((u + 1) * (2 ^ N * (r * w))) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  simp only [leafCost, one_mul, mul_one]
  have hA : u * (2 ^ N * (29 * r * w + 20 * N + 36) + 10 * N + 33) ≤
      128 * (u * (2 ^ N * (r * w))) := by
    have hin : 2 ^ N * (29 * r * w + 20 * N + 36) + 10 * N + 33 ≤ 128 * (2 ^ N * (r * w)) := by
      have h2 : 2 ^ N * (29 * r * w + 20 * N + 36) ≤ 85 * (2 ^ N * (r * w)) := by
        calc 2 ^ N * (29 * r * w + 20 * N + 36) ≤ 2 ^ N * (85 * (r * w)) := by
              apply Nat.mul_le_mul_left
              have : 29 * r * w = 29 * (r * w) := by ring
              omega
          _ = 85 * (2 ^ N * (r * w)) := by ring
      omega
    calc u * (2 ^ N * (29 * r * w + 20 * N + 36) + 10 * N + 33) ≤
        u * (128 * (2 ^ N * (r * w))) := Nat.mul_le_mul_left _ hin
      _ = 128 * (u * (2 ^ N * (r * w))) := by ring
  have hB : (u + 1) * (2 ^ N * (r * w)) = u * (2 ^ N * (r * w)) + 2 ^ N * (r * w) := by ring
  omega

theorem mrT_ker_le (A Gd : ℕ) (ds : ComplexFramedExecution.Directions) {cfg : List ℕ} {K ρ N r w' q aT : ℕ}
    (hr : 1 ≤ r) (hw1 : 1 ≤ w') (hK : 1 ≤ K) (hρ : ρ < K) (hKN : K ≤ N)
    (hq : aT + K * q ≤ N) (hN : N ≤ r * w') :
    topKerSCost A Gd ds cfg K ρ 1 N r w' q aT ≤
      4 * topGetCost cfg + 500 * ((q + 1) * (2 ^ N * (r * w'))) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  have hqq : q ≤ K * q := Nat.le_mul_of_pos_left _ hK
  have hleaf := mrT_leaf_le (u := q) (K := K) (ρ := ρ) (a₀ := aT) hr hw1 (by omega) (by omega)
    hKN (by omega) hN
  simp only [topKerSCost, layerCost]
  have hB : (q + 1) * (2 ^ N * (r * w')) = q * (2 ^ N * (r * w')) + 2 ^ N * (r * w') := by ring
  rw [hB] at hleaf ⊢
  omega

/-! ### The block of pieces -/

theorem mrT_down_le {cfg : List ℕ} {n a r w' : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w')
    (hN : n + a ≤ r * w') :
    topDownCost cfg n a r w' ≤ topGetCost cfg + 150 * (2 ^ (n + a) * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  simp only [topDownCost]
  have h2n : 2 ^ n * (r * w') ≤ 2 ^ (n + a) * (r * w') :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hB : 2 ^ (n + a) * r * w' = 2 ^ (n + a) * (r * w') := by ring
  have hrw : r * w' ≤ 2 ^ (n + a) * (r * w') := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  omega

theorem mrT_up_le {cfg : List ℕ} {n a r w' : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w')
    (hN : n + a ≤ r * w') :
    topUpCost cfg n a r w' ≤ topGetCost cfg + 150 * (2 ^ (n + a) * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  simp only [topUpCost]
  have h2n : 2 ^ n * (r * w') ≤ 2 ^ (n + a) * (r * w') :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hB : 2 ^ (n + a) * r * w' = 2 ^ (n + a) * (r * w') := by ring
  omega

theorem mrT_pad_le {cfg : List ℕ} {n a r w' R₂ : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w')
    (hR₂ : R₂ ≤ 2 * 2 ^ a) (hN : n + a ≤ r * w') :
    topPadCost cfg a 1 R₂ (2 ^ n * r * w') (1 * 2 ^ a * 2 ^ n * r * w') ≤
      3 * topGetCost cfg + 200 * (2 ^ (n + a) * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  simp only [topPadCost, one_mul, mul_one]
  have h2a : 2 ^ a ≤ 2 ^ (n + a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hprod : 2 ^ a * 2 ^ n * r * w' = 2 ^ (n + a) * (r * w') := by
    rw [pow_add]; ring
  have hsub : R₂ - 2 ^ a ≤ 2 * 2 ^ a := (Nat.sub_le _ _).trans hR₂
  have h2aV : 2 ^ a ≤ 2 ^ (n + a) * (r * w') := h2a.trans h2N
  have hR₂V : R₂ ≤ 2 * (2 ^ (n + a) * (r * w')) := by omega
  have hA : (R₂ - 2 ^ a) * (4 * (2 ^ n * r * w') + 7) ≤ 22 * (2 ^ (n + a) * (r * w')) := by
    calc (R₂ - 2 ^ a) * (4 * (2 ^ n * r * w') + 7) ≤
        (2 * 2 ^ a) * (4 * (2 ^ n * r * w') + 7) := Nat.mul_le_mul_right _ hsub
      _ = 8 * (2 ^ a * 2 ^ n * r * w') + 14 * 2 ^ a := by ring
      _ ≤ 22 * (2 ^ (n + a) * (r * w')) := by rw [hprod]; omega
  omega

theorem mrT_unpad_le {cfg : List ℕ} {n a r w' R₂ : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w')
    (hR₂ : R₂ ≤ 2 * 2 ^ a) (hN : n + a ≤ r * w') :
    topUnpadCost cfg a 1 (2 ^ n * r * w') (R₂ * 2 ^ n * r * w') ≤
      2 * topGetCost cfg + 200 * (2 ^ (n + a) * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  simp only [topUnpadCost, mul_one]
  have h2a : 2 ^ a ≤ 2 ^ (n + a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hprod : 2 ^ a * 2 ^ n * r * w' = 2 ^ (n + a) * (r * w') := by
    rw [pow_add]; ring
  have h2aV : 2 ^ a ≤ 2 ^ (n + a) * (r * w') := h2a.trans h2N
  have hR₂V : R₂ ≤ 2 * (2 ^ (n + a) * (r * w')) := by omega
  have hA : 2 ^ a * (4 * (2 ^ n * r * w') + 7) ≤ 11 * (2 ^ (n + a) * (r * w')) := by
    calc 2 ^ a * (4 * (2 ^ n * r * w') + 7) = 4 * (2 ^ a * 2 ^ n * r * w') + 7 * 2 ^ a := by
          ring
      _ ≤ 11 * (2 ^ (n + a) * (r * w')) := by rw [hprod]; omega
  have hB : R₂ * 2 ^ n * r * w' ≤ 2 * (2 ^ (n + a) * (r * w')) := by
    calc R₂ * 2 ^ n * r * w' ≤ (2 * 2 ^ a) * 2 ^ n * r * w' := by gcongr
      _ = 2 * (2 ^ a * 2 ^ n * r * w') := by ring
      _ = 2 * (2 ^ (n + a) * (r * w')) := by rw [hprod]
  omega

/-- The fields of a piece meeting `TopPc.Ok` are at most `n`. -/
theorem mrT_pc_fields {ds : ComplexFramedExecution.Directions} {K n w' R₂ Gd : ℕ} {pc : TopPc}
    (hK : 1 ≤ K) (h : pc.Ok ds K n w' R₂ Gd) :
    pc.j ≤ n ∧ pc.u ≤ n ∧ pc.a₀ ≤ n ∧ K * bits pc.u pc.j ≤ n ∧ rowsAt pc.R₀ pc.j = R₂ := by
  have h1 := lc_lev_le_bits h.hu pc.j
  have h2 : pc.u ≤ bits pc.u pc.j := by
    rw [lc_bits_eq]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by norm_num [m]) _)
  have h3 : bits pc.u pc.j ≤ K * bits pc.u pc.j := Nat.le_mul_of_pos_left _ hK
  have h4 := h.hfit
  exact ⟨by omega, by omega, by omega, by omega, h.hR.symm⟩

/-- One piece: the record reads and bookkeeping cost `≤ topGetCost cfg + 50 V` beside its call
of the layer procedure. -/
theorem mrT_pc_le (A Gd : ℕ) (ds : ComplexFramedExecution.Directions) {cfg : List ℕ}
    {K ρ n a r w' R₂ : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w') (hK : 1 ≤ K) (hR₂ : R₂ ≤ 2 * 2 ^ a)
    (hN : n + a ≤ r * w') {pc : TopPc} (h : pc.Ok ds K n w' R₂ Gd) :
    topPcCost A Gd ds cfg K ρ n r w' pc ≤
      topGetCost cfg + layerCost A (nT CReg) ds pc.u K ρ pc.R₀ n r w' Gd pc.j pc.a₀ +
        200 * (2 ^ (n + a) * (r * w')) := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  obtain ⟨hj, hu, ha₀, hb, hR⟩ := mrT_pc_fields hK h
  have h2a : 2 ^ a ≤ 2 ^ (n + a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [topPcCost]
  rw [hR]
  omega

/-- The loop over the pieces. -/
theorem mrT_pcs_le (A Gd : ℕ) (ds : ComplexFramedExecution.Directions) {cfg : List ℕ}
    {K ρ n a r w' R₂ : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w') (hK : 1 ≤ K) (hR₂ : R₂ ≤ 2 * 2 ^ a)
    (hN : n + a ≤ r * w') :
    ∀ pcs : List TopPc, (∀ pc ∈ pcs, pc.Ok ds K n w' R₂ Gd) →
      topPcsCost A Gd ds cfg K ρ n r w' pcs ≤
        (pcs.length + 1) * (topGetCost cfg + 201 * (2 ^ (n + a) * (r * w'))) +
          (pcs.map fun pc => layerCost A (nT CReg) ds pc.u K ρ pc.R₀ n r w' Gd pc.j pc.a₀).sum
  | [], _ => by
      obtain ⟨h1, -, -, -, -⟩ := mrT_vol_facts hr hw1 hN
      simp only [topPcsCost, List.length_nil, List.map_nil, List.sum_nil]
      nlinarith
  | pc :: pcs, hok => by
      have ih := mrT_pcs_le A Gd ds (cfg := cfg) (ρ := ρ) hr hw1 hK hR₂ hN pcs fun q hq => hok q (List.mem_cons_of_mem _ hq)
      have hpc := mrT_pc_le A Gd ds (cfg := cfg) (ρ := ρ) hr hw1 hK hR₂ hN (hok pc List.mem_cons_self)
      obtain ⟨h1, -, -, -, -⟩ := mrT_vol_facts hr hw1 hN
      simp only [topPcsCost, List.length_cons, List.map_cons, List.sum_cons]
      have e : (pcs.length + 1 + 1) * (topGetCost cfg + 201 * (2 ^ (n + a) * (r * w'))) =
          (pcs.length + 1) * (topGetCost cfg + 201 * (2 ^ (n + a) * (r * w'))) +
            (topGetCost cfg + 201 * (2 ^ (n + a) * (r * w'))) := by ring
      rw [e]
      omega

/-- The piece record has at most `|pcs| (4 n + 4)` symbols. -/
theorem mrT_pcRec_le {ds : ComplexFramedExecution.Directions} {K n w' R₂ Gd : ℕ} (hK : 1 ≤ K) :
    ∀ pcs : List TopPc, (∀ pc ∈ pcs, pc.Ok ds K n w' R₂ Gd) →
      topRecLen (topPcRec K pcs) ≤ pcs.length * (4 * n + 4)
  | [], _ => by simp [topPcRec, topRecLen]
  | pc :: pcs, hok => by
      have ih := mrT_pcRec_le hK pcs fun q hq => hok q (List.mem_cons_of_mem _ hq)
      obtain ⟨hj, hu, ha₀, hb, -⟩ := mrT_pc_fields hK (hok pc List.mem_cons_self)
      simp only [topPcRec, List.flatMap_cons, topRecLen, List.map_append, List.sum_append,
        topPcFields, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons]
      simp only [topPcRec, topRecLen] at ih
      have e : (pcs.length + 1) * (4 * n + 4) = pcs.length * (4 * n + 4) + (4 * n + 4) := by ring
      omega

theorem mrT_block_le (A Gd : ℕ) (ds : ComplexFramedExecution.Directions) {cfg : List ℕ}
    {K ρ n a r w' R₂ : ℕ} (hr : 1 ≤ r) (hw1 : 1 ≤ w') (hK : 1 ≤ K) (hR₂ : R₂ ≤ 2 * 2 ^ a)
    (hN : n + a ≤ r * w') (pcs : List TopPc) (hok : ∀ pc ∈ pcs, pc.Ok ds K n w' R₂ Gd) :
    topBlockCost A Gd ds cfg K ρ n a r w' 1 R₂ pcs ≤
      (pcs.length + 8) * topGetCost cfg +
        (pcs.length + 1) * (1000 * (2 ^ (n + a) * (r * w'))) +
        (pcs.map fun pc => layerCost A (nT CReg) ds pc.u K ρ pc.R₀ n r w' Gd pc.j pc.a₀).sum := by
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  have hd := mrT_down_le (cfg := cfg) hr hw1 hN
  have hu := mrT_up_le (cfg := cfg) hr hw1 hN
  have hp := mrT_pad_le (cfg := cfg) hr hw1 hR₂ hN
  have hup := mrT_unpad_le (cfg := cfg) hr hw1 hR₂ hN
  have hpcs := mrT_pcs_le A Gd ds (cfg := cfg) (ρ := ρ) hr hw1 hK hR₂ hN pcs hok
  have hrec := mrT_pcRec_le hK pcs hok
  have hn : n ≤ 2 ^ (n + a) * (r * w') := by omega
  have hrec' : pcs.length * (4 * n + 4) ≤ pcs.length * (8 * (2 ^ (n + a) * (r * w'))) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [topBlockCost]
  generalize 2 ^ (n + a) * (r * w') = V at *
  generalize topGetCost cfg = G at *
  generalize pcs.length = L at *
  generalize (pcs.map fun pc => layerCost A (nT CReg) ds pc.u K ρ pc.R₀ n r w' Gd pc.j pc.a₀).sum = S
    at *
  nlinarith

/-! ### The whole machine -/

/-- `topCost` with one row `R = 1`: the linear stages and the top kernels cost
`C (q + q₂ + 1 + |pcs|) 2^(n+a) r w'`, plus the layer calls of the pieces. -/
theorem mrT_topCost_le (A : ℕ) (ds : ComplexFramedExecution.Directions) :
    ∃ C : ℕ, ∀ (w w' s n a r K ρ q aT oS D R₂ q₂ aT₂ Gd : ℕ) (pcs : List TopPc),
      1 ≤ r → 1 ≤ w' → w ≤ w' → s ≤ w' → 1 ≤ K → ρ < K → 2 ^ a ≤ R₂ → R₂ ≤ 2 * 2 ^ a →
      aT + K * q ≤ n + a → aT₂ + K * q₂ ≤ n + a → K * D ≤ n + a → oS ≤ n + a → K ≤ n + a →
      n + a ≤ r * w' →
      (∀ pc ∈ pcs, pc.Ok ds K n w' R₂ Gd) →
      topCost A Gd ds w w' s n a 1 r K ρ q aT oS D R₂ q₂ aT₂ pcs ≤
        C * ((q + q₂ + 1 + pcs.length) * (2 ^ (n + a) * (r * w'))) +
          (pcs.map fun pc => layerCost A (nT CReg) ds pc.u K ρ pc.R₀ n r w' Gd pc.j pc.a₀).sum := by
  refine ⟨30000, ?_⟩
  intro w w' s n a r K ρ q aT oS D R₂ q₂ aT₂ Gd pcs hr hw1 hw hs hK hρ hR₂l hR₂ hq hq₂ hD hoS hKN
    hN hok
  obtain ⟨h1, hNV, hwV, h2N, hrw⟩ := mrT_vol_facts hr hw1 hN
  have hDD : D ≤ K * D := Nat.le_mul_of_pos_left _ hK
  have hG := mrT_get_le hr hw1 hw hs hK hR₂ hq hq₂ hD hoS hN
  have hwid := mrT_widen_le (cfg := topCfg w s a 1 R₂ q aT K oS D q₂ aT₂) hr hw1 hw hN
  have hph := mrT_phase_le (cfg := topCfg w s a 1 R₂ q aT K oS D q₂ aT₂) hr hw1 hρ hKN hD hoS hN
  have hker := mrT_ker_le A Gd ds (cfg := topCfg w s a 1 R₂ q aT K oS D q₂ aT₂) hr hw1 hK hρ hKN
    hq hN
  have hker₂ := mrT_ker_le A Gd ds (cfg := topCfg w s a 1 R₂ q aT K oS D q₂ aT₂) hr hw1 hK hρ hKN
    hq₂ hN
  have hbl := mrT_block_le A Gd ds (cfg := topCfg w s a 1 R₂ q aT K oS D q₂ aT₂) (ρ := ρ) hr hw1 hK hR₂ hN
    pcs hok
  have hun := mrT_unit_le (cfg := topCfg w s a 1 R₂ q aT K oS D q₂ aT₂) (D := D) hr hw1 (by omega) hN
  have hsh := mrT_shift_le (cfg := topCfg w s a 1 R₂ q aT K oS D q₂ aT₂) hr hw1 hw hs hN
  simp only [topCost]
  generalize 2 ^ (n + a) * (r * w') = V at *
  generalize topGetCost (topCfg w s a 1 R₂ q aT K oS D q₂ aT₂) = G at *
  generalize pcs.length = L at *
  generalize (pcs.map fun pc => layerCost A (nT CReg) ds pc.u K ρ pc.R₀ n r w' Gd pc.j pc.a₀).sum = S
    at *
  nlinarith

end IntegerMultBounds.MathlibTM2.Cost
