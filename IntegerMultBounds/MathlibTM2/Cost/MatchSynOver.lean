module

public import IntegerMultBounds.MathlibTM2.Cost.MatchSynLay

/-!
# Cost matching: the per-round overheads of the synthetic transforms

The step bound `synLayerStepCost` of one layer step of the computed synthetic transforms
(`Fast/SynRound.lean`) is the layer itself (`synLayerCost`, bounded elsewhere) plus the record
builder (`synRecCost`), the rest state of the layer machine (`synRestUpCost`,
`synRestDownCost`), the parking of the wires (`stk`) and the configuration record; the twiddle
of the round costs `synTwCost`. With the size parameter `Z = N + D + ℓ + K + w + l + 1`
(`mrZ`) and the working width `w' = synW2`, every overhead is at most a constant times
`Z^8 · 2^N + 2^N · 2^l · w'` plus `2 stk + 2` (`mrO_step_le`); the constant depends on the
node (`gateCount`, `factorCount`) only.

* `mrO_expSeq_le`, `mrO_synE_le`: the piece exponents are polynomial, `expSeq G F u j ≤
  (G + u)(F + 1)^j` and `synE G F D D ≤ (G + m) D^6` when `F + 1 ≤ m^5` (a nonzero digit `j`
  has `m^j ≤ D`).
* `mrO_synW2_le`: `w' ≤ w + (G + m + 3)(D + 1)^6`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks

set_option maxHeartbeats 4000000

/-! ### Exponents and widths -/

theorem mrO_expSeq_le (G F u j : ℕ) : expSeq G F u j ≤ (G + u) * (F + 1) ^ j := by
  induction j with
  | zero => simp [expSeq]
  | succ j ih =>
      rw [expSeq, pow_succ]
      have h1 : 1 ≤ (F + 1) ^ j := Nat.one_le_pow _ _ (by omega)
      have h2 : F * expSeq G F u j ≤ F * ((G + u) * (F + 1) ^ j) := Nat.mul_le_mul_left _ ih
      nlinarith

/-- A nonzero digit `j` of `D` has `m^j ≤ D`. -/
theorem mrO_pow_le_of_dg {D j : ℕ} (h : synDg D j ≠ 0) : m ^ j ≤ D :=
  (div_pow_pos_iff m_pos).1 (synDg_pos_div h)

theorem mrO_synDg_lt (D j : ℕ) : synDg D j < m := Nat.mod_lt _ m_pos

/-- `(F + 1)^j ≤ D^5` when `m^j ≤ D` and `F + 1 ≤ m^5`. -/
theorem mrO_pow_F_le {F D j : ℕ} (hF : F + 1 ≤ m ^ 5) (hj : m ^ j ≤ D) :
    (F + 1) ^ j ≤ D ^ 5 :=
  calc (F + 1) ^ j ≤ (m ^ 5) ^ j := Nat.pow_le_pow_left hF j
    _ = (m ^ j) ^ 5 := by rw [← pow_mul m 5 j, ← pow_mul m j 5, Nat.mul_comm]
    _ ≤ D ^ 5 := Nat.pow_le_pow_left hj 5

/-- The exponent of a nonzero digit is at most `(G + m) D^5`. -/
theorem mrO_expSeq_dg_le {G F D j : ℕ} (hF : F + 1 ≤ m ^ 5) (h : synDg D j ≠ 0) {i : ℕ}
    (hi : i ≤ j) : expSeq G F (synDg D j) i ≤ (G + m) * D ^ 5 := by
  have h1 := mrO_expSeq_le G F (synDg D j) i
  have h2 : m ^ i ≤ D := (Nat.pow_le_pow_right m_pos hi).trans (mrO_pow_le_of_dg h)
  have h3 := mrO_pow_F_le hF h2
  have h4 := mrO_synDg_lt D j
  calc expSeq G F (synDg D j) i ≤ (G + synDg D j) * (F + 1) ^ i := h1
    _ ≤ (G + m) * D ^ 5 := Nat.mul_le_mul (by omega) h3

theorem mrO_synE_le (G F D : ℕ) (hF : F + 1 ≤ m ^ 5) : synE G F D D ≤ (G + m) * D ^ 6 := by
  unfold synE
  have h : ∀ j ∈ Finset.range D,
      (if synDg D j = 0 then 0 else expSeq G F (synDg D j) j) ≤ (G + m) * D ^ 5 := by
    intro j _
    split_ifs with h0
    · exact Nat.zero_le _
    · exact mrO_expSeq_dg_le hF h0 le_rfl
  refine (Finset.sum_le_card_nsmul _ _ _ h).trans ?_
  rw [Finset.card_range, smul_eq_mul]
  ring_nf
  exact le_rfl

theorem mrO_synLg_le (es : List ℕ) (ℓ : ℕ) : synLg es ℓ ≤ es.length := by
  unfold synLg layLongs
  exact (List.length_filter_le _ _).trans (by simp)

theorem mrO_synDp_le (es : List ℕ) (ℓ h : ℕ) : synDp es ℓ h ≤ es.length := by
  unfold synDp
  split_ifs
  · exact le_rfl
  · exact mrO_synLg_le es ℓ

theorem mrO_synQ_le (es : List ℕ) (ℓ K h : ℕ) : synQ es ℓ K h ≤ es.length := by
  unfold synQ
  split_ifs
  · exact synQK_le es
  · exact mrO_synDp_le es ℓ h

theorem mrO_synDpp_le (es : List ℕ) : synDpp es ≤ es.length := Nat.sub_le _ _

theorem mrO_synER_le (es : List ℕ) (ℓ K G F h : ℕ) (hF : F + 1 ≤ m ^ 5) :
    synER es ℓ K G F h ≤ (G + m) * es.length ^ 6 := by
  unfold synER
  split_ifs
  · exact (mrO_synE_le G F _ hF).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (mrO_synDpp_le es) 6))
  · exact Nat.zero_le _

theorem mrO_synS_le (es : List ℕ) (ℓ K G F h : ℕ) (hF : F + 1 ≤ m ^ 5) :
    synS es ℓ K G F h ≤ (G + m + 2) * (es.length + 1) ^ 6 := by
  unfold synS
  have h1 := mrO_synDp_le es ℓ h
  have h2 := mrO_synQ_le es ℓ K h
  have h3 := mrO_synER_le es ℓ K G F h hF
  have h4 : es.length ^ 6 ≤ (es.length + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have h5 : es.length + 1 ≤ (es.length + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have h6 : (G + m) * es.length ^ 6 ≤ (G + m) * (es.length + 1) ^ 6 := Nat.mul_le_mul_left _ h4
  have h7 : (synDp es ℓ h + 1) / 2 ≤ es.length + 1 := by omega
  generalize (es.length + 1) ^ 6 = P at *
  generalize (G + m) * P = Q at *
  nlinarith

theorem mrO_synW2_le (es : List ℕ) (ℓ K G F w h : ℕ) (hF : F + 1 ≤ m ^ 5) :
    synW2 es ℓ K G F w h ≤ w + (G + m + 3) * (es.length + 1) ^ 6 := by
  unfold synW2
  have h1 := mrO_synS_le es ℓ K G F h hF
  have h5 : es.length + 1 ≤ (es.length + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  generalize (es.length + 1) ^ 6 = P at *
  nlinarith

theorem mrO_le_synW2 (es : List ℕ) (ℓ K G F w h : ℕ) : w ≤ synW2 es ℓ K G F w h := by
  unfold synW2; omega

theorem mrO_synS_le_synW2 (es : List ℕ) (ℓ K G F w h : ℕ) :
    synS es ℓ K G F h ≤ synW2 es ℓ K G F w h := by
  unfold synW2; omega

theorem mrO_length_le_synW2 (es : List ℕ) (ℓ K G F w h : ℕ) :
    es.length ≤ synW2 es ℓ K G F w h := by
  unfold synW2; omega

/-! ### The size parameter -/

/-- The size parameter of a round. -/
def mrZ (es : List ℕ) (ℓ K w l : ℕ) : ℕ := es.sum + es.length + ℓ + K + w + l + 1

/-! ### Elementary cost bounds -/

theorem mrO_mulR_le {x y Z : ℕ} (hZ : 1 ≤ Z) (hx : x ≤ Z) (hy : y ≤ Z) :
    synMulRCost x y ≤ 17 * Z ^ 2 := by
  unfold synMulRCost
  have : x * y ≤ Z * Z := Nat.mul_le_mul hx hy
  nlinarith

theorem mrO_mulR_le3 {x y Z : ℕ} (hZ : 1 ≤ Z) (hx : x ≤ Z) (hy : y ≤ Z ^ 2) :
    synMulRCost x y ≤ 17 * Z ^ 3 := by
  unfold synMulRCost
  have : x * y ≤ Z * Z ^ 2 := Nat.mul_le_mul hx hy
  have : Z ≤ Z ^ 3 := Nat.le_self_pow (by norm_num) _
  nlinarith

theorem mrO_divMod_le {x K Z : ℕ} (hZ : 1 ≤ Z) (hx : x ≤ Z) (hK : K ≤ Z) :
    synDivModCost x K ≤ 33 * Z ^ 2 := by
  unfold synDivModCost
  have : x * K ≤ Z * Z := Nat.mul_le_mul hx hK
  nlinarith

theorem mrO_cntPass_le (k X t : ℕ) : synCntPassCost k X t ≤ 8 * X + 11 := by
  unfold synCntPassCost
  have h1 : X / k ^ t ≤ X := Nat.div_le_self _ _
  have h2 : X / k ^ t / k ≤ X / k ^ t := Nat.div_le_self _ _
  split_ifs <;> omega

theorem mrO_cnt_le (k X n : ℕ) : synCntCost k X n ≤ n * (8 * X + 14) + 2 * n + 4 := by
  unfold synCntCost
  have h : ∀ t ∈ Finset.range n, synCntPassCost k X t + 3 ≤ 8 * X + 14 := fun t _ => by
    have := mrO_cntPass_le k X t; omega
  have := Finset.sum_le_card_nsmul _ _ _ h
  rw [Finset.card_range, smul_eq_mul] at this
  omega

theorem mrO_preBr_le {w a dp oS D Z : ℕ} (hZ : 1 ≤ Z) (hw : w ≤ Z) (ha : a ≤ Z) (hdp : dp ≤ Z)
    (hoS : oS ≤ Z) (hD : D ≤ Z) :
    synPreBrCost w a dp oS D ≤ 10 * 2 ^ a + 200 * Z := by
  unfold synPreBrCost
  omega

/-! ### The twiddle -/

theorem mrO_getD_le_sum (es : List ℕ) (t : ℕ) : es.getD t 0 ≤ es.sum := by
  rcases Nat.lt_or_ge t es.length with ht | ht
  · rw [List.getD_eq_getElem _ _ ht]
    exact List.le_sum_of_mem (List.getElem_mem ht)
  · rw [List.getD_eq_default _ _ ht]
    exact Nat.zero_le _

theorem mrO_seg_le (e h : ℕ) : synSegCost e h ≤ 10 * e + 8 * h + 24 := by
  unfold synSegCost
  split_ifs <;> omega

theorem mrO_sum_map_succ (es : List ℕ) : (es.map (· + 1)).sum = es.sum + es.length := by
  induction es with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, List.sum_cons, List.length_cons, ih]; ring

theorem mrO_roles_le {A : ℕ} (es : List ℕ) {h Z : ℕ} (hZ : 1 ≤ Z) (hN : es.sum ≤ Z)
    (hD : es.length ≤ Z) (hh : h ≤ Z) : synRolesCost (A := A) es h ≤ 72 * Z ^ 2 := by
  unfold synRolesCost
  rw [length_topRec, mrO_sum_map_succ]
  have h : ∀ t ∈ Finset.range es.length,
      2 * es.getD t 0 + 3 + synSegCost (es.getD t 0) h + (2 * es.getD t 0 + 2) + 3 ≤ 58 * Z := by
    intro t _
    have h1 := mrO_getD_le_sum es t
    have h2 := mrO_seg_le (es.getD t 0) h
    omega
  have := Finset.sum_le_card_nsmul _ _ _ h
  rw [Finset.card_range, smul_eq_mul] at this
  have h3 : es.length * (58 * Z) ≤ Z * (58 * Z) := Nat.mul_le_mul_right _ hD
  nlinarith

theorem mrO_twPassL_le {N h l w Z : ℕ} (hZ : 1 ≤ Z) (hN : N ≤ Z) (hh : h ≤ Z) (hl : l ≤ Z) :
    twPassLCost N h l w (2 ^ N) ≤ 248 * (Z ^ 2 * 2 ^ N) + 35 * (2 ^ N * (2 ^ l * w)) + 4 := by
  unfold twPassLCost twGatherCost twExpCost twRecCost
  have h1 : N ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left hN 2
  have h2 : N * (12 * h + 33) ≤ 12 * Z ^ 2 + 33 * Z := by nlinarith
  have hin : 12 * N ^ 2 + 12 * N + 6 + (N * (12 * h + 33) + 24 * h + 4 * l + 70) + (2 * N + 2) +
      (33 * 2 ^ l * w + 20 * l + 40) + 4 * N + 5 + 2 ≤ 248 * Z ^ 2 + 33 * (2 ^ l * w) := by
    have : 33 * 2 ^ l * w = 33 * (2 ^ l * w) := by ring
    have : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
    nlinarith
  have h3 := Nat.mul_le_mul_left (2 ^ N) hin
  have e : 2 ^ N * (248 * Z ^ 2 + 33 * (2 ^ l * w)) =
      248 * (Z ^ 2 * 2 ^ N) + 33 * (2 ^ N * (2 ^ l * w)) := by ring
  rw [e] at h3
  omega

theorem mrO_twCost_le (es : List ℕ) {l w h Z : ℕ} (hZ : 1 ≤ Z) (hw1 : 1 ≤ w) (hN : es.sum ≤ Z)
    (hD : es.length ≤ Z) (hh : h ≤ Z) (hl : l ≤ Z) (hw : w ≤ Z) :
    synTwCost es l w h ≤ 500 * (Z ^ 8 * 2 ^ es.sum) + 60 * (2 ^ es.sum * (2 ^ l * w)) := by
  simp only [synTwCost]
  have h1 := mrO_roles_le (A := 0) es hZ hN hD hh
  have h2 := mrO_twPassL_le (w := w) hZ hN hh hl
  have h3 : synMulRCost (2 ^ l) w ≤ 13 * (2 ^ es.sum * (2 ^ l * w)) + 4 := by
    unfold synMulRCost
    have hP : 1 ≤ 2 ^ es.sum := Nat.one_le_two_pow
    have : 2 ^ l ≤ 2 ^ l * w := Nat.le_mul_of_pos_right _ hw1
    have : 2 ^ l * (4 * w + 7) + 2 * 2 ^ l ≤ 13 * (2 ^ l * w) := by nlinarith
    have : 2 ^ l * w ≤ 2 ^ es.sum * (2 ^ l * w) := Nat.le_mul_of_pos_left _ hP
    omega
  have h4 : 2 ^ l * w ≤ 2 ^ es.sum * (2 ^ l * w) := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  have h5 : Z ^ 2 * 2 ^ es.sum ≤ Z ^ 8 * 2 ^ es.sum :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hZ (by norm_num))
  have h6 : Z ^ 2 ≤ Z ^ 8 * 2 ^ es.sum := by
    have : Z ^ 2 ≤ Z ^ 8 := Nat.pow_le_pow_right hZ (by norm_num)
    have : Z ^ 8 ≤ Z ^ 8 * 2 ^ es.sum := Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
    omega
  have h7 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have hx : 1 ≤ Z ^ 8 * 2 ^ es.sum := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

/-! ### The rest state -/

theorem mrO_restUp_le {N r W Kh Rh prl Z : ℕ} (hZ : 1 ≤ Z) (hW1 : 1 ≤ W) (hN : N ≤ Z)
    (hK : Kh ≤ Z) (hR : Rh ≤ Z) :
    synRestUpCost N r W Kh Rh prl ≤ 60 * (2 ^ N * (r * W)) + 30 * W + 4 * prl + 100 * Z ^ 2 := by
  unfold synRestUpCost
  have h1 : synMulRCost r W ≤ 13 * (2 ^ N * (r * W)) + 4 := by
    unfold synMulRCost
    have : r ≤ r * W := Nat.le_mul_of_pos_right _ hW1
    have : r * W ≤ 2 ^ N * (r * W) := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
    nlinarith
  have h2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

theorem mrO_restDown_le {N r W Kh Rh prl Z : ℕ} (hZ : 1 ≤ Z) (hN : N ≤ Z)
    (hK : Kh ≤ Z) (hR : Rh ≤ Z) :
    synRestDownCost N r W Kh Rh prl ≤ 8 * (2 ^ N * (r * W)) + 10 * W + 2 * prl + 50 * Z ^ 2 := by
  unfold synRestDownCost
  have : r * W ≤ 2 ^ N * (r * W) := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  have h2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-! ### Round parameters against the address bits -/

theorem mrO_length_le_sum {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) : es.length ≤ es.sum := by
  apply List.length_le_sum_of_one_le
  intro e he
  have := H.widths e he
  have := H.ℓ_ge
  omega

theorem mrO_synOS_le {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) (h : ℕ) :
    synOS es ℓ K h ≤ es.sum := by
  by_cases hc : synChunk ℓ K h
  · have := synChunk_fit H hc
    omega
  · unfold synOS
    unfold synChunk at hc
    split_ifs with h1 h2
    · omega
    · exact absurd ⟨h1, by omega⟩ hc
    · omega

/-- The chunk offset in the explicit form of the record builder. -/
theorem mrO_synOS_chunk {es : List ℕ} {ℓ K h : ℕ} (hc : synChunk ℓ K h) :
    synOS es ℓ K h = K * ((h - layB ℓ K) / K * es.length) := by
  unfold synOS
  rw [if_pos hc.1, if_neg (not_lt.2 hc.2)]

theorem mrO_synAT_le {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) (h : ℕ) :
    synAT es ℓ K h ≤ es.sum := by
  unfold synAT
  split_ifs with hc
  · have h1 := synChunk_fit H hc
    have h2 : K * synDpp es ≤ K * es.length := Nat.mul_le_mul_left _ (mrO_synDpp_le es)
    omega
  · exact mrO_synOS_le H h

theorem mrO_synKhQ_le {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) (h : ℕ) :
    synKh ℓ K h * synQ es ℓ K h ≤ es.sum := by
  unfold synKh synQ
  split_ifs with hc
  · have h1 := synChunk_fit H hc
    have h2 : K * synQK es ≤ K * es.length := Nat.mul_le_mul_left _ (synQK_le es)
    omega
  · have := mrO_synDp_le es ℓ h
    have := mrO_length_le_sum H
    omega

theorem mrO_synKh_le {ℓ K : ℕ} (hK : 1 ≤ K) (h : ℕ) : synKh ℓ K h ≤ K := by
  unfold synKh; split_ifs <;> omega

theorem mrO_synRh_le {ℓ K : ℕ} (hK : 1 ≤ K) (h : ℕ) : synRh ℓ K h ≤ K := by
  unfold synRh; split_ifs
  · exact (Nat.mod_lt _ hK).le
  · exact Nat.zero_le _

theorem mrO_synAc_le {es : List ℕ} {ℓ K h : ℕ} (H : LayHyp es ℓ K) (hc : synChunk ℓ K h) :
    synAc es ℓ K ≤ es.sum := by
  have := synAR_le H h
  unfold synAR at this
  rwa [if_pos hc] at this

theorem mrO_synR2_le {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) (h : ℕ) :
    synR2 es ℓ K h ≤ 2 * 2 ^ es.sum := by
  unfold synR2
  split_ifs with hc
  · have h1 := synR2c_lt es ℓ K H.K_pos
    have h2 : 2 ^ synAc es ℓ K ≤ 2 ^ es.sum :=
      Nat.pow_le_pow_right (by norm_num) (mrO_synAc_le H hc)
    omega
  · have : 2 ^ synA es ℓ K ≤ 2 ^ es.sum := Nat.pow_le_pow_right (by norm_num) (synA_le H)
    omega

/-- The configuration record of a round. -/
theorem mrO_cfl_le {es : List ℕ} {ℓ K G F w h Z : ℕ} (H : LayHyp es ℓ K) (hF : F + 1 ≤ m ^ 5)
    (hZ : 1 ≤ Z) (hN : es.sum ≤ Z) (hD : es.length + 1 ≤ Z) (hw : w ≤ Z) :
    topRecLen (synCfg es ℓ K G F w h) ≤ (G + m + 2) * Z ^ 6 + 2 * 2 ^ es.sum + 18 * Z := by
  simp only [synCfg, topCfg, topRecLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h1 := mrO_synS_le es ℓ K G F h hF
  have h1' : (G + m + 2) * (es.length + 1) ^ 6 ≤ (G + m + 2) * Z ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
  have h2 := synAR_le H h
  have h3 := mrO_synR2_le H h
  have h4 := mrO_synQ_le es ℓ K h
  have h5 := mrO_synAT_le H h
  have h6 := mrO_synKhQ_le H h
  have h7 := mrO_synOS_le H h
  have h8 := mrO_synDp_le es ℓ h
  omega

/-! ### The piece record -/

theorem mrO_topRecLen_append (l₁ l₂ : List ℕ) :
    topRecLen (l₁ ++ l₂) = topRecLen l₁ + topRecLen l₂ := by
  simp [topRecLen]

theorem mrO_topRecLen_flatMap (K : ℕ) : ∀ pcs : List TopPc,
    topRecLen (topPcRec K pcs) = (pcs.map fun pc => topRecLen (topPcFields K pc)).sum
  | [] => by simp [topPcRec, topRecLen]
  | pc :: pcs => by
      rw [topPcRec, List.flatMap_cons, mrO_topRecLen_append, List.map_cons, List.sum_cons,
        ← mrO_topRecLen_flatMap K pcs]
      rfl

theorem mrO_length_synPcs (K a D oS J t : ℕ) : (synPcs K a D oS J t).length ≤ t := by
  unfold synPcs
  exact (List.length_filterMap_le _ _).trans (by simp)

theorem mrO_prl_le {es : List ℕ} {ℓ K h Z : ℕ} (H : LayHyp es ℓ K) (hZ : 1 ≤ Z)
    (hN : es.sum ≤ Z) (hD : es.length ≤ Z) :
    topRecLen (topPcRec (synKh ℓ K h) (synPcsR es ℓ K h)) ≤ (m + 8) * Z ^ 2 := by
  unfold synPcsR synKh
  split_ifs with hc
  · rw [mrO_topRecLen_flatMap]
    have hfit := synChunk_fit H hc
    have hDp : K * synDpp es ≤ K * es.length := Nat.mul_le_mul_left _ (mrO_synDpp_le es)
    have hb : ∀ x ∈ (synPcs K (synX es ℓ K) (synDpp es) (synOS es ℓ K h) (synJp es)
        (synDpp es)).map (fun pc => topRecLen (topPcFields K pc)), x ≤ (m + 8) * Z := by
      intro x hx
      obtain ⟨pc, hpc, rfl⟩ := List.mem_map.1 hx
      obtain ⟨j, hj, h0, rfl⟩ := mem_synPcs hpc
      simp only [synPc, topPcFields, topRecLen, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, bits_eq_mul]
      have h1 : synDpp es % m ^ j + synDg (synDpp es) j * m ^ j ≤ synDpp es := by
        rw [← mod_pow_succ_dg]; exact Nat.mod_le _ _
      have h2 : K * (synDpp es % m ^ j) + K * (synDg (synDpp es) j * m ^ j) ≤ K * synDpp es := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h1
      have h3 := mrO_synDg_lt (synDpp es) j
      have h4 := mrO_synDpp_le es
      have h5 : m ≤ m * Z := Nat.le_mul_of_pos_right _ hZ
      nlinarith
    have := List.sum_le_card_nsmul _ _ hb
    rw [List.length_map, smul_eq_mul] at this
    have hl := mrO_length_synPcs K (synX es ℓ K) (synDpp es) (synOS es ℓ K h) (synJp es)
      (synDpp es)
    have h6 : (synPcs K (synX es ℓ K) (synDpp es) (synOS es ℓ K h) (synJp es)
        (synDpp es)).length * ((m + 8) * Z) ≤ Z * ((m + 8) * Z) :=
      Nat.mul_le_mul_right _ (hl.trans ((mrO_synDpp_le es).trans hD))
    nlinarith
  · simp [topPcRec, topRecLen]

/-! ### The chunk branch of the record builder -/

theorem mrO_chunkA_le {hv bv Kv Dv Z : ℕ} (hZ : 1 ≤ Z) (hh : hv ≤ Z) (hb : bv ≤ Z) (hK : Kv ≤ Z)
    (hD : Dv ≤ Z) : synChunkACost hv bv Kv Dv ≤ 200 * Z ^ 3 := by
  unfold synChunkACost
  have hx : hv - bv ≤ Z := by omega
  have h1 := mrO_divMod_le hZ hx hK
  have h2 : (hv - bv) % Kv ≤ Z := (Nat.mod_le _ _).trans hx
  have h3 : (hv - bv) / Kv ≤ Z := (Nat.div_le_self _ _).trans hx
  have h4 := mrO_mulR_le hZ h3 hD
  have h5 : (hv - bv) / Kv * Dv ≤ Z ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul h3 hD
  have h6 := mrO_mulR_le3 hZ hK h5
  have h7 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have h8 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ (by norm_num)
  omega

theorem mrO_chunkQ_le {oS Kv Dv Z : ℕ} (hZ : 1 ≤ Z) (hoS : oS ≤ Z) (hK : Kv ≤ Z) (hD : Dv ≤ Z) :
    synChunkQCost oS Kv Dv ≤ 500 * Z ^ 2 := by
  simp only [synChunkQCost, synCW]
  have h1 := synJ_le Dv Dv
  have h2 := mrO_cnt_le m Dv Dv
  have h3 : Dv * (8 * Dv + 14) ≤ 8 * Z ^ 2 + 14 * Z := by nlinarith
  have hq : Dv - (Dv - 46 * (synJ Dv Dv - 1)) ≤ Z := by omega
  have h4 := mrO_mulR_le hZ hK hq
  have h5 := mrO_mulR_le hZ hK (show Dv - (Dv - (Dv - 46 * (synJ Dv Dv - 1))) ≤ Z by omega)
  have h6 : Kv * (Dv - (Dv - 46 * (synJ Dv Dv - 1))) ≤ Z ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul hK hq
  have h7 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

theorem mrO_piece_le (G : ℕ) {F Kv d t A0 Z : ℕ} (hZ : 1 ≤ Z) (hK : Kv ≤ Z) (hd : d ≤ m)
    (hdm : d * m ^ t ≤ Z) (ht : t ≤ Z) (hA : A0 ≤ 2 * Z ^ 2)
    (hexp : ∀ i ≤ t, expSeq G F d i ≤ (G + m) * Z ^ 5) :
    synPieceCost G F Kv d t A0 ≤ 200 * ((G + m + 1) * Z ^ 6) := by
  unfold synPieceCost synMulRCost
  have h1 : d * (4 * m ^ t + 7) ≤ 4 * Z + 7 * m := by nlinarith
  have h2 : Kv * (d * m ^ t) ≤ Z ^ 2 := by rw [sq]; exact Nat.mul_le_mul hK hdm
  have h3 : Kv * (4 * (d * m ^ t) + 7) ≤ 4 * Z ^ 2 + 7 * Z := by nlinarith
  have h4 : ∀ i ∈ Finset.range t, 8 * expSeq G F d i + 12 ≤ 8 * ((G + m) * Z ^ 5) + 12 :=
    fun i hi => by have := hexp i (Finset.mem_range.1 hi).le; omega
  have h5 := Finset.sum_le_card_nsmul _ _ _ h4
  rw [Finset.card_range, smul_eq_mul] at h5
  have h6 : t * (8 * ((G + m) * Z ^ 5) + 12) ≤ 8 * ((G + m) * Z ^ 6) + 12 * Z := by
    have : t * ((G + m) * Z ^ 5) ≤ (G + m) * Z ^ 6 := by
      calc t * ((G + m) * Z ^ 5) ≤ Z * ((G + m) * Z ^ 5) := Nat.mul_le_mul_right _ ht
        _ = (G + m) * Z ^ 6 := by ring
    nlinarith
  have h7 := hexp t le_rfl
  have h8 : (G + m) * Z ^ 5 ≤ (G + m) * Z ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ (by norm_num))
  have h9 : Z ^ 2 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by norm_num)
  have h10 : Z ≤ Z ^ 6 := Nat.le_self_pow (by norm_num) _
  have h11 : m * Z ^ 6 ≤ (G + m + 1) * Z ^ 6 := Nat.mul_le_mul_right _ (by omega)
  have h12 : (G + m) * Z ^ 6 ≤ (G + m + 1) * Z ^ 6 := Nat.mul_le_mul_right _ (by omega)
  have h13 : Z ^ 6 ≤ (G + m + 1) * Z ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  have h14 : m ≤ m * Z ^ 6 := Nat.le_mul_of_pos_right _ (by positivity)
  omega

theorem mrO_pow_synJ_le (D : ℕ) : m ^ synJ D D ≤ m * D + 1 := by
  by_cases hD : D = 0
  · subst hD; simp [synJ, synJk]
  · rw [synJ_self_eq hD, pow_succ]
    have := Nat.pow_log_le_self m hD
    nlinarith

theorem mrO_digPass_le (G : ℕ) {F Kv oS D t Z : ℕ} (hF : F + 1 ≤ m ^ 5) (hZ : 1 ≤ Z)
    (hK : Kv ≤ Z) (hoS : oS ≤ Z) (hD : D ≤ Z) (ht : t ≤ Z) :
    synDigPassCost G F Kv oS D t ≤ 200 * ((G + m + 1) * Z ^ 6) + 100 * Z := by
  unfold synDigPassCost
  split_ifs with h0
  · omega
  · have hpos : 0 < D / m ^ t := Nat.pos_of_ne_zero h0
    have hmt : m ^ t ≤ D := (div_pow_pos_iff m_pos).1 hpos
    unfold synDigBodyCost
    rw [synDg_eq]
    have hx : D / m ^ t ≤ D := Nat.div_le_self _ _
    have hxm : m * (D / m ^ t / m) ≤ D / m ^ t := Nat.mul_div_le _ _
    have hxm' : D / m ^ t / m ≤ D / m ^ t := Nat.div_le_self _ _
    have hdg := mrO_synDg_lt D t
    have hdx : synDg D t ≤ D / m ^ t := Nat.mod_le _ _
    have hdgm : synDg D t * m ^ t ≤ D := by
      have : D % m ^ t + synDg D t * m ^ t ≤ D := by
        rw [← mod_pow_succ_dg]; exact Nat.mod_le _ _
      exact (Nat.le_add_left _ _).trans this
    have hA : oS + Kv * (D % m ^ t) ≤ 2 * Z ^ 2 := by
      have : Kv * (D % m ^ t) ≤ Z * Z := Nat.mul_le_mul hK ((Nat.mod_le _ _).trans hD)
      have : Z ≤ Z * Z := Nat.le_mul_of_pos_right _ hZ
      nlinarith
    have h6 : Z ≤ Z ^ 6 := Nat.le_self_pow (by norm_num) _
    have h7 : Z ^ 6 ≤ (G + m + 1) * Z ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
    split_ifs with hd0
    · omega
    · have hp := mrO_piece_le G hZ hK hdg.le (hdgm.trans hD) ht hA fun i hi =>
        (mrO_expSeq_dg_le (G := G) hF hd0 hi).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 5))
      omega

theorem mrO_digits_le (G : ℕ) {F Kv oS D Z : ℕ} (hF : F + 1 ≤ m ^ 5) (hZ : 1 ≤ Z) (hK : Kv ≤ Z)
    (hoS : oS ≤ Z) (hD : D ≤ Z) :
    synDigitsCost G F Kv oS D ≤ 400 * ((G + m + 1) * Z ^ 7) := by
  unfold synDigitsCost
  have h1 : ∀ t ∈ Finset.range D, synDigPassCost G F Kv oS D t + 3 ≤
      200 * ((G + m + 1) * Z ^ 6) + 103 * Z := fun t ht => by
    have := mrO_digPass_le G hF hZ hK hoS hD ((Finset.mem_range.1 ht).le.trans hD)
    omega
  have h2 := Finset.sum_le_card_nsmul _ _ _ h1
  rw [Finset.card_range, smul_eq_mul] at h2
  have h3 : D * (200 * ((G + m + 1) * Z ^ 6) + 103 * Z) ≤
      200 * ((G + m + 1) * Z ^ 7) + 103 * Z ^ 2 := by
    have e1 : D * (200 * ((G + m + 1) * Z ^ 6)) ≤ 200 * ((G + m + 1) * Z ^ 7) := by
      calc D * (200 * ((G + m + 1) * Z ^ 6)) ≤ Z * (200 * ((G + m + 1) * Z ^ 6)) :=
            Nat.mul_le_mul_right _ hD
        _ = 200 * ((G + m + 1) * Z ^ 7) := by ring
    have e2 : D * (103 * Z) ≤ 103 * Z ^ 2 := by
      calc D * (103 * Z) ≤ Z * (103 * Z) := Nat.mul_le_mul_right _ hD
        _ = 103 * Z ^ 2 := by ring
    nlinarith
  have h4 := mrO_pow_synJ_le D
  have h5 : Kv * D ≤ Z ^ 2 := by rw [sq]; exact Nat.mul_le_mul hK hD
  have h6 : m * D ≤ m * Z := Nat.mul_le_mul_left _ hD
  have h7 : Z ^ 2 ≤ Z ^ 7 := Nat.pow_le_pow_right hZ (by norm_num)
  have h8 : Z ≤ Z ^ 7 := Nat.le_self_pow (by norm_num) _
  have h9 : m * Z ≤ (G + m + 1) * Z ^ 7 :=
    Nat.mul_le_mul (by omega) h8
  have h10 : Z ^ 7 ≤ (G + m + 1) * Z ^ 7 := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem mrO_chunkR2_le {a' Jn P Z : ℕ} (hZ : 1 ≤ Z) (hP : 1 ≤ P) (ha : a' ≤ Z) (hJ : Jn ≤ Z)
    (hB : NW ^ (Jn - 1) ≤ P)
    (hR : 2 ^ (a' - (synJk 2 (NW ^ (Jn - 1)) (a' + 1) - 1)) * NW ^ (Jn - 1) ≤ 2 * P) :
    synChunkR2Cost a' Jn ≤ 40 * (Z * P) + 200 * Z := by
  simp only [synChunkR2Cost]
  have h1 : ∀ j ∈ Finset.range (Jn - 1), 8 * (NW ^ j * 1) + 8 + 3 ≤ 8 * P + 11 := fun j hj => by
    have : NW ^ j ≤ NW ^ (Jn - 1) :=
      Nat.pow_le_pow_right NW_pos (Finset.mem_range.1 hj).le
    omega
  have h2 := Finset.sum_le_card_nsmul _ _ _ h1
  rw [Finset.card_range, smul_eq_mul] at h2
  have h3 : (Jn - 1) * (8 * P + 11) ≤ 8 * (Z * P) + 11 * Z := by
    have : Jn - 1 ≤ Z := by omega
    nlinarith
  have h4 := mrO_cnt_le 2 (NW ^ (Jn - 1)) (a' + 1)
  have h5 : (a' + 1) * (8 * NW ^ (Jn - 1) + 14) ≤ 16 * (Z * P) + 28 * Z := by
    have : a' + 1 ≤ 2 * Z := by omega
    nlinarith
  have h6 : synJk 2 (NW ^ (Jn - 1)) (a' + 1) - 1 ≤ a' := by
    have := synJk_le 2 (NW ^ (Jn - 1)) (a' + 1); omega
  have h7 : a' - (synJk 2 (NW ^ (Jn - 1)) (a' + 1) - 1) ≤ a' := Nat.sub_le _ _
  have h8 : NW ^ (Jn - 1) / 2 ^ (a' + 1) ≤ P := (Nat.div_le_self _ _).trans hB
  have h9 : P ≤ Z * P := Nat.le_mul_of_pos_left _ hZ
  omega

theorem mrO_chunkCfg_le {W a' Dv q E R2 aT Kq oS Z : ℕ} (hZ : 1 ≤ Z) (hW : W ≤ Z) (ha : a' ≤ Z)
    (hD : Dv ≤ Z) (hq : q ≤ Z) (haT : aT ≤ Z) (hKq : Kq ≤ Z) (hoS : oS ≤ Z) :
    synChunkCfgCost W a' Dv q E R2 aT Kq oS ≤ 4 * E + 4 * R2 + 200 * Z := by
  unfold synChunkCfgCost
  omega

theorem mrO_chunkEnd_le {W S Dv S5 oS R2 Jn q Dp Kq aT a' Z : ℕ} (hZ : 1 ≤ Z) (hW : W ≤ Z)
    (hD : Dv ≤ Z) (hS5 : S5 ≤ 2 * Z) (hoS : oS ≤ Z) (hJ : Jn ≤ Z) (hq : q ≤ Z) (hDp : Dp ≤ Z)
    (hKq : Kq ≤ Z) (haT : aT ≤ Z) (ha : a' ≤ Z) :
    synChunkEndCost W S Dv S5 oS R2 Jn q Dp Kq aT a' ≤ 6 * S + 2 * R2 + 100 * Z := by
  unfold synChunkEndCost
  omega

/-- **The chunk branch of the record builder.** -/
theorem mrO_chunk_le (G F : ℕ) {es : List ℕ} {ℓ K w h Z : ℕ} (H : LayHyp es ℓ K)
    (hc : synChunk ℓ K h) (hF : F + 1 ≤ m ^ 5) (hZ : 1 ≤ Z) (hN : es.sum ≤ Z)
    (hD : es.length ≤ Z) (hK : K ≤ Z) (hw : w ≤ Z) (hh : h ≤ Z) :
    synChunkCost G F (synA es ℓ K) h (layB ℓ K) K es.length w ≤
      2000 * ((G + m + 1) * Z ^ 7) + 60 * (Z * 2 ^ es.sum) := by
  have hK1 := H.K_pos
  have hb : layB ℓ K ≤ Z := (H.b_lt.le).trans hK
  have hfit := synChunk_fit H hc
  rw [mrO_synOS_chunk hc] at hfit
  have hAc := mrO_synAc_le H hc
  unfold synAc synQK synJt at hAc
  have hB := NW_pow_synJp_le es ℓ K hK1
  have hR := (synR2c_lt es ℓ K hK1).le
  unfold synJp synAc synDpp synQK synJt at hB
  unfold synR2c synX synLb synJp synAc synDpp synQK synJt at hR
  have hq0 : synQKn es.length (synJ es.length es.length - 1) ≤ es.length := synQK_le es
  have hP : 1 ≤ 2 ^ es.sum := Nat.one_le_two_pow
  simp only [synChunkCost]
  set q := synQKn es.length (synJ es.length es.length - 1) with hq'
  set Dp := es.length - q with hDp'
  set oS := K * ((h - layB ℓ K) / K * es.length) with hoS'
  set E := synE G F Dp Dp with hE'
  set Jn := synJ Dp Dp with hJn'
  set a' := K * q + synA es ℓ K with ha'
  set R2 := 2 ^ (a' - (synJk 2 (NW ^ (Jn - 1)) (a' + 1) - 1)) * NW ^ (Jn - 1) with hR2'
  have hoS : oS ≤ es.sum := by omega
  have hKD : K * es.length ≤ es.sum := by omega
  have hKq : K * q ≤ K * es.length := Nat.mul_le_mul_left _ hq0
  have hDp : Dp ≤ es.length := by rw [hDp']; exact Nat.sub_le _ _
  have hKDp : K * Dp ≤ K * es.length := Nat.mul_le_mul_left _ hDp
  have haT : oS + K * Dp ≤ es.sum := by omega
  have hE : E ≤ (G + m) * Z ^ 6 := by
    rw [hE']
    exact (mrO_synE_le G F Dp hF).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hDp.trans hD) 6))
  have hJ : Jn ≤ Z := by rw [hJn']; exact (synJ_le _ _).trans (hDp.trans hD)
  have hB' : NW ^ (Jn - 1) ≤ 2 ^ es.sum :=
    hB.trans (Nat.pow_le_pow_right (by norm_num) hAc)
  have hR' : R2 ≤ 2 * 2 ^ es.sum :=
    hR.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hAc))
  have hS5 : (es.length + 1) / 2 + q ≤ 2 * Z := by omega
  have hA := mrO_chunkA_le hZ hh hb hK hD
  have hQ := mrO_chunkQ_le hZ (hoS.trans hN) hK hD
  have hDg := mrO_digits_le G hF hZ hK (hoS.trans hN) (hDp.trans hD)
  have hR2 := mrO_chunkR2_le (P := 2 ^ es.sum) hZ hP (hAc.trans hN) hJ hB' (by rw [← hR2']; exact hR')
  have hCf := mrO_chunkCfg_le (E := E) (R2 := R2) hZ hw (hAc.trans hN) hD (hq0.trans hD)
    (haT.trans hN) (hKq.trans (hKD.trans hN)) (hoS.trans hN)
  have hEn := mrO_chunkEnd_le (S := (es.length + 1) / 2 + q + E) (R2 := R2) hZ hw hD hS5
    (hoS.trans hN) hJ (hq0.trans hD) (hDp.trans hD) (hKq.trans (hKD.trans hN)) (haT.trans hN)
    (hAc.trans hN)
  have h1 : Z ^ 3 ≤ Z ^ 7 := Nat.pow_le_pow_right hZ (by norm_num)
  have h2 : Z ^ 2 ≤ Z ^ 7 := Nat.pow_le_pow_right hZ (by norm_num)
  have h3 : Z ≤ Z ^ 7 := Nat.le_self_pow (by norm_num) _
  have h4 : Z ^ 6 ≤ Z ^ 7 := Nat.pow_le_pow_right hZ (by norm_num)
  have h5 : (G + m) * Z ^ 6 ≤ (G + m + 1) * Z ^ 7 := Nat.mul_le_mul (by omega) h4
  have h6 : Z ^ 7 ≤ (G + m + 1) * Z ^ 7 := Nat.le_mul_of_pos_left _ (by omega)
  have h7 : 2 ^ es.sum ≤ Z * 2 ^ es.sum := Nat.le_mul_of_pos_left _ hZ
  omega

/-! ### The record builder -/

theorem mrO_synRecCost_le (G F : ℕ) {es : List ℕ} {ℓ K w h Z : ℕ} (H : LayHyp es ℓ K)
    (hh : h < ℓ) (hF : F + 1 ≤ m ^ 5) (hZ : 1 ≤ Z) (hN : es.sum ≤ Z) (hD : es.length ≤ Z)
    (hℓ : ℓ ≤ Z) (hK : K ≤ Z) (hw : w ≤ Z) :
    synRecCost G F es ℓ K w h ≤ 2100 * ((G + m + 1) * Z ^ 7) + 100 * (Z * 2 ^ es.sum) := by
  have hK1 := H.K_pos
  have hb : layB ℓ K ≤ Z := (H.b_lt.le).trans hK
  have h0 := mrO_mulR_le hZ hb hD
  have hLg := (mrO_synLg_le es ℓ).trans hD
  have ha := synA_le H
  have hP : 1 ≤ 2 ^ es.sum := Nat.one_le_two_pow
  have h2a : 2 ^ synA es ℓ K ≤ 2 ^ es.sum := Nat.pow_le_pow_right (by norm_num) ha
  have hPZ : 2 ^ es.sum ≤ Z * 2 ^ es.sum := Nat.le_mul_of_pos_left _ hZ
  have h1 : Z ≤ Z ^ 7 := Nat.le_self_pow (by norm_num) _
  have h2 : Z ^ 2 ≤ Z ^ 7 := Nat.pow_le_pow_right hZ (by norm_num)
  have h6 : Z ^ 7 ≤ (G + m + 1) * Z ^ 7 := Nat.le_mul_of_pos_left _ (by omega)
  simp only [synRecCost]
  split_ifs with h1' h2'
  · -- low rounds
    have h3 := mrO_mulR_le hZ (show layB ℓ K - h ≤ Z by omega) hD
    have h4 : (layB ℓ K - h) * es.length ≤ Z ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (by omega) hD
    have h5 := mrO_preBr_le (oS := es.sum - synLg es ℓ - (layB ℓ K - h) * es.length) hZ hw
      (ha.trans hN) hD (by omega) hD
    omega
  · -- chunk rounds
    have h3 := mrO_chunk_le G F H ⟨h1', by omega⟩ hF hZ hN hD hK hw (by omega)
    generalize synChunkCost G F (synA es ℓ K) h (layB ℓ K) K es.length w = X at h3 ⊢
    omega
  · -- the top round
    have h5 := mrO_preBr_le (oS := es.sum - synLg es ℓ) hZ hw (ha.trans hN) hLg (by omega) hD
    omega

/-! ### The layer step -/

/-- **The overheads of one round**: the layer step plus the twiddle, less the layer itself, is
at most a constant times `Z^8 2^N + 2^N 2^l w'` plus `2 stk + 2`. -/
theorem mrO_step_le (ds : ComplexFramedExecution.Directions)
    (hF : factorCount (program ds) + 1 ≤ m ^ 5) :
    ∃ C : ℕ, ∀ (es : List ℕ) (ℓ K w l h stk : ℕ), LayHyp es ℓ K → h < ℓ → 1 ≤ w →
      synLayerStepCost ds es ℓ K w l h stk + synTwCost es l w h ≤
        synLayerCost ds es ℓ K l w h +
          C * (mrZ es ℓ K w l ^ 8 * 2 ^ es.sum +
            2 ^ es.sum * (2 ^ l * synW2 es ℓ K (gateCount (program ds))
              (factorCount (program ds)) w h)) +
          2 * stk + 2 := by
  refine ⟨4000 * (gateCount (program ds) + m + 1), ?_⟩
  intro es ℓ K w l h stk H hh hw1
  simp only [synLayerStepCost]
  generalize hG : gateCount (program ds) = G at *
  generalize hFe : factorCount (program ds) = F at *
  have hK1 := H.K_pos
  have hZ : 1 ≤ mrZ es ℓ K w l := by unfold mrZ; omega
  have hN : es.sum ≤ mrZ es ℓ K w l := by unfold mrZ; omega
  have hD : es.length ≤ mrZ es ℓ K w l := by unfold mrZ; omega
  have hD1 : es.length + 1 ≤ mrZ es ℓ K w l := by unfold mrZ; omega
  have hℓ : ℓ ≤ mrZ es ℓ K w l := by unfold mrZ; omega
  have hK : K ≤ mrZ es ℓ K w l := by unfold mrZ; omega
  have hw : w ≤ mrZ es ℓ K w l := by unfold mrZ; omega
  have hl : l ≤ mrZ es ℓ K w l := by unfold mrZ; omega
  have hhZ : h ≤ mrZ es ℓ K w l := by omega
  have hrec := mrO_synRecCost_le G F H hh hF hZ hN hD hℓ hK hw
  have hprl := mrO_prl_le (h := h) H hZ hN hD
  have hKh : synKh ℓ K h ≤ mrZ es ℓ K w l := (mrO_synKh_le (ℓ := ℓ) hK1 h).trans hK
  have hRh : synRh ℓ K h ≤ mrZ es ℓ K w l := (mrO_synRh_le (ℓ := ℓ) hK1 h).trans hK
  have hup := mrO_restUp_le (r := 2 ^ l) (W := synW2 es ℓ K G F w h)
    (prl := topRecLen (topPcRec (synKh ℓ K h) (synPcsR es ℓ K h))) hZ
    (hw1.trans (mrO_le_synW2 es ℓ K G F w h)) hN hKh hRh
  have hdown := mrO_restDown_le (r := 2 ^ l) (W := synW2 es ℓ K G F w h)
    (prl := topRecLen (topPcRec (synKh ℓ K h) (synPcsR es ℓ K h))) hZ hN hKh hRh
  have hcfl := mrO_cfl_le (G := G) (F := F) (h := h) H hF hZ hN hD1 hw
  have htw := mrO_twCost_le es hZ hw1 hN hD hhZ hl hw
  have hWZ : synW2 es ℓ K G F w h ≤ (G + m + 4) * mrZ es ℓ K w l ^ 6 := by
    have h1 := mrO_synW2_le es ℓ K G F w h hF
    have h2 : (G + m + 3) * (es.length + 1) ^ 6 ≤ (G + m + 3) * mrZ es ℓ K w l ^ 6 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD1 6)
    have h3 : mrZ es ℓ K w l ≤ mrZ es ℓ K w l ^ 6 := Nat.le_self_pow (by norm_num) _
    nlinarith
  have hV0 : 2 ^ es.sum * (2 ^ l * w) ≤ 2 ^ es.sum * (2 ^ l * synW2 es ℓ K G F w h) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (mrO_le_synW2 es ℓ K G F w h))
  -- everything against `Y = Z^8 2^N`
  set Z := mrZ es ℓ K w l with hZdef
  set Y := Z ^ 8 * 2 ^ es.sum with hY
  set V := 2 ^ es.sum * (2 ^ l * synW2 es ℓ K G F w h) with hV
  have hP1 : 1 ≤ 2 ^ es.sum := Nat.one_le_two_pow
  have c0 : 1 ≤ Y := by
    rw [hY]
    have := Nat.mul_le_mul (Nat.one_le_pow 8 Z hZ) hP1
    simpa using this
  have c1 : Z ^ 7 ≤ Y := by
    rw [hY]
    calc Z ^ 7 ≤ Z ^ 8 := Nat.pow_le_pow_right hZ (by norm_num)
      _ ≤ Z ^ 8 * 2 ^ es.sum := Nat.le_mul_of_pos_right _ hP1
  have c1' : (G + m + 1) * Z ^ 7 ≤ (G + m + 1) * Y := Nat.mul_le_mul_left _ c1
  have c2 : Z * 2 ^ es.sum ≤ Y := by
    rw [hY]; exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
  have c6 : Z ^ 6 ≤ Y := (Nat.pow_le_pow_right hZ (by norm_num)).trans c1
  have c3 : synW2 es ℓ K G F w h ≤ (G + m + 4) * Y :=
    hWZ.trans (Nat.mul_le_mul_left _ c6)
  have c4 : Z ^ 2 ≤ Y := (Nat.pow_le_pow_right hZ (by norm_num)).trans c1
  have c5 : (m + 8) * Z ^ 2 ≤ (m + 8) * Y := Nat.mul_le_mul_left _ c4
  have c6' : (G + m + 2) * Z ^ 6 ≤ (G + m + 2) * Y := Nat.mul_le_mul_left _ c6
  have c7 : 2 ^ es.sum ≤ Y := by
    rw [hY]; exact Nat.le_mul_of_pos_left _ (pow_pos hZ 8)
  have c8 : Z ≤ Y := (Nat.le_self_pow (by norm_num) _).trans c4
  generalize synRecCost G F es ℓ K w h = R at hrec ⊢
  generalize synLayerCost ds es ℓ K l w h = L at ⊢
  generalize synTwCost es l w h = Tw at htw ⊢
  generalize synW2 es ℓ K G F w h = W at hup hdown c3 hV hV0 ⊢
  generalize topRecLen (topPcRec (synKh ℓ K h) (synPcsR es ℓ K h)) = prl at hup hdown hprl ⊢
  generalize topRecLen (synCfg es ℓ K G F w h) = cfl at hcfl ⊢
  generalize synRestUpCost es.sum (2 ^ l) W (synKh ℓ K h) (synRh ℓ K h) prl = U at hup ⊢
  generalize synRestDownCost es.sum (2 ^ l) W (synKh ℓ K h) (synRh ℓ K h) prl = Dn at hdown ⊢
  generalize 2 ^ es.sum * (2 ^ l * w) = V0 at htw hV0 ⊢
  have n1 : 0 ≤ G * Y := Nat.zero_le _
  have n2 : 0 ≤ m * Y := Nat.zero_le _
  have n3 : 0 ≤ G * V := Nat.zero_le _
  have n4 : 0 ≤ m * V := Nat.zero_le _
  nlinarith

end IntegerMultBounds.MathlibTM2.Cost
